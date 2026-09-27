import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { initBoardState } from "../src/engine/board.ts";
import { boardPath, importLegacyBoard, legacyBoardPath } from "../src/extension/persistence.ts";
import { SqliteBoardBackend } from "../src/extension/sqlite.ts";
import { memoryBoard } from "../src/extension/store.ts";

const created: string[] = [];

function dir(): string {
  const path = mkdtempSync(join(tmpdir(), "board-persist-"));
  created.push(path);
  return path;
}

/** A populated board exercising every state table. */
function populated() {
  const board = memoryBoard();
  board.register("alice");
  board.register("bob");
  board.bind("bob", "inbox");
  const delivered = board.send("alice", "inbox", "delivered", "m-1");
  const failed = board.send("alice", "inbox", "failed", "m-2");
  const queued = board.send("alice", "inbox", "queued", "m-3");
  board.deliver("bob", "inbox", delivered.message);
  board.fail("inbox", failed.message, "expired");
  board.post("alice", "design", "Why SQLite?", "Because transactions.", null, "p-1");
  board.subscribe("bob", "design");
  expect(board.state.mstatus[queued.message]).toBe("queued");
  return board;
}

afterEach(() => {
  for (const path of created.splice(0)) rmSync(path, { recursive: true, force: true });
});

describe("sqlite board backend", () => {
  it("round-trips a populated board exactly", () => {
    const backend = new SqliteBoardBackend(join(dir(), "board.db"));
    const state = populated().state;
    backend.write(state);
    expect(backend.read()).toEqual(state);
    backend.close();
  });

  it("reopens and lets a second connection read what the first wrote", () => {
    const path = join(dir(), "board.db");
    const first = new SqliteBoardBackend(path);
    first.write(populated().state);
    const revision = first.read()?.revision;
    first.close();
    const second = new SqliteBoardBackend(path);
    expect(second.read()?.revision).toBe(revision);
    second.close();
  });

  it("serializes read-modify-write through the transaction", () => {
    const backend = new SqliteBoardBackend(join(dir(), "board.db"));
    backend.write({ ...initBoardState(), revision: 7 });
    const next = backend.lock(() => {
      const current = backend.read()!;
      const updated = { ...current, revision: current.revision + 1 };
      backend.write(updated);
      return updated.revision;
    });
    expect(next).toBe(8);
    expect(backend.read()?.revision).toBe(8);
    backend.close();
  });

  it("imports an ack-era JSON board once, requeueing the leased message", () => {
    const root = dir();
    const legacy = legacyBoardPath(root);
    mkdirSync(dirname(legacy), { recursive: true });
    writeFileSync(
      legacy,
      JSON.stringify({
        registered: { alice: true },
        bound: { alice: "inbox" },
        owner: { inbox: "alice" },
        sender: { "m-1": "alice", "m-2": "alice", "m-3": "alice" },
        origin: { "m-1": "alice", "m-2": "alice", "m-3": "alice" },
        recipient: { "m-1": "inbox", "m-2": "inbox", "m-3": "inbox" },
        sentAt: { "m-1": 1, "m-2": 2, "m-3": 3 },
        mstatus: { "m-1": "fetched", "m-2": "queued", "m-3": "acked" },
        mailbox: { inbox: ["m-2"] },
        lease: { inbox: "m-1" },
        pstatus: {},
        author: {},
        porigin: {},
        parent: {},
        topic: {},
        posted: [],
        clock: 3,
        revision: 4,
        bodies: { "m-1": "one", "m-2": "two", "m-3": "three" },
        subjects: {},
        postBodies: {},
      }),
      "utf8",
    );
    const backend = new SqliteBoardBackend(boardPath(root), { legacyPath: legacy });
    const state = backend.read();
    expect(state?.mstatus["m-1"]).toBe("queued");
    expect(state?.mstatus["m-3"]).toBe("delivered");
    expect(state?.mailbox["inbox"]).toEqual(["m-1", "m-2"]);
    expect(state).not.toHaveProperty("lease");
    expect(existsSync(legacy)).toBe(false);
    expect(readdirSync(join(root, ".pi", "message-board")).some((name) => name.includes(".json.migrated-"))).toBe(true);
    const board = memoryBoard(state);
    expect(board.violations()).toEqual([]);
    backend.close();
  });

  it("keeps delivery metadata out of the state encoding", () => {
    const backend = new SqliteBoardBackend(join(dir(), "board.db"));
    backend.write(populated().state);
    const before = backend.read()!.revision;
    backend.ledger.record("m-1", Date.now(), Date.now() + 1_000);
    backend.ledger.setReason("m-1", "testing");
    backend.write(populated().state);
    expect(backend.read()!.revision).toBe(before);
    expect(backend.ledger.reason("m-1")).toBe("testing");
    backend.close();
  });
});

describe("importLegacyBoard", () => {
  it("maps statuses and prepends a leased message to its mailbox", () => {
    const state = importLegacyBoard(
      JSON.stringify({
        registered: { alice: true },
        bound: { alice: "inbox" },
        owner: { inbox: "alice" },
        sender: { "m-1": "alice" },
        origin: { "m-1": "alice" },
        recipient: { "m-1": "inbox" },
        sentAt: { "m-1": 1 },
        mstatus: { "m-1": "fetched" },
        mailbox: { inbox: [] },
        lease: { inbox: "m-1" },
      }),
    );
    expect(state.mstatus["m-1"]).toBe("queued");
    expect(state.mailbox["inbox"]).toEqual(["m-1"]);
    expect(state.subscribed["alice"]).toEqual([]);
  });
});

describe("repository-scoped board location", () => {
  function git(args: readonly string[], cwd: string): string {
    return execFileSync("git", args, { cwd, encoding: "utf8" });
  }

  it("shares one board file across linked worktrees without dirtying them", () => {
    const root = dir();
    git(["init", "-q", "-b", "main"], root);
    git(["config", "user.email", "board@example.com"], root);
    git(["config", "user.name", "board"], root);
    writeFileSync(join(root, ".gitignore"), ".worktrees/\n", "utf8");
    writeFileSync(join(root, "README.md"), "x\n", "utf8");
    git(["add", "-A"], root);
    git(["commit", "-qm", "init"], root);
    const worktree = join(root, ".worktrees", "n1");
    git(["worktree", "add", "-q", "-b", "dag/n1", worktree], root);

    // The dispatcher (root) and a node agent (worktree cwd) see the same board.
    expect(boardPath(worktree)).toBe(boardPath(root));
    expect(boardPath(root)).toContain(join(".git", "message-board"));
    expect(boardPath(root).endsWith("default.db")).toBe(true);
    new SqliteBoardBackend(boardPath(root)).write(initBoardState());
    // The DAG refuses to run against a dirty root; the board lives inside .git,
    // so it is invisible to `git status`.
    expect(git(["status", "--porcelain", "--untracked-files=all"], root).trim()).toBe("");
  });

  it("falls back to the working directory outside a repository", () => {
    const root = dir();
    expect(boardPath(root)).toBe(join(root, ".pi", "message-board", "default.db"));
    expect(legacyBoardPath(root)).toBe(join(root, ".pi", "message-board", "default.json"));
  });

  it("honours PI_MESSAGE_BOARD_DIR", () => {
    const root = dir();
    const override = dir();
    process.env["PI_MESSAGE_BOARD_DIR"] = override;
    try {
      expect(boardPath(root)).toBe(join(override, "default.db"));
    } finally {
      delete process.env["PI_MESSAGE_BOARD_DIR"];
    }
  });
});
