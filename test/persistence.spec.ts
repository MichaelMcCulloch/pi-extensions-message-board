import { execFileSync } from "node:child_process";
import { mkdtempSync, readdirSync, rmSync, utimesSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { boardPath, FileBoardBackend } from "../src/extension/persistence.ts";
import { initBoardState } from "../src/engine/board.ts";

const created: string[] = [];

function dir(): string {
  const path = mkdtempSync(join(tmpdir(), "board-persist-"));
  created.push(path);
  return path;
}

afterEach(() => {
  for (const path of created.splice(0)) rmSync(path, { recursive: true, force: true });
});

describe("file board backend", () => {
  it("round-trips a board", () => {
    const backend = new FileBoardBackend(boardPath(dir()));
    const state = initBoardState();
    backend.write(state);
    expect(backend.read()?.revision).toBe(state.revision);
  });

  it("quarantines a corrupt artifact instead of losing it", () => {
    const root = dir();
    const path = boardPath(root);
    const backend = new FileBoardBackend(path);
    writeFileSync(path, "{ not json", "utf8");
    expect(backend.read()).toBeNull();
    const quarantined = readdirSync(join(root, ".pi", "message-board")).filter((name) => name.includes(".corrupt-"));
    expect(quarantined).toHaveLength(1);
  });

  it("reclaims a stale lock", () => {
    const root = dir();
    const path = boardPath(root);
    const backend = new FileBoardBackend(path, { lockStaleMs: 1, lockTimeoutMs: 500, lockRetryMs: 2 });
    const lockPath = `${path}.lock`;
    writeFileSync(lockPath, "");
    const old = new Date(Date.now() - 60_000);
    utimesSync(lockPath, old, old);
    expect(backend.lock(() => "ok")).toBe("ok");
  });

  it("times out on a live lock instead of proceeding unsafely", () => {
    const root = dir();
    const path = boardPath(root);
    const backend = new FileBoardBackend(path, { lockStaleMs: 60_000, lockTimeoutMs: 50, lockRetryMs: 2 });
    writeFileSync(`${path}.lock`, "");
    expect(() => backend.lock(() => "no")).toThrow(/timed out/);
    rmSync(`${path}.lock`, { force: true });
  });

  it("serializes read-modify-write through the lock", () => {
    const root = dir();
    const path = boardPath(root);
    const backend = new FileBoardBackend(path);
    const state = { ...initBoardState(), revision: 7 };
    backend.write(state);
    const next = backend.lock(() => {
      const current = backend.read()!;
      const updated = { ...current, revision: current.revision + 1 };
      backend.write(updated);
      return updated.revision;
    });
    expect(next).toBe(8);
    expect(backend.read()?.revision).toBe(8);
  });
});

describe("repository-scoped board location", () => {
  function git(args: readonly string[], cwd: string): string {
    return execFileSync("git", args, { cwd, encoding: "utf8" });
  }

  it("shares one board across linked worktrees without dirtying them", () => {
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
    new FileBoardBackend(boardPath(root)).write(initBoardState());
    expect(boardPath(root)).toContain(join(".git", "message-board"));
    // The DAG refuses to run against a dirty root; the board lives inside .git,
    // so it is invisible to `git status`.
    expect(git(["status", "--porcelain", "--untracked-files=all"], root).trim()).toBe("");
  });

  it("falls back to the working directory outside a repository", () => {
    const root = dir();
    expect(boardPath(root)).toBe(join(root, ".pi", "message-board", "default.json"));
  });

  it("honours PI_MESSAGE_BOARD_DIR", () => {
    const root = dir();
    const override = dir();
    process.env["PI_MESSAGE_BOARD_DIR"] = override;
    try {
      expect(boardPath(root)).toBe(join(override, "default.json"));
    } finally {
      delete process.env["PI_MESSAGE_BOARD_DIR"];
    }
  });
});
