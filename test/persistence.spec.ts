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
