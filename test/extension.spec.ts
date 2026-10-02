import { describe, expect, it } from "vitest";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import boardExtension, { BOARD_STATE_ENTRY, latestSnapshot } from "../src/index.ts";
import { initBoardState } from "../src/engine/board.ts";
import { boardPath } from "../src/extension/persistence.ts";
import { SqliteBoardBackend } from "../src/extension/sqlite.ts";

function fakeCtx(branch: readonly unknown[]): ExtensionContext {
  return { sessionManager: { getBranch: () => branch } } as unknown as ExtensionContext;
}

describe("extension wiring", () => {
  it("registers the board tool, command, and lifecycle handlers", () => {
    const tools: string[] = [];
    const commands: string[] = [];
    const events: string[] = [];
    const pi = {
      on: (event: string) => {
        events.push(event);
      },
      registerTool: (tool: { name: string }) => {
        tools.push(tool.name);
      },
      registerCommand: (name: string) => {
        commands.push(name);
      },
      appendEntry: () => {},
    } as unknown as ExtensionAPI;

    boardExtension(pi);
    expect(tools).toEqual(["board"]);
    expect(commands).toEqual(["board"]);
    expect(events).toContain("session_start");
    expect(events).toContain("session_tree");
  });

  it("folds the newest persisted snapshot and ignores other entries", () => {
    const first = initBoardState();
    const branch = [
      { type: "message", message: {} },
      { type: "custom", customType: "other", data: {} },
      { type: "custom", customType: BOARD_STATE_ENTRY, data: first },
    ];
    expect(latestSnapshot(fakeCtx(branch))).toBe(first);
  });

  it("returns null for an empty branch", () => {
    expect(latestSnapshot(fakeCtx([]))).toBeNull();
  });

  it("admits the session on start and releases its name on shutdown", () => {
    const dir = mkdtempSync(join(tmpdir(), "board-extension-"));
    const handlers = new Map<string, (event: unknown, ctx: ExtensionContext) => unknown>();
    const pi = {
      on: (event: string, handler: (event: unknown, ctx: ExtensionContext) => unknown) => {
        handlers.set(event, handler);
      },
      registerTool: () => {},
      registerCommand: () => {},
      appendEntry: () => {},
      sendMessage: () => {},
      events: { on: () => () => {}, emit: () => {} },
    } as unknown as ExtensionAPI;
    const ctx = {
      cwd: dir,
      mode: "print",
      hasUI: false,
      sessionManager: { getSessionId: () => "s1", getBranch: () => [] },
    } as unknown as ExtensionContext;
    const backend = new SqliteBoardBackend(boardPath(dir));
    try {
      boardExtension(pi, { splitTools: true, mailboxName: () => "coordinator" });
      handlers.get("session_start")!({}, ctx);
      const admitted = backend.read()!;
      expect(admitted.registered["s1"]).toBe(true);
      expect(admitted.bound["s1"]).toBe("coordinator");

      handlers.get("session_shutdown")!({}, ctx);
      const released = backend.read()!;
      expect(released.bound["s1"]).toBe(null);
      expect(released.registered["s1"]).toBe(false);
      expect(released.owner["coordinator"]).toBe(null);
    } finally {
      backend.close();
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
