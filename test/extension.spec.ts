import { describe, expect, it } from "vitest";
import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import boardExtension, { BOARD_STATE_ENTRY, latestSnapshot } from "../src/index.ts";
import { initBoardState } from "../src/engine/board.ts";

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
});
