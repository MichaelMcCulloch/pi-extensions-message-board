/**
 * pi extension entry point.
 *
 * The board is file-backed and shared, so agents in separate pi processes (a
 * DAG's children, a pedestrian subagent swarm) see one log. The extension
 * registers the `board` tool and a `/board` command and reloads on session
 * start and tree navigation.
 */

import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import { initBoardState, type BoardState } from "./engine/board.ts";
import { boardPath, FileBoardBackend } from "./extension/persistence.ts";
import { BoardStore } from "./extension/store.ts";
import { buildBoardTool } from "./extension/tool.ts";

/** The custom-entry type that carries one complete board snapshot. */
export const BOARD_STATE_ENTRY = "board/state";

/** Fold the newest persisted snapshot out of a session branch. */
export function latestSnapshot(ctx: ExtensionContext): BoardState | null {
  let latest: BoardState | null = null;
  for (const entry of ctx.sessionManager.getBranch()) {
    if (entry.type === "custom" && entry.customType === BOARD_STATE_ENTRY && entry.data !== undefined) {
      latest = entry.data as BoardState;
    }
  }
  return latest;
}

/** Default export consumed by pi. */
export default function boardExtension(pi: ExtensionAPI): void {
  let store: BoardStore | null = null;

  const getStore = (ctx: ExtensionContext): BoardStore => {
    if (store === null) {
      store = new BoardStore(new FileBoardBackend(boardPath(ctx.cwd)));
      void latestSnapshot(ctx);
    }
    return store;
  };

  pi.on("session_start", (_event, ctx) => {
    store = new BoardStore(new FileBoardBackend(boardPath(ctx.cwd)));
  });
  pi.on("session_tree", (_event, ctx) => {
    getStore(ctx).refresh();
  });
  pi.on("session_shutdown", () => {
    store = null;
  });

  pi.registerTool(buildBoardTool(getStore));

  pi.registerCommand("board", {
    description: "Show the shared agent board",
    handler: async (_args, ctx) => {
      const board = getStore(ctx).projection;
      const lines = [
        `revision ${board.revision}`,
        `agents: ${board.agents.map((agent) => `${agent.id}${agent.box === null ? "" : `@${agent.box}`}`).join(", ") || "(none)"}`,
        `mailboxes: ${board.boxes.map((box) => `${box.name}(${box.queued} queued${box.owner === null ? ", unowned" : `, ${box.owner}`})`).join(", ") || "(none)"}`,
        `topics: ${getStore(ctx).topics().map((topic) => `${topic.topic}(${topic.posts})`).join(", ") || "(none)"}`,
      ];
      ctx.ui.notify(lines.join("\n"), "info");
    },
  });
}

/** A fresh in-memory board state, exported for tests. */
export { initBoardState };
