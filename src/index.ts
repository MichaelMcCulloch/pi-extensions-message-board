/**
 * pi extension entry point.
 *
 * The board is file-backed and shared, so agents in separate pi processes (a
 * DAG's children, a pedestrian subagent swarm) see one log. The extension
 * registers the `board` tool, a `/board` explorer, and a compact summary widget
 * that polls the shared file so it reflects other processes' writes.
 */

import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import type { TUI } from "@earendil-works/pi-tui";
import { initBoardState, type BoardState } from "./engine/board.ts";
import { boardPath, FileBoardBackend } from "./extension/persistence.ts";
import { BoardStore } from "./extension/store.ts";
import { buildBoardTool } from "./extension/tool.ts";
import { BoardExplorer, BoardWidget, renderBoardDetail, renderBoardWidget } from "./extension/hud.ts";

/** The custom-entry type that carries one complete board snapshot. */
export const BOARD_STATE_ENTRY = "board/state";

/** The widget slot above the editor. */
const WIDGET_KEY = "message-board";

/** Poll cadence for the shared file, so other processes' writes show up. */
const POLL_MS = 2_000;

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
  let currentCtx: ExtensionContext | null = null;
  let widgetTui: TUI | null = null;
  let widgetInstalled = false;
  let poll: NodeJS.Timeout | null = null;

  const getStore = (ctx: ExtensionContext): BoardStore => {
    if (store === null) {
      store = new BoardStore(new FileBoardBackend(boardPath(ctx.cwd)));
      void latestSnapshot(ctx);
    }
    return store;
  };

  const hideWidget = (): void => {
    if (widgetInstalled && currentCtx !== null && currentCtx.mode === "tui" && currentCtx.hasUI) {
      currentCtx.ui.setWidget(WIDGET_KEY, undefined);
    }
    widgetInstalled = false;
  };

  const refreshWidget = (): void => {
    const ctx = currentCtx;
    if (ctx === null) return;
    const board = getStore(ctx).projection;
    if (ctx.mode !== "tui" || !ctx.hasUI) return;
    if (board.agents.length === 0 && board.boxes.length === 0 && board.posts.length === 0) {
      hideWidget();
      return;
    }
    if (!widgetInstalled) {
      ctx.ui.setWidget(WIDGET_KEY, (tui) => {
        widgetTui = tui;
        return new BoardWidget(
          () => renderBoardWidget(getStore(ctx)),
          8,
          () => void openExplorer(currentCtx ?? ctx),
        );
      });
      widgetInstalled = true;
    }
    widgetTui?.requestRender();
  };

  const stopPolling = (): void => {
    if (poll !== null) {
      clearInterval(poll);
      poll = null;
    }
  };
  const startPolling = (): void => {
    stopPolling();
    poll = setInterval(() => {
      if (currentCtx !== null) getStore(currentCtx).refresh();
      refreshWidget();
    }, POLL_MS);
    poll.unref?.();
  };

  pi.on("session_start", (_event, ctx) => {
    currentCtx = ctx;
    store = new BoardStore(new FileBoardBackend(boardPath(ctx.cwd)));
    refreshWidget();
    startPolling();
  });
  pi.on("session_tree", (_event, ctx) => {
    currentCtx = ctx;
    getStore(ctx).refresh();
    refreshWidget();
  });
  pi.on("session_shutdown", () => {
    stopPolling();
    hideWidget();
    store = null;
    currentCtx = null;
    widgetTui = null;
  });

  pi.registerTool(buildBoardTool(getStore));

  const openExplorer = async (ctx: ExtensionContext): Promise<void> => {
    if (ctx.mode !== "tui" || !ctx.hasUI) return;
    await ctx.ui.custom<undefined>(
      (tui, theme, _keybindings, done) =>
        new BoardExplorer(
          (width) => renderBoardDetail(getStore(ctx), width),
          tui,
          () => ctx.ui.theme,
          () => done(undefined),
        ),
      { overlay: true, overlayOptions: { width: "92%", maxHeight: "92%", anchor: "center", margin: 1 } },
    );
  };

  pi.registerCommand("board", {
    description: "Show the shared agent board; open the scrollable explorer",
    handler: async (_args, ctx) => {
      if (ctx.mode !== "tui" || !ctx.hasUI) {
        ctx.ui.notify(renderBoardDetail(getStore(ctx), 100).join("\n"), "info");
        return;
      }
      await openExplorer(ctx);
    },
  });
}

/** A fresh in-memory board state, exported for tests. */
export { initBoardState };
