/**
 * pi extension entry point.
 *
 * The board is file-backed (SQLite) and shared, so agents in separate pi
 * processes (a DAG's children, a pedestrian subagent swarm) see one log. The
 * extension registers the `board` tool, a `/board` explorer, and a compact
 * summary widget that polls the shared file so it reflects other processes'
 * writes. A per-process pusher turns durable state into notifications: direct
 * messages into the serving agent's context, forum activity into the context of
 * subscribers, and failures back to senders.
 */

import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import type { TUI } from "@earendil-works/pi-tui";
import { initBoardState, type BoardState } from "./engine/board.ts";
import { BOARD_CHANGED } from "./extension/bus.ts";
import { boardPath, legacyBoardPath } from "./extension/persistence.ts";
import { BoardPusher } from "./extension/push.ts";
import { SqliteBoardBackend } from "./extension/sqlite.ts";
import { BoardStore } from "./extension/store.ts";
import { agentOf, buildBoardTool } from "./extension/tool.ts";
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

/** Host options: how the tools are split and which durable name a session prefers. */
export interface BoardExtensionOptions {
  splitTools?: boolean;
  /** Preferred mailbox name for a session; the session identity is the fallback. */
  mailboxName?: (ctx: ExtensionContext) => string | null | undefined;
}

/** Default export consumed by pi. */
export default function boardExtension(pi: ExtensionAPI, options: BoardExtensionOptions = {}): void {
  let store: BoardStore | null = null;
  let currentCtx: ExtensionContext | null = null;
  let widgetTui: TUI | null = null;
  let widgetInstalled = false;
  let poll: NodeJS.Timeout | null = null;
  let pusher: BoardPusher | null = null;
  let unsubscribeChanged: (() => void) | null = null;

  const openStore = (ctx: ExtensionContext): BoardStore =>
    new BoardStore(
      new SqliteBoardBackend(boardPath(ctx.cwd), { legacyPath: legacyBoardPath(ctx.cwd) }),
    );

  const getStore = (ctx: ExtensionContext): BoardStore => {
    if (store === null) {
      store = openStore(ctx);
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
      ctx.ui.setWidget(WIDGET_KEY, (tui, theme) => {
        widgetTui = tui;
        return new BoardWidget(
          () => renderBoardWidget(getStore(ctx)),
          8,
          () => void openExplorer(currentCtx ?? ctx),
          () => currentCtx?.ui.theme ?? theme,
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
      if (currentCtx === null) return;
      try {
        pusher?.tick();
      } catch {
        // A transient failure must not kill the watcher; the next tick retries.
      }
      refreshWidget();
    }, POLL_MS);
    poll.unref?.();
  };

  const stopPusher = (): void => {
    unsubscribeChanged?.();
    unsubscribeChanged = null;
    pusher = null;
  };
  const startPusher = (ctx: ExtensionContext): void => {
    stopPusher();
    pusher = new BoardPusher({
      store: getStore(ctx),
      agent: agentOf(ctx),
      notify: (notification) =>
        pi.sendMessage(
          {
            customType: `board/${notification.kind}`,
            content: notification.text,
            display: true,
            details: notification.details,
          },
          { triggerTurn: true },
        ),
      emit: (channel, data) => pi.events.emit(channel, data),
    });
    unsubscribeChanged = pi.events.on(BOARD_CHANGED, () => refreshWidget());
    pusher.tick();
  };

  pi.on("session_start", (_event, ctx) => {
    currentCtx = ctx;
    store = openStore(ctx);
    // Participation is lifecycle, not a model-facing action: every session is
    // registered and serves a mailbox before any message can be pushed.
    store.admit(agentOf(ctx), options.mailboxName?.(ctx));
    refreshWidget();
    startPolling();
    startPusher(ctx);
  });
  pi.on("session_tree", (_event, ctx) => {
    currentCtx = ctx;
    const current = getStore(ctx);
    current.refresh();
    current.admit(agentOf(ctx), options.mailboxName?.(ctx));
    refreshWidget();
  });
  pi.on("session_shutdown", (_event, ctx) => {
    const shutdownCtx = ctx ?? currentCtx;
    stopPolling();
    stopPusher();
    if (store !== null && shutdownCtx !== null) {
      // Best effort: release the name and leave the registry so a later
      // session can serve it. A crash still leaks both; stale-owner takeover
      // is a documented gap.
      try {
        const agent = agentOf(shutdownCtx);
        if (store.boundBox(agent) !== null) store.unbind(agent);
        store.unregister(agent);
      } catch {
        // Shutdown must not throw.
      }
    }
    hideWidget();
    store = null;
    currentCtx = null;
    widgetTui = null;
  });

  for (const facet of options.splitTools ? ['forum', 'mailbox'] as const : [undefined]) {
    const boardTool = buildBoardTool(getStore, facet);
    const execute = boardTool.execute!;
    boardTool.execute = async (...args) => {
      const result = await execute(...args);
      pusher?.notifyLocal();
      refreshWidget();
      return result;
    };
    pi.registerTool(boardTool);
  }

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
