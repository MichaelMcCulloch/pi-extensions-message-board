/**
 * Terminal presentation for the message board.
 *
 * The board is shared and file-backed, so the widget is a compact summary and
 * `/board` opens a read-only explorer: agents, mailboxes with their queued
 * previews, and every forum topic with its posts and bodies.
 */

import type { Theme } from "@earendil-works/pi-coding-agent";
import { Key, matchesKey, truncateToWidth, wrapTextWithAnsi, type Component, type TUI, type TuiMouseEvent, type TuiMouseEventResult } from "@earendil-works/pi-tui";
import type { BoardStore } from "./store.ts";

/** A compact summary for the persistent widget. Empty when the board is unused. */
export function renderBoardWidget(store: BoardStore): string[] {
  const board = store.projection;
  if (board.agents.length === 0 && board.boxes.length === 0 && board.posts.length === 0) return [];
  const topics = store.topics();
  const lines = [
    `board · rev ${board.revision} · ${board.agents.length} agents · ${board.boxes.length} mailboxes · ${board.posts.length} posts`,
  ];
  for (const box of board.boxes.slice(0, 4)) {
    lines.push(`  ${box.name} · ${box.queued} queued${box.owner === null ? " · unowned" : ` · served by ${box.owner}`}`);
  }
  if (topics.length > 0) lines.push(`  topics: ${topics.map((topic) => `${topic.topic}(${topic.posts})`).join(", ")}`);
  return lines;
}

/** The full explorer body: agents, every mailbox queue, and every topic thread. */
export function renderBoardDetail(store: BoardStore, width: number): string[] {
  const board = store.projection;
  const wrap = Math.max(20, width - 4);
  const lines = [`revision ${board.revision}`, ""];

  lines.push("AGENTS");
  if (board.agents.length === 0) lines.push("  (none registered)");
  for (const agent of board.agents) {
    lines.push(`  ${agent.id}${agent.box === null ? "" : ` · serves ${agent.box}`}${agent.subscribed.length === 0 ? "" : ` · watches ${agent.subscribed.map((topic) => `#${topic}`).join(", ")}`}`);
  }
  lines.push("");

  lines.push("MAILBOXES");
  if (board.boxes.length === 0) lines.push("  (none)");
  for (const box of board.boxes) {
    lines.push(`  ${box.name} · ${box.queued} queued${box.owner === null ? " · unowned" : ` · served by ${box.owner}`}${box.delivered === 0 ? "" : ` · ${box.delivered} delivered`}${box.failed === 0 ? "" : ` · ${box.failed} failed`}`);
    for (const entry of store.inbox(box.name)) {
      lines.push(`    ${entry.id}${entry.from === null ? "" : ` from ${entry.from}`}: ${entry.preview}`);
    }
  }
  lines.push("");

  lines.push("FORUM");
  const topics = store.topics();
  if (topics.length === 0) lines.push("  (no posts)");
  for (const topic of topics) {
    lines.push(`  #${topic.topic} (${topic.posts})`);
    for (const post of store.read(topic.topic)) {
      lines.push(`    ${post.id}${post.author === null ? "" : ` by ${post.author}`}${post.parent === null ? "" : ` ↩ ${post.parent}`} — ${post.subject}`);
      if (post.body.trim().length > 0) {
        for (const wrapped of wrapTextWithAnsi(post.body.trim(), wrap)) lines.push(`        ${wrapped}`);
      }
    }
  }
  return lines;
}

/** A full-width rule, dimmed when a theme is available. */
function separator(width: number, theme: Theme | undefined): string {
  const line = "─".repeat(Math.max(0, width));
  return theme === undefined ? line : theme.fg("borderMuted", line);
}

/** The persistent widget. `lines` is read on every render so it is always live. */
export class BoardWidget implements Component {
  public constructor(
    private readonly lines: () => string[],
    private readonly maxLines = 8,
    private readonly onActivate?: () => void,
    private readonly getTheme?: () => Theme,
  ) {}

  public invalidate(): void {
    // Rendering re-reads the shared board each frame.
  }

  public handleMouse(event: TuiMouseEvent): TuiMouseEventResult | undefined {
    if (event.type === "click" && event.button === "left" && this.onActivate !== undefined) {
      this.onActivate();
      return { handled: true };
    }
    return undefined;
  }

  public render(width: number): string[] {
    const body = this.lines();
    if (body.length === 0) return [];
    const shown = body.slice(0, this.maxLines);
    if (body.length > this.maxLines) shown.push(`… +${body.length - this.maxLines} more — click to open`);
    const fitted = shown.map((line) => truncateToWidth(line, width, "…", true));
    return [separator(width, this.getTheme?.()), ...fitted];
  }
}

/** The scrollable `/board` explorer overlay. */
export class BoardExplorer implements Component {
  #scroll = 0;
  #total = 0;

  public constructor(
    private readonly body: (width: number) => string[],
    private readonly tui: TUI,
    private readonly getTheme: () => Theme,
    private readonly done: () => void,
  ) {}

  public invalidate(): void {
    // The body is recomputed from the shared board each render.
  }

  public handleInput(data: string): void {
    if (matchesKey(data, Key.escape) || matchesKey(data, "ctrl+c") || matchesKey(data, "q")) {
      this.done();
      return;
    }
    if (matchesKey(data, Key.up)) this.#scroll -= 1;
    else if (matchesKey(data, Key.down)) this.#scroll += 1;
    else if (matchesKey(data, Key.pageUp)) this.#scroll -= this.#viewport();
    else if (matchesKey(data, Key.pageDown)) this.#scroll += this.#viewport();
    else if (matchesKey(data, Key.home)) this.#scroll = 0;
    else if (matchesKey(data, Key.end)) this.#scroll = Number.MAX_SAFE_INTEGER;
    this.#clamp();
    this.tui.requestRender();
  }

  public render(width: number): string[] {
    const theme = this.getTheme();
    const lines: string[] = [];
    lines.push(truncateToWidth(theme.bold(theme.fg("accent", "Board")) + theme.fg("dim", "   ↑/↓ scroll · q close"), width, "…", true));
    lines.push(theme.fg("borderMuted", "─".repeat(Math.max(0, width))));
    const body = this.body(Math.max(20, width - 2));
    this.#total = body.length;
    this.#clamp();
    const viewport = this.#viewport();
    const end = Math.min(body.length, this.#scroll + viewport);
    for (let i = this.#scroll; i < end; i++) lines.push(truncateToWidth(body[i] ?? "", width, "…", true));
    for (let i = end - this.#scroll; i < viewport; i++) lines.push(" ".repeat(Math.max(0, width)));
    lines.push(theme.fg("borderMuted", "─".repeat(Math.max(0, width))));
    const range = body.length === 0 ? "0/0" : `${this.#scroll + 1}-${end}/${body.length}`;
    lines.push(truncateToWidth(theme.fg("dim", range), width, "…", true));
    return lines;
  }

  #viewport(): number {
    return Math.max(3, this.tui.terminal.rows - 6);
  }

  #clamp(): void {
    const max = Math.max(0, this.#total - this.#viewport());
    if (this.#scroll < 0) this.#scroll = 0;
    else if (this.#scroll > max) this.#scroll = max;
  }
}
