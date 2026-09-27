/**
 * Board persistence.
 *
 * The board must be shared by agents running in different pi processes, so the
 * durable store is a single SQLite file (see `sqlite.ts`). This module owns the
 * backend contract, the in-memory backend tests use, the repository-scoped
 * location, and the one-time import of ack-era JSON boards.
 */

import { execFileSync } from "node:child_process";
import { join, resolve } from "node:path";
import { initBoardState, type BoardState } from "../engine/board.ts";
import type { MessageStatus } from "../formal/model.ts";

/**
 * Operational delivery metadata: deadlines, failure reasons, and which failure
 * notices were already injected. Deliberately NOT part of `BoardState` — the
 * verified state does not model clocks, and the state writer must not rewrite
 * this table. Both backends provide one.
 */
export interface DeliveryLedger {
  /** Record a freshly queued message; `deadlineAt` is null when it waits forever. */
  record(message: string, createdAt: number, deadlineAt: number | null): void;
  /** Messages whose deadline has passed by `now`. */
  due(now: number): readonly string[];
  /** The failure reason, or null. */
  reason(message: string): string | null;
  setReason(message: string, reason: string): void;
  /** When the sender was told, or null. */
  notifiedAt(message: string): number | null;
  markNotified(message: string, at: number): void;
}

/** An in-process ledger for tests and single-process use. */
export class MemoryDeliveryLedger implements DeliveryLedger {
  readonly #entries = new Map<string, { createdAt: number; deadlineAt: number | null; reason: string | null; notifiedAt: number | null }>();

  public record(message: string, createdAt: number, deadlineAt: number | null): void {
    this.#entries.set(message, { createdAt, deadlineAt, reason: null, notifiedAt: null });
  }

  public due(now: number): readonly string[] {
    return [...this.#entries]
      .filter(([, entry]) => entry.deadlineAt !== null && entry.deadlineAt <= now)
      .map(([message]) => message);
  }

  public reason(message: string): string | null {
    return this.#entries.get(message)?.reason ?? null;
  }

  public setReason(message: string, reason: string): void {
    const entry = this.#entries.get(message);
    if (entry !== undefined) entry.reason = reason;
  }

  public notifiedAt(message: string): number | null {
    return this.#entries.get(message)?.notifiedAt ?? null;
  }

  public markNotified(message: string, at: number): void {
    const entry = this.#entries.get(message);
    if (entry !== undefined) entry.notifiedAt = at;
  }
}

/** The durable backend the store mutates through. */
export interface BoardBackend {
  readonly ledger: DeliveryLedger;
  read(): BoardState | null;
  write(state: BoardState): void;
  lock<T>(operation: () => T): T;
}

/** An in-process backend for tests and single-process use. */
export class MemoryBoardBackend implements BoardBackend {
  #state: BoardState | null;
  public readonly ledger = new MemoryDeliveryLedger();

  public constructor(initial: BoardState | null = null) {
    this.#state = initial;
  }

  public read(): BoardState | null {
    return this.#state;
  }

  public write(state: BoardState): void {
    this.#state = state;
  }

  public lock<T>(operation: () => T): T {
    return operation();
  }
}

/**
 * The git common directory of `cwd`, or undefined when `cwd` is not in a git
 * repository (or git is unavailable).
 *
 * `--git-common-dir` is the shared `.git` of every linked worktree. That is the
 * anchor for a board shared by a repository's checkouts: the main worktree and
 * each of the DAG's per-node worktrees resolve to the same directory, while
 * nothing the board writes is part of any working tree (so it can never make a
 * checkout dirty or be committed by a node).
 */
function gitCommonDirectory(cwd: string): string | undefined {
  const run = (args: readonly string[]): string | undefined => {
    try {
      const out = execFileSync("git", ["-C", cwd, ...args], {
        encoding: "utf8",
        stdio: ["ignore", "pipe", "ignore"],
      }).trim();
      return out.length > 0 ? out : undefined;
    } catch {
      return undefined;
    }
  };
  const absolute = run(["rev-parse", "--path-format=absolute", "--git-common-dir"]);
  if (absolute !== undefined) return absolute;
  // git < 2.31 has no --path-format; its output can be relative to cwd.
  const relative = run(["rev-parse", "--git-common-dir"]);
  return relative !== undefined ? resolve(cwd, relative) : undefined;
}

/** Where a repository's shared board lives: inside the git common directory. */
export function boardDirectory(cwd: string): string {
  if (process.env["PI_MESSAGE_BOARD_DIR"]) return process.env["PI_MESSAGE_BOARD_DIR"]!;
  const common = gitCommonDirectory(cwd);
  // Inside a repository every worktree shares `.git`; outside one, fall back to
  // the working directory as before.
  return common !== undefined ? join(common, "message-board") : join(cwd, ".pi", "message-board");
}

/** Where a shared board lives under a working directory. */
export function boardPath(cwd: string, board = "default"): string {
  return join(boardDirectory(cwd), `${board}.db`);
}

/** Where an ack-era JSON board lived, for the one-time import. */
export function legacyBoardPath(cwd: string, board = "default"): string {
  return join(boardDirectory(cwd), `${board}.json`);
}

/** Initialize an empty board and repair fields that older snapshots omitted. */
export function ensureBoard(state: BoardState | null): BoardState {
  if (state === null) return initBoardState();
  const base = initBoardState();
  // Snapshots written by older versions can omit whole fields (`owner` and
  // `subscribed` did not always exist), not just per-id entries. Rebuild every
  // map from the ids the snapshot does carry, then fill the missing entries
  // with the same defaults `initAbstractBoardState` uses.
  const registered = { ...(state.registered ?? {}) };
  const bound = { ...(state.bound ?? {}) };
  const owner = { ...(state.owner ?? {}) };
  const mailbox = { ...(state.mailbox ?? {}) };
  const subscribed = { ...(state.subscribed ?? {}) } as Record<string, readonly string[]>;
  const sender = { ...(state.sender ?? {}) };
  const origin = { ...(state.origin ?? {}) };
  const recipient = { ...(state.recipient ?? {}) };
  const sentAt = { ...(state.sentAt ?? {}) };
  const mstatus = { ...(state.mstatus ?? {}) };
  const pstatus = { ...(state.pstatus ?? {}) };
  const author = { ...(state.author ?? {}) };
  const porigin = { ...(state.porigin ?? {}) };
  const parent = { ...(state.parent ?? {}) };
  const topic = { ...(state.topic ?? {}) };

  for (const agent of new Set([...Object.keys(registered), ...Object.keys(bound), ...Object.keys(subscribed)])) {
    if (registered[agent] === undefined) registered[agent] = false;
    if (bound[agent] === undefined) bound[agent] = null;
    if (subscribed[agent] === undefined) subscribed[agent] = [];
  }
  for (const box of new Set([...Object.keys(mailbox), ...Object.keys(owner)])) {
    if (mailbox[box] === undefined) mailbox[box] = [];
    if (owner[box] === undefined) owner[box] = null;
  }
  for (const message of new Set([...Object.keys(mstatus), ...Object.keys(sender), ...Object.keys(origin), ...Object.keys(recipient), ...Object.keys(sentAt)])) {
    if (mstatus[message] === undefined) mstatus[message] = "absent";
    if (sender[message] === undefined) sender[message] = null;
    if (origin[message] === undefined) origin[message] = null;
    if (recipient[message] === undefined) recipient[message] = null;
    if (sentAt[message] === undefined) sentAt[message] = 0;
  }
  for (const post of new Set([...Object.keys(pstatus), ...Object.keys(author), ...Object.keys(porigin), ...Object.keys(parent), ...Object.keys(topic)])) {
    if (pstatus[post] === undefined) pstatus[post] = "absent";
    if (author[post] === undefined) author[post] = null;
    if (porigin[post] === undefined) porigin[post] = null;
    if (parent[post] === undefined) parent[post] = null;
    if (topic[post] === undefined) topic[post] = null;
  }
  return {
    ...base,
    ...state,
    registered,
    bound,
    owner,
    mailbox,
    subscribed,
    sender,
    origin,
    recipient,
    sentAt,
    mstatus,
    pstatus,
    author,
    porigin,
    parent,
    topic,
    posted: state.posted ?? [],
    clock: state.clock ?? 0,
    revision: state.revision ?? 0,
    bodies: state.bodies ?? {},
    subjects: state.subjects ?? {},
    postBodies: state.postBodies ?? {},
  };
}

/**
 * Import an ack-era JSON board into the push revision.
 *
 * The old two-phase lifecycle maps onto the new one without loss: a queued
 * message stays queued, a fetched-but-unacked message returns to its mailbox
 * (it was never committed, so it must be delivered again), and an acked
 * message becomes delivered. The old `lease` map is dropped; a leased message
 * is prepended to its mailbox because the old invariant guaranteed it preceded
 * the messages still in the queue.
 */
export function importLegacyBoard(raw: string): BoardState {
  const parsed = JSON.parse(raw) as Record<string, unknown>;
  const oldStatus = (value: unknown): MessageStatus => {
    switch (value) {
      case "queued":
        return "queued";
      case "fetched":
      case "acked":
        return value === "acked" ? "delivered" : "queued";
      case "delivered":
      case "failed":
        return value;
      default:
        return "absent";
    }
  };
  const oldMailbox = (parsed["mailbox"] ?? {}) as Record<string, string[]>;
  const oldLease = (parsed["lease"] ?? {}) as Record<string, string | null>;
  const mailbox: Record<string, string[]> = {};
  for (const [box, queue] of Object.entries(oldMailbox)) mailbox[box] = [...queue];
  for (const [box, message] of Object.entries(oldLease)) {
    if (message === null) continue;
    mailbox[box] = [message, ...(mailbox[box] ?? [])];
  }
  const mstatus: Record<string, MessageStatus> = {};
  for (const [message, status] of Object.entries((parsed["mstatus"] ?? {}) as Record<string, unknown>)) {
    mstatus[message] = oldStatus(status);
  }
  const migrated = { ...parsed, mailbox, mstatus } as unknown as BoardState;
  delete (migrated as unknown as Record<string, unknown>)["lease"];
  return ensureBoard(migrated);
}
