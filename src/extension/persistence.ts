/**
 * Board persistence.
 *
 * The board must be shared by agents running in different pi processes, so the
 * durable store is a file guarded by a lock file. Every mutation re-reads the
 * current board under the lock, applies one command, and atomically replaces the
 * file, so two processes cannot lose each other's messages. Tests use the
 * in-memory backend, which shares the same interface without the filesystem.
 */

import {
  closeSync,
  existsSync,
  mkdirSync,
  openSync,
  readFileSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { initBoardState, type BoardState } from "../engine/board.ts";

/** The durable backend the store mutates through. */
export interface BoardBackend {
  read(): BoardState | null;
  write(state: BoardState): void;
  lock<T>(operation: () => T): T;
}

/** An in-process backend for tests and single-process use. */
export class MemoryBoardBackend implements BoardBackend {
  #state: BoardState | null;

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

const LOCK_STALE_MS = 5_000;
const LOCK_RETRY_MS = 5;
const LOCK_TIMEOUT_MS = 5_000;

/** Tunables for the file backend's advisory lock. */
export interface FileBackendOptions {
  readonly lockStaleMs?: number;
  readonly lockTimeoutMs?: number;
  readonly lockRetryMs?: number;
}

function sleep(ms: number): void {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
}

/**
 * A file backend with a best-effort advisory lock.
 *
 * `write` goes through a temporary file and a rename so a crash cannot leave a
 * half-written board. The lock is a sibling `*.lock` file; a lock older than
 * {@link LOCK_STALE_MS} is treated as a crashed holder and reclaimed.
 */
export class FileBoardBackend implements BoardBackend {
  readonly #path: string;
  readonly #lockPath: string;
  readonly #lockStaleMs: number;
  readonly #lockTimeoutMs: number;
  readonly #lockRetryMs: number;

  public constructor(path: string, options: FileBackendOptions = {}) {
    this.#path = path;
    this.#lockPath = `${path}.lock`;
    this.#lockStaleMs = options.lockStaleMs ?? LOCK_STALE_MS;
    this.#lockTimeoutMs = options.lockTimeoutMs ?? LOCK_TIMEOUT_MS;
    this.#lockRetryMs = options.lockRetryMs ?? LOCK_RETRY_MS;
    mkdirSync(dirname(path), { recursive: true });
  }

  public read(): BoardState | null {
    if (!existsSync(this.#path)) return null;
    const raw = readFileSync(this.#path, "utf8");
    if (raw.trim().length === 0) return null;
    try {
      return JSON.parse(raw) as BoardState;
    } catch {
      // A corrupt artifact must not be silently treated as an empty board: it
      // is quarantined beside the log so the data survives and the board starts
      // from a clean file.
      renameSync(this.#path, `${this.#path}.corrupt-${Date.now()}`);
      return null;
    }
  }

  public write(state: BoardState): void {
    const temporary = `${this.#path}.${process.pid}.tmp`;
    writeFileSync(temporary, JSON.stringify(state));
    renameSync(temporary, this.#path);
  }

  public lock<T>(operation: () => T): T {
    const started = Date.now();
    for (;;) {
      try {
        closeSync(openSync(this.#lockPath, "wx"));
        break;
      } catch {
        if (existsSync(this.#lockPath)) {
          try {
            if (Date.now() - statSync(this.#lockPath).mtimeMs > this.#lockStaleMs) {
              rmSync(this.#lockPath, { force: true });
              continue;
            }
          } catch {
            continue;
          }
        }
        if (Date.now() - started > this.#lockTimeoutMs) {
          throw new Error(`timed out acquiring ${this.#lockPath}`);
        }
        sleep(this.#lockRetryMs);
      }
    }
    try {
      return operation();
    } finally {
      rmSync(this.#lockPath, { force: true });
    }
  }
}

/** Where a shared board lives under a working directory. */
export function boardPath(cwd: string, board = "default"): string {
  return join(cwd, ".pi", "message-board", `${board}.json`);
}

/** Initialize an empty board and repair fields that older snapshots omitted. */
export function ensureBoard(state: BoardState | null): BoardState {
  if (state === null) return initBoardState();
  const base = initBoardState();
  // Snapshots written by older versions can omit whole fields (`owner` and
  // `lease` did not exist before unbound sends were tracked), not just per-id
  // entries. Rebuild every map from the ids the snapshot does carry, then fill
  // the missing entries with the same defaults `initAbstractBoardState` uses.
  const registered = { ...(state.registered ?? {}) };
  const bound = { ...(state.bound ?? {}) };
  const owner = { ...(state.owner ?? {}) };
  const mailbox = { ...(state.mailbox ?? {}) };
  const lease = { ...(state.lease ?? {}) };
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

  for (const agent of new Set([...Object.keys(registered), ...Object.keys(bound)])) {
    if (registered[agent] === undefined) registered[agent] = false;
    if (bound[agent] === undefined) bound[agent] = null;
  }
  for (const box of new Set([...Object.keys(mailbox), ...Object.keys(owner), ...Object.keys(lease)])) {
    if (mailbox[box] === undefined) mailbox[box] = [];
    if (owner[box] === undefined) owner[box] = null;
    if (lease[box] === undefined) lease[box] = null;
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
    lease,
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
