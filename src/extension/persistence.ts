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

  public constructor(path: string) {
    this.#path = path;
    this.#lockPath = `${path}.lock`;
    mkdirSync(dirname(path), { recursive: true });
  }

  public read(): BoardState | null {
    if (!existsSync(this.#path)) return null;
    const raw = readFileSync(this.#path, "utf8");
    if (raw.trim().length === 0) return null;
    return JSON.parse(raw) as BoardState;
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
            if (Date.now() - statSync(this.#lockPath).mtimeMs > LOCK_STALE_MS) {
              rmSync(this.#lockPath, { force: true });
              continue;
            }
          } catch {
            continue;
          }
        }
        if (Date.now() - started > LOCK_TIMEOUT_MS) {
          throw new Error(`timed out acquiring ${this.#lockPath}`);
        }
        sleep(LOCK_RETRY_MS);
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

/** Guard against an empty file being parsed as a board. */
export function ensureBoard(state: BoardState | null): BoardState {
  return state ?? initBoardState();
}
