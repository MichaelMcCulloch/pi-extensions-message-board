/**
 * SQLite storage for the board.
 *
 * SQLite is **storage, not engine**: this backend encodes the same `BoardState`
 * the reducer produces. `read` reconstructs the state in one read transaction,
 * `write` replaces the state tables in one write transaction, and `lock` is
 * `BEGIN IMMEDIATE`, so cross-process exclusion is SQLite's rather than a
 * hand-rolled lock file.
 *
 * Operational delivery metadata (deadlines, failure reasons, which notices were
 * injected) lives in the `delivery` table, which `write` never touches: the
 * encoding of `BoardState` stays exact and round-trips bit for bit.
 */

import { DatabaseSync } from "node:sqlite";
import { existsSync, mkdirSync, readFileSync, renameSync } from "node:fs";
import { dirname } from "node:path";
import { initBoardState, type BoardState } from "../engine/board.ts";
import {
  ensureBoard,
  importLegacyBoard,
  type BoardBackend,
  type DeliveryLedger,
} from "./persistence.ts";

const SCHEMA = `
CREATE TABLE IF NOT EXISTS agents (
  agent TEXT PRIMARY KEY,
  registered INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS boxes (
  name TEXT PRIMARY KEY,
  owner TEXT
);
CREATE TABLE IF NOT EXISTS messages (
  id TEXT PRIMARY KEY,
  sender TEXT,
  origin TEXT,
  recipient TEXT,
  sent_at INTEGER NOT NULL,
  status TEXT NOT NULL,
  body TEXT NOT NULL DEFAULT ''
);
CREATE TABLE IF NOT EXISTS posts (
  id TEXT PRIMARY KEY,
  seq INTEGER NOT NULL UNIQUE,
  author TEXT,
  origin TEXT,
  topic TEXT,
  parent TEXT,
  subject TEXT NOT NULL DEFAULT '',
  body TEXT NOT NULL DEFAULT ''
);
CREATE TABLE IF NOT EXISTS subscriptions (
  agent TEXT NOT NULL,
  topic TEXT NOT NULL,
  PRIMARY KEY (agent, topic)
);
CREATE TABLE IF NOT EXISTS meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS delivery (
  id TEXT PRIMARY KEY,
  created_at INTEGER NOT NULL,
  deadline_at INTEGER,
  notified_at INTEGER,
  fail_reason TEXT
);
CREATE INDEX IF NOT EXISTS messages_recipient ON messages (recipient, status, sent_at);
`;

/** The operational ledger, backed by the `delivery` table. */
class SqliteDeliveryLedger implements DeliveryLedger {
  readonly #db: DatabaseSync;

  public constructor(db: DatabaseSync) {
    this.#db = db;
  }

  public record(message: string, createdAt: number, deadlineAt: number | null): void {
    this.#db
      .prepare(
        `INSERT INTO delivery (id, created_at, deadline_at) VALUES (?, ?, ?)
         ON CONFLICT(id) DO UPDATE SET created_at = excluded.created_at, deadline_at = excluded.deadline_at`,
      )
      .run(message, createdAt, deadlineAt);
  }

  public due(now: number): readonly string[] {
    const rows = this.#db
      .prepare("SELECT id FROM delivery WHERE deadline_at IS NOT NULL AND deadline_at <= ?")
      .all(now) as { id: string }[];
    return rows.map((row) => row.id);
  }

  public reason(message: string): string | null {
    const row = this.#db.prepare("SELECT fail_reason FROM delivery WHERE id = ?").get(message) as
      | { fail_reason: string | null }
      | undefined;
    return row?.fail_reason ?? null;
  }

  public setReason(message: string, reason: string): void {
    this.#db
      .prepare(
        `INSERT INTO delivery (id, created_at, fail_reason) VALUES (?, ?, ?)
         ON CONFLICT(id) DO UPDATE SET fail_reason = excluded.fail_reason`,
      )
      .run(message, Date.now(), reason);
  }

  public notifiedAt(message: string): number | null {
    const row = this.#db.prepare("SELECT notified_at FROM delivery WHERE id = ?").get(message) as
      | { notified_at: number | null }
      | undefined;
    return row?.notified_at ?? null;
  }

  public markNotified(message: string, at: number): void {
    this.#db
      .prepare(
        `INSERT INTO delivery (id, created_at, notified_at) VALUES (?, ?, ?)
         ON CONFLICT(id) DO UPDATE SET notified_at = excluded.notified_at`,
      )
      .run(message, at, at);
  }
}

/** Options for the SQLite backend. */
export interface SqliteBackendOptions {
  /** An ack-era JSON board to import once, then rename aside. */
  readonly legacyPath?: string;
}

/** A SQLite-backed board. One connection per process; WAL handles contention. */
export class SqliteBoardBackend implements BoardBackend {
  readonly #db: DatabaseSync;
  #depth = 0;
  public readonly ledger: DeliveryLedger;

  public constructor(path: string, options: SqliteBackendOptions = {}) {
    mkdirSync(dirname(path), { recursive: true });
    this.#db = new DatabaseSync(path);
    this.#db.exec("PRAGMA journal_mode = WAL");
    this.#db.exec("PRAGMA busy_timeout = 5000");
    this.#db.exec(SCHEMA);
    this.ledger = new SqliteDeliveryLedger(this.#db);
    const legacy = options.legacyPath;
    if (legacy !== undefined && existsSync(legacy) && !this.#hasState()) {
      const state = importLegacyBoard(readFileSync(legacy, "utf8"));
      this.write(state);
      renameSync(legacy, `${legacy}.migrated-${Date.now()}`);
    }
  }

  public read(): BoardState | null {
    return this.#transaction("DEFERRED", () => {
      const meta = new Map(
        (this.#db.prepare("SELECT key, value FROM meta").all() as { key: string; value: string }[]).map(
          (row) => [row.key, row.value] as const,
        ),
      );
      if (meta.size === 0) return null;

      const registered: Record<string, boolean> = {};
      const bound: Record<string, string | null> = {};
      const subscribed: Record<string, string[]> = {};
      for (const row of this.#db.prepare("SELECT agent, registered FROM agents").all() as { agent: string; registered: number }[]) {
        registered[row.agent] = row.registered !== 0;
        bound[row.agent] = null;
        subscribed[row.agent] = [];
      }
      for (const row of this.#db
        .prepare("SELECT agent, topic FROM subscriptions ORDER BY topic")
        .all() as { agent: string; topic: string }[]) {
        (subscribed[row.agent] ??= []).push(row.topic);
      }

      const owner: Record<string, string | null> = {};
      const mailbox: Record<string, string[]> = {};
      for (const row of this.#db.prepare("SELECT name, owner FROM boxes").all() as {
        name: string;
        owner: string | null;
      }[]) {
        owner[row.name] = row.owner ?? null;
        mailbox[row.name] = [];
        if (row.owner !== null && row.owner !== undefined) bound[row.owner] = row.name;
      }

      const sender: Record<string, string | null> = {};
      const origin: Record<string, string | null> = {};
      const recipient: Record<string, string | null> = {};
      const sentAt: Record<string, number> = {};
      const mstatus: Record<string, string> = {};
      const bodies: Record<string, string> = {};
      for (const row of this.#db.prepare("SELECT * FROM messages ORDER BY sent_at").all() as {
        id: string;
        sender: string | null;
        origin: string | null;
        recipient: string | null;
        sent_at: number;
        status: string;
        body: string;
      }[]) {
        sender[row.id] = row.sender ?? null;
        origin[row.id] = row.origin ?? null;
        recipient[row.id] = row.recipient ?? null;
        sentAt[row.id] = row.sent_at;
        mstatus[row.id] = row.status;
        bodies[row.id] = row.body;
        if (row.recipient !== null && owner[row.recipient] === undefined) {
          owner[row.recipient] = null;
          mailbox[row.recipient] = [];
        }
        if (row.status === "queued" && row.recipient !== null) mailbox[row.recipient]!.push(row.id);
      }

      const pstatus: Record<string, string> = {};
      const author: Record<string, string | null> = {};
      const porigin: Record<string, string | null> = {};
      const parent: Record<string, string | null> = {};
      const topic: Record<string, string | null> = {};
      const subjects: Record<string, string> = {};
      const postBodies: Record<string, string> = {};
      const posted: string[] = [];
      for (const row of this.#db.prepare("SELECT * FROM posts ORDER BY seq").all() as {
        id: string;
        author: string | null;
        origin: string | null;
        topic: string | null;
        parent: string | null;
        subject: string;
        body: string;
      }[]) {
        posted.push(row.id);
        pstatus[row.id] = "posted";
        author[row.id] = row.author ?? null;
        porigin[row.id] = row.origin ?? null;
        parent[row.id] = row.parent ?? null;
        topic[row.id] = row.topic ?? null;
        subjects[row.id] = row.subject;
        postBodies[row.id] = row.body;
      }

      return ensureBoard({
        ...initBoardState(),
        registered,
        bound,
        owner,
        mailbox,
        subscribed,
        sender,
        origin,
        recipient,
        sentAt,
        mstatus: mstatus as BoardState["mstatus"],
        pstatus: pstatus as BoardState["pstatus"],
        author,
        porigin,
        parent,
        topic,
        posted,
        clock: Number(meta.get("clock") ?? 0),
        revision: Number(meta.get("revision") ?? 0),
        bodies,
        subjects,
        postBodies,
      });
    });
  }

  public write(state: BoardState): void {
    this.#transaction("IMMEDIATE", () => {
      for (const table of ["agents", "boxes", "messages", "posts", "subscriptions", "meta"]) {
        this.#db.exec(`DELETE FROM ${table}`);
      }
      const agent = this.#db.prepare("INSERT INTO agents (agent, registered) VALUES (?, ?)");
      for (const [id, registered] of Object.entries(state.registered)) agent.run(id, registered ? 1 : 0);

      const box = this.#db.prepare("INSERT INTO boxes (name, owner) VALUES (?, ?)");
      for (const [name, owner] of Object.entries(state.owner)) box.run(name, owner);

      const message = this.#db.prepare(
        "INSERT INTO messages (id, sender, origin, recipient, sent_at, status, body) VALUES (?, ?, ?, ?, ?, ?, ?)",
      );
      for (const [id, status] of Object.entries(state.mstatus)) {
        message.run(
          id,
          state.sender[id] ?? null,
          state.origin[id] ?? null,
          state.recipient[id] ?? null,
          state.sentAt[id] ?? 0,
          status,
          state.bodies[id] ?? "",
        );
      }

      const post = this.#db.prepare(
        "INSERT INTO posts (id, seq, author, origin, topic, parent, subject, body) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
      );
      state.posted.forEach((id, index) => {
        post.run(
          id,
          index + 1,
          state.author[id] ?? null,
          state.porigin[id] ?? null,
          state.topic[id] ?? null,
          state.parent[id] ?? null,
          state.subjects[id] ?? "",
          state.postBodies[id] ?? "",
        );
      });

      const subscription = this.#db.prepare("INSERT INTO subscriptions (agent, topic) VALUES (?, ?)");
      for (const [id, topics] of Object.entries(state.subscribed)) {
        for (const topic of topics) subscription.run(id, topic);
      }

      const meta = this.#db.prepare("INSERT INTO meta (key, value) VALUES (?, ?)");
      meta.run("revision", String(state.revision));
      meta.run("clock", String(state.clock));
    });
  }

  public lock<T>(operation: () => T): T {
    return this.#transaction("IMMEDIATE", operation);
  }

  #hasState(): boolean {
    return this.#db.prepare("SELECT 1 FROM meta LIMIT 1").get() !== undefined;
  }

  #transaction<T>(mode: "IMMEDIATE" | "DEFERRED", operation: () => T): T {
    if (this.#depth > 0) return operation();
    this.#db.exec(`BEGIN ${mode}`);
    this.#depth = 1;
    try {
      const value = operation();
      this.#depth = 0;
      this.#db.exec("COMMIT");
      return value;
    } catch (error) {
      this.#depth = 0;
      try {
        this.#db.exec("ROLLBACK");
      } catch {
        // The transaction may already have been rolled back by SQLite.
      }
      throw error;
    }
  }

  /** Close the connection (tests and shutdown). */
  public close(): void {
    this.#db.close();
  }
}
