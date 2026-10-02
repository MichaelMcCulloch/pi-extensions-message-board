/**
 * The board store (push revision).
 *
 * Mutations run on the backend as read-modify-write against the durable board.
 * Read operations refresh first, so a process sees other processes' writes.
 * Mailboxes are named: an agent binds a name to serve it, and a name that stays
 * unbound is a durable inbox that a later session can drain. Delivery and
 * failure are applied by the runtime when it injects, or gives up on, a
 * message; there is no agent-facing fetch/ack handshake.
 */

import { randomUUID } from "node:crypto";
import { boardViolations, projectBoard, type BoardProjection, type BoardState } from "../engine/board.ts";
import { reduceBoardCommand, type BoardCommand } from "../engine/reducer.ts";
import { BoardStateError } from "../formal/model.ts";
import type { BoardBackend, DeliveryLedger } from "./persistence.ts";
import { ensureBoard, MemoryBoardBackend } from "./persistence.ts";

/** A store error carrying a stable code. */
export class BoardOperationError extends Error {
  public constructor(
    public readonly code: string,
    message: string,
  ) {
    super(message);
    this.name = "BoardOperationError";
  }
}

/** One queued message as seen without delivering it. */
export interface InboxEntry {
  readonly id: string;
  readonly from: string | null;
  readonly preview: string;
}

/** One message the local runtime should inject next. */
export interface PendingDelivery {
  readonly box: string;
  readonly id: string;
  readonly from: string | null;
  readonly body: string;
}

/** The board store. */
export class BoardStore {
  readonly #backend: BoardBackend;
  readonly #ledger: DeliveryLedger;
  #state: BoardState;

  public constructor(backend: BoardBackend) {
    this.#backend = backend;
    this.#ledger = backend.ledger;
    this.#state = ensureBoard(backend.read());
  }

  /** The current in-memory view (refreshed on every read and mutation). */
  public get state(): BoardState {
    return this.#state;
  }

  /** Re-read the durable board. */
  public refresh(): BoardState {
    this.#state = ensureBoard(this.#backend.read());
    return this.#state;
  }

  /** The read-only projection. */
  public get projection(): BoardProjection {
    this.refresh();
    return projectBoard(this.#state);
  }

  /** Invariant failures in the current state. */
  public violations(): readonly { invariant: string; detail: string }[] {
    return boardViolations(this.#state);
  }

  /** Register the calling agent. Idempotent. */
  public register(agent: string): BoardState {
    this.refresh();
    if (this.#state.registered[agent] === true) return this.#state;
    return this.#apply({ type: "register", agent });
  }

  /** Bind a name to serve. A name may have at most one serving agent. */
  public bind(agent: string, box: string): BoardState {
    this.refresh();
    return this.#apply({ type: "bind", agent, box });
  }

  /** Release the served name; its queued messages wait for a new owner. */
  public unbind(agent: string): BoardState {
    this.refresh();
    return this.#apply({ type: "unbind", agent });
  }

  /** Enqueue a direct message to a named mailbox; the sender is the actor. */
  public send(
    agent: string,
    box: string,
    body: string,
    explicitId?: string,
    ttlMs?: number,
  ): { message: string; state: BoardState } {
    this.refresh();
    this.#requireRegistered(agent);
    const message = explicitId ?? `m-${randomUUID().slice(0, 8)}`;
    const result = this.#apply({ type: "send", agent, box, message, body });
    const now = Date.now();
    this.#ledger.record(message, now, ttlMs === undefined ? null : now + ttlMs);
    return { message, state: result };
  }

  /**
   * Mark a message delivered. The runtime calls this **after** it has injected
   * the message into the agent's context: a crash in between leaves the message
   * queued, so it is redelivered (duplicates are possible, loss is not).
   */
  public deliver(agent: string, box: string, message: string): BoardState {
    this.refresh();
    return this.#apply({ type: "deliver", agent, box, message });
  }

  /** Mark a message failed (expiry or injection error) and report the reason. */
  public fail(box: string, message: string, reason = "failed"): BoardState {
    this.refresh();
    const state = this.#apply({ type: "fail", box, message });
    this.#ledger.setReason(message, reason);
    return state;
  }

  /**
   * Fail every queued message whose deadline has passed. Called by the runtime
   * janitor; the ledger owns the clock, the model owns the transition.
   */
  public expire(now = Date.now()): readonly string[] {
    const expired: string[] = [];
    for (const message of this.#ledger.due(now)) {
      this.refresh();
      if (this.#state.mstatus[message] !== "queued") continue;
      const box = this.#state.recipient[message];
      if (typeof box !== "string") continue;
      this.#apply({ type: "fail", box, message });
      this.#ledger.setReason(message, "expired");
      expired.push(message);
    }
    return expired;
  }

  /** Failures this agent sent that have not yet been reported to it. */
  public outboundFailures(agent: string): readonly { id: string; box: string | null; reason: string | null }[] {
    this.refresh();
    const out: { id: string; box: string | null; reason: string | null }[] = [];
    for (const [id, status] of Object.entries(this.#state.mstatus)) {
      if (status !== "failed" || this.#state.sender[id] !== agent) continue;
      if (this.#ledger.notifiedAt(id) !== null) continue;
      out.push({ id, box: this.#state.recipient[id] ?? null, reason: this.#ledger.reason(id) });
    }
    return out;
  }

  /** Record that the sender has been told about a failure. */
  public markFailureNotified(message: string): void {
    this.#ledger.markNotified(message, Date.now());
  }

  /** Watch a topic; posting in a topic subscribes the author automatically. */
  public subscribe(agent: string, topic: string): BoardState {
    this.refresh();
    if (topic.trim().length === 0) throw new BoardOperationError("board-empty-topic", "topic is required");
    return this.#apply({ type: "subscribe", agent, topic });
  }

  /** Stop watching a topic. */
  public unsubscribe(agent: string, topic: string): BoardState {
    this.refresh();
    return this.#apply({ type: "unsubscribe", agent, topic });
  }

  /** List queued messages of a named mailbox without delivering them. */
  public inbox(box: string): InboxEntry[] {
    this.refresh();
    return (this.#state.mailbox[box] ?? []).map((id) => ({
      id,
      from: this.#state.sender[id] ?? null,
      preview: (this.#state.bodies[id] ?? "").slice(0, 120),
    }));
  }

  /** The heads of every mailbox this agent serves, ready to inject. */
  public pending(agent: string): PendingDelivery[] {
    this.refresh();
    const out: PendingDelivery[] = [];
    for (const [box, queue] of Object.entries(this.#state.mailbox)) {
      if (this.#state.owner[box] !== agent) continue;
      const id = queue[0];
      if (id === undefined) continue;
      out.push({ box, id, from: this.#state.sender[id] ?? null, body: this.#state.bodies[id] ?? "" });
    }
    return out;
  }

  /** How many posts the log holds; the high-water mark for push notification. */
  public postCount(): number {
    this.refresh();
    return this.#state.posted.length;
  }

  /** Posts after a log position, in append order, with their 1-based seq. */
  public postsAfter(seq: number): readonly {
    readonly id: string;
    readonly seq: number;
    readonly topic: string;
    readonly author: string | null;
    readonly subject: string;
    readonly body: string;
  }[] {
    this.refresh();
    return this.#state.posted.slice(seq).map((id, index) => ({
      id,
      seq: seq + index + 1,
      topic: this.#state.topic[id] ?? "",
      author: this.#state.author[id] ?? null,
      subject: this.#state.subjects[id] ?? "",
      body: this.#state.postBodies[id] ?? "",
    }));
  }

  /** The topics an agent watches. */
  public subscriptions(agent: string): readonly string[] {
    this.refresh();
    return this.#state.subscribed[agent] ?? [];
  }

  /** Append a post to the forum. */
  public post(
    agent: string,
    topic: string,
    subject: string,
    body: string,
    parent: string | null = null,
    explicitId?: string,
  ): { post: string; state: BoardState } {
    this.refresh();
    this.#requireRegistered(agent);
    if (topic.trim().length === 0) throw new BoardOperationError("board-empty-topic", "topic is required");
    const post = explicitId ?? `p-${randomUUID().slice(0, 8)}`;
    const state = this.#apply({ type: "post", agent, post, topic, subject, body, parent });
    return { post, state };
  }

  /** Atomic idempotent publication. A reused key with different content is refused. */
  public postOnce(agent: string, topic: string, subject: string, body: string, id: string): { post: string; state: BoardState } {
    return this.#backend.lock(() => {
      this.refresh();
      if (this.#state.pstatus[id] === "posted") {
        if (this.#state.author[id] !== agent || this.#state.topic[id] !== topic || this.#state.subjects[id] !== subject
          || this.#state.postBodies[id] !== body || this.#state.parent[id] !== null)
          throw new BoardOperationError("board-idempotency-conflict", "publication key already has different content");
        return {post:id,state:this.#state};
      }
      return this.post(agent,topic,subject,body,null,id);
    });
  }

  /** Read a topic, optionally only posts after a known post id. */
  public read(topic: string, since: string | null = null): readonly {
    id: string;
    parent: string | null;
    author: string | null;
    subject: string;
    body: string;
  }[] {
    this.refresh();
    const all = this.#state.posted.filter((post) => this.#state.topic[post] === topic);
    const start = since === null ? 0 : all.indexOf(since) + 1;
    return all.slice(start < 0 ? all.length : start).map((id) => ({
      id,
      parent: this.#state.parent[id] ?? null,
      author: this.#state.author[id] ?? null,
      subject: this.#state.subjects[id] ?? "",
      body: this.#state.postBodies[id] ?? "",
    }));
  }

  /** The distinct topics with a post count. */
  public topics(): { topic: string; posts: number }[] {
    this.refresh();
    const counts = new Map<string, number>();
    for (const post of this.#state.posted) {
      const topic = this.#state.topic[post];
      if (typeof topic === "string") counts.set(topic, (counts.get(topic) ?? 0) + 1);
    }
    return [...counts].map(([topic, posts]) => ({ topic, posts })).sort((a, b) => a.topic.localeCompare(b.topic));
  }

  /** The name the caller currently serves, if any. */
  public boundBox(agent: string): string | null {
    this.refresh();
    return this.#state.bound[agent] ?? null;
  }

  #requireRegistered(agent: string): void {
    if (this.#state.registered[agent] !== true) {
      throw new BoardOperationError("board-unregistered", `${agent} is not registered`);
    }
  }

  #apply(command: BoardCommand): BoardState {
    this.refresh();
    try {
      return this.#backend.lock(() => {
        const current = ensureBoard(this.#backend.read());
        const result = reduceBoardCommand(current, command);
        const violations = boardViolations(result.state);
        if (violations.length > 0) {
          throw new BoardOperationError(
            "board-invariant-violation",
            violations.map((violation) => `${violation.invariant}: ${violation.detail}`).join("; "),
          );
        }
        this.#backend.write(result.state);
        this.#state = result.state;
        return result.state;
      });
    } catch (error) {
      if (error instanceof BoardStateError) {
        throw new BoardOperationError("board-transition-refused", error.message);
      }
      throw error;
    }
  }
}

/** A fresh store over an in-memory backend, for tests and single-process use. */
export function memoryBoard(initial: BoardState | null = null): BoardStore {
  return new BoardStore(new MemoryBoardBackend(initial));
}
