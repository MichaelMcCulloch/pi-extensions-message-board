/**
 * The board store (named-mailbox revision).
 *
 * Mutations run under the backend lock as read-modify-write against the durable
 * board. Read operations refresh first, so a process sees other processes'
 * writes. Mailboxes are named: an agent binds a name to serve it, and a name
 * that stays unbound is a durable inbox that a later session can drain.
 */

import { randomUUID } from "node:crypto";
import { boardViolations, projectBoard, type BoardProjection, type BoardState } from "../engine/board.ts";
import { isEnabled, reduceBoardCommand, type BoardCommand } from "../engine/reducer.ts";
import { BoardStateError } from "../formal/model.ts";
import type { BoardBackend } from "./persistence.ts";
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

/** One queued message as seen without fetching it. */
export interface InboxEntry {
  readonly id: string;
  readonly from: string | null;
  readonly preview: string;
}

/** A fetched message with its body. */
export interface FetchedMessage {
  readonly id: string;
  readonly from: string | null;
  readonly body: string;
}

/** The board store. */
export class BoardStore {
  readonly #backend: BoardBackend;
  #state: BoardState;

  public constructor(backend: BoardBackend) {
    this.#backend = backend;
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

  /** Release the served name, returning any fetched message to its queue. */
  public unbind(agent: string): BoardState {
    this.refresh();
    return this.#apply({ type: "unbind", agent });
  }

  /** Enqueue a direct message to a named mailbox; the sender is the actor. */
  public send(agent: string, box: string, body: string, explicitId?: string): { message: string; state: BoardState } {
    this.refresh();
    this.#requireRegistered(agent);
    const message = explicitId ?? `m-${randomUUID().slice(0, 8)}`;
    const result = this.#apply({ type: "send", agent, box, message, body });
    return { message, state: result };
  }

  /** Fetch the head of a named mailbox, without acking it. */
  public recv(agent: string, box?: string): { state: BoardState; message: FetchedMessage | null; reason?: string } {
    this.refresh();
    const name = this.#resolveBox(agent, box);
    const queue = this.#state.mailbox[name] ?? [];
    if (queue.length === 0) return { state: this.#state, message: null, reason: "mailbox-empty" };
    const message = queue[0]!;
    const state = this.#apply({ type: "recv", agent, box: name, message });
    return {
      state,
      message: {
        id: message,
        from: this.#state.sender[message] ?? null,
        body: this.#state.bodies[message] ?? "",
      },
    };
  }

  /** Acknowledge a fetched message: the POP3 commit. */
  public ack(agent: string, box: string, message: string): BoardState {
    this.refresh();
    return this.#apply({ type: "ack", agent, box, message });
  }

  /** Acknowledge every message the caller has fetched from its bound mailbox. */
  public ackAll(agent: string): BoardState {
    this.refresh();
    const name = this.#resolveBox(agent);
    const message = this.#state.lease[name] ?? null;
    if (message !== null && isEnabled(this.#state, { type: "ack", agent, box: name, message })) {
      this.#apply({ type: "ack", agent, box: name, message });
    }
    return this.#state;
  }

  /** Abandon the fetch without acking; the head returns to the queue. */
  public rollback(agent: string, box: string): BoardState {
    this.refresh();
    return this.#apply({ type: "rollback", agent, box });
  }

  /** Revoke a lease (the runtime trigger for TTL expiry). */
  public reclaim(box: string): BoardState {
    this.refresh();
    return this.#apply({ type: "reclaim", box });
  }

  /** List queued messages of a named mailbox without fetching them. */
  public inbox(box: string): InboxEntry[] {
    this.refresh();
    return (this.#state.mailbox[box] ?? []).map((id) => ({
      id,
      from: this.#state.sender[id] ?? null,
      preview: (this.#state.bodies[id] ?? "").slice(0, 120),
    }));
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

  #resolveBox(agent: string, box?: string): string {
    if (box !== undefined && box.length > 0) return box;
    const bound = this.#state.bound[agent] ?? null;
    if (bound === null) {
      throw new BoardOperationError("board-unbound", `${agent} serves no mailbox; bind one or pass box`);
    }
    return bound;
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
