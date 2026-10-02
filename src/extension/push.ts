/**
 * The push watcher.
 *
 * One loop per process turns durable board state into in-process notifications:
 *
 * - a direct message whose mailbox this session serves is injected into the
 *   agent's context and only then marked delivered, so a crash between the two
 *   duplicates rather than loses;
 * - a forum post in a topic this session subscribes to, by someone else, is
 *   coalesced per topic and injected;
 * - a queued message past its deadline is failed, and the sender is told about
 *   every failure it has not yet been told about.
 *
 * The watcher never mutates state except through `BoardStore`, which applies
 * the verified transition relation. Bus emissions are post-commit and advisory.
 */

import { BOARD_CHANGED, BOARD_DELIVERED, BOARD_FAILED, BOARD_POST } from "./bus.ts";
import { BoardOperationError, type BoardStore } from "./store.ts";

/** One notification handed to the runtime for injection. */
export interface BoardNotification {
  readonly kind: "dm" | "post" | "failure";
  readonly text: string;
  readonly details: Record<string, unknown>;
}

/** What the pusher needs from the host runtime. */
export interface PushDeps {
  readonly store: BoardStore;
  /** The session's agent identity. */
  readonly agent: string;
  /** Inject into the agent's context (`pi.sendMessage`). */
  readonly notify: (notification: BoardNotification) => void;
  /** Emit a post-commit observation (`pi.events.emit`). */
  readonly emit: (channel: string, data: unknown) => void;
  /** Injectable clock for tests. */
  readonly now?: () => number;
}

function errorText(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

/** The per-process delivery loop. */
export class BoardPusher {
  readonly #deps: PushDeps;
  #lastRevision: number;
  #lastPostSeq: number;

  public constructor(deps: PushDeps) {
    this.#deps = deps;
    // Start from the current log: missed activity is read, not replayed.
    this.#lastRevision = deps.store.refresh().revision;
    this.#lastPostSeq = deps.store.postCount();
  }

  /** One poll iteration. */
  public tick(): void {
    this.#observe();
    this.#deliverDirect();
    this.#notifyForum();
    this.#failExpired();
    this.#reportFailures();
  }

  /** A local tool call committed a transition: announce it as local. */
  public notifyLocal(): void {
    const revision = this.#deps.store.refresh().revision;
    if (revision === this.#lastRevision) return;
    this.#lastRevision = revision;
    this.#deps.emit(BOARD_CHANGED, { revision, origin: "local" });
  }

  #observe(): void {
    const state = this.#deps.store.refresh();
    if (state.revision === this.#lastRevision) return;
    this.#lastRevision = state.revision;
    this.#deps.emit(BOARD_CHANGED, { revision: state.revision, origin: "observed" });
  }

  #deliverDirect(): void {
    for (const pending of this.#deps.store.pending(this.#deps.agent)) {
      try {
        const sender = pending.from === null ? "unknown" : pending.fromBox === null ? pending.from : `${pending.fromBox} (${pending.from})`;
        this.#deps.notify({
          kind: "dm",
          text: `[board] direct message ${pending.id} from ${sender} (box ${pending.box})\n${pending.body}`,
          details: { box: pending.box, message: pending.id, from: pending.from, fromBox: pending.fromBox },
        });
      } catch (error) {
        // The message can never reach the agent's context, so fail it now and
        // let the sender be told rather than retrying a poison message forever.
        const state = this.#deps.store.fail(pending.box, pending.id, `injection-failed: ${errorText(error)}`);
        // Our own commit is announced by board:failed; advancing the revision
        // keeps the next tick from re-announcing it as an observed change.
        this.#lastRevision = state.revision;
        this.#deps.emit(BOARD_FAILED, { box: pending.box, message: pending.id, reason: "injection-failed" });
        continue;
      }
      try {
        // Inject first, mark second: a crash in between leaves the message
        // queued and it is delivered again.
        const state = this.#deps.store.deliver(this.#deps.agent, pending.box, pending.id);
        this.#lastRevision = state.revision;
        this.#deps.emit(BOARD_DELIVERED, { box: pending.box, message: pending.id, from: pending.from });
      } catch (error) {
        if (!(error instanceof BoardOperationError)) throw error;
        // Someone else settled the message between the read and the mark; the
        // injected copy is an at-least-once duplicate.
      }
    }
  }

  #notifyForum(): void {
    const posts = this.#deps.store.postsAfter(this.#lastPostSeq);
    if (posts.length === 0) return;
    const subscribed = new Set(this.#deps.store.subscriptions(this.#deps.agent));
    const byTopic = new Map<string, { id: string; author: string | null; subject: string; body: string }[]>();
    for (const post of posts) {
      this.#lastPostSeq = Math.max(this.#lastPostSeq, post.seq);
      this.#deps.emit(BOARD_POST, { topic: post.topic, post: post.id, author: post.author });
      if (post.author === this.#deps.agent) continue;
      if (!subscribed.has(post.topic)) continue;
      const bucket = byTopic.get(post.topic) ?? [];
      bucket.push({ id: post.id, author: post.author, subject: post.subject, body: post.body });
      byTopic.set(post.topic, bucket);
    }
    for (const [topic, bucket] of byTopic) {
      const lines = bucket.map((post) => `- ${post.author ?? "unknown"}: ${post.subject} — ${post.body}`);
      this.#deps.notify({
        kind: "post",
        text: `[board] #${topic}: ${bucket.length} new post${bucket.length === 1 ? "" : "s"}\n${lines.join("\n")}`,
        details: { topic, posts: bucket.map((post) => post.id) },
      });
    }
  }

  #failExpired(): void {
    const now = (this.#deps.now ?? Date.now)();
    const expired = this.#deps.store.expire(now);
    if (expired.length > 0) this.#lastRevision = this.#deps.store.state.revision;
    for (const message of expired) {
      this.#deps.emit(BOARD_FAILED, { box: null, message, reason: "expired" });
    }
  }

  #reportFailures(): void {
    for (const failure of this.#deps.store.outboundFailures(this.#deps.agent)) {
      this.#deps.notify({
        kind: "failure",
        text: `[board] delivery of ${failure.id} to ${failure.box ?? "?"} failed: ${failure.reason ?? "unknown"}`,
        details: { box: failure.box, message: failure.id, reason: failure.reason },
      });
      this.#deps.store.markFailureNotified(failure.id);
      this.#deps.emit(BOARD_FAILED, { box: failure.box, message: failure.id, reason: failure.reason });
    }
  }
}
