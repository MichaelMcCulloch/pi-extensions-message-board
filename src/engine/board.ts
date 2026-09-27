/**
 * Durable board state (push revision).
 *
 * Mailboxes are keyed by a durable name, and an agent binds a name to serve it.
 * Production state extends the verified abstract state with payloads and a
 * revision; `boardConfigOf` derives the live key sets for the invariant checker.
 */

import {
  boardInvariantViolations,
  initAbstractBoardState,
  type AbstractBoardState,
  type AgentId,
  type BoardModelConfig,
  type BoardViolation,
  type BoxId,
  type MessageId,
  type PostId,
  type TopicId,
} from "../formal/model.ts";

/** Capacity of a named mailbox. */
export const MAILBOX_CAPACITY = 32;

/** Production state: the abstract product plus payloads and a revision. */
export interface BoardState extends AbstractBoardState {
  readonly revision: number;
  readonly bodies: Readonly<Record<MessageId, string>>;
  readonly subjects: Readonly<Record<PostId, string>>;
  readonly postBodies: Readonly<Record<PostId, string>>;
}

/** A fresh, empty board. Agents, boxes, messages, and posts appear as used. */
export function initBoardState(): BoardState {
  const empty: BoardModelConfig = {
    agents: [],
    boxes: [],
    messages: [],
    posts: [],
    topics: [],
    mailboxCapacity: MAILBOX_CAPACITY,
  };
  return {
    ...initAbstractBoardState(empty),
    revision: 0,
    bodies: {},
    subjects: {},
    postBodies: {},
  };
}

/**
 * Project durable state onto the verified abstract vocabulary. The production
 * state extends the abstract state, so the projection is the state itself; the
 * payload fields (bodies, subjects, revision) are not part of the model.
 */
export function abstractBoardState(state: BoardState): AbstractBoardState {
  return state;
}

export function boardConfigOf(state: BoardState, extra?: { box?: BoxId; topic?: TopicId }): BoardModelConfig {
  const boxes = new Set<BoxId>([...Object.keys(state.owner), ...Object.keys(state.mailbox)]);
  if (extra?.box !== undefined) boxes.add(extra.box);
  const topics = new Set<TopicId>();
  for (const post of Object.keys(state.topic)) {
    const value = state.topic[post];
    if (value != null) topics.add(value);
  }
  for (const agent of Object.keys(state.subscribed)) {
    for (const topic of state.subscribed[agent] ?? []) topics.add(topic);
  }
  if (extra?.topic !== undefined) topics.add(extra.topic);
  return {
    agents: Object.keys(state.registered),
    boxes: [...boxes],
    messages: Object.keys(state.mstatus),
    posts: Object.keys(state.pstatus),
    topics: [...topics],
    mailboxCapacity: MAILBOX_CAPACITY,
    // The live instance admits fresh message IDs; use a clock bound independent of its current size.
    maxClock: Number.MAX_SAFE_INTEGER,
  };
}

/** The invariant failures in a live board. */
export function boardViolations(state: BoardState): BoardViolation[] {
  return boardInvariantViolations(state, boardConfigOf(state));
}

/** A read-only projection of the board. */
export interface BoardProjection {
  readonly revision: number;
  readonly agents: readonly {
    readonly id: AgentId;
    readonly box: BoxId | null;
    readonly subscribed: readonly TopicId[];
  }[];
  readonly boxes: readonly {
    readonly name: BoxId;
    readonly owner: AgentId | null;
    readonly queued: number;
    readonly delivered: number;
    readonly failed: number;
  }[];
  readonly messages: readonly {
    readonly id: MessageId;
    readonly status: string;
    readonly from: AgentId | null;
    readonly to: BoxId | null;
  }[];
  readonly posts: readonly {
    readonly id: PostId;
    readonly topic: TopicId;
    readonly parent: PostId | null;
    readonly author: AgentId | null;
    readonly subject: string;
  }[];
}

/** Derive the board projection. */
export function projectBoard(state: BoardState): BoardProjection {
  const boxes = [...new Set([...Object.keys(state.owner), ...Object.keys(state.mailbox)])];
  return {
    revision: state.revision,
    agents: Object.keys(state.registered).map((id) => ({
      id,
      box: state.bound[id] ?? null,
      subscribed: state.subscribed[id] ?? [],
    })),
    boxes: boxes.map((name) => {
      const messages = Object.keys(state.mstatus).filter((id) => state.recipient[id] === name);
      return {
        name,
        owner: state.owner[name] ?? null,
        queued: state.mailbox[name]?.length ?? 0,
        delivered: messages.filter((id) => state.mstatus[id] === "delivered").length,
        failed: messages.filter((id) => state.mstatus[id] === "failed").length,
      };
    }),
    messages: Object.keys(state.mstatus).map((id) => ({
      id,
      status: state.mstatus[id]!,
      from: state.sender[id] ?? null,
      to: state.recipient[id] ?? null,
    })),
    posts: state.posted.map((id) => ({
      id,
      topic: state.topic[id] ?? "",
      parent: state.parent[id] ?? null,
      author: state.author[id] ?? null,
      subject: state.subjects[id] ?? "",
    })),
  };
}
