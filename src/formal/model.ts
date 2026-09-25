/**
 * The executable abstract model of the message board (named-mailbox revision).
 *
 * Mailboxes are now named (`BoxId`), and an agent *binds* a name to serve it.
 * This decouples delivery from a session id: a fresh session can bind a name and
 * drain a mailbox a previous session left behind. A lease can be *reclaimed*
 * (the runtime triggers this on TTL expiry), so a fetched-but-unacked message is
 * never stranded when its consumer dies.
 *
 * Four machines:
 *
 *   RegistryMachine  registered        which agents may act
 *   BindingMachine   bound, owner      the exclusive agent<->mailbox binding
 *   MailboxMachine   mailbox, lease    per-name FIFO queue and its single lease
 *   MessageMachine   mstatus           absent -> queued -> fetched -> acked
 *   ForumMachine     posted, ...       append-only threaded log
 */

export type AgentId = string;
export type BoxId = string;
export type MessageId = string;
export type PostId = string;
export type MessageStatus = "absent" | "queued" | "fetched" | "acked";
export type PostStatus = "absent" | "posted";

/** The finite bounds the reference model is checked under. */
export interface BoardModelConfig {
  readonly agents: readonly AgentId[];
  readonly boxes: readonly BoxId[];
  readonly messages: readonly MessageId[];
  readonly posts: readonly PostId[];
  readonly topics: readonly string[];
  readonly mailboxCapacity: number;
}

/** The verification target: two agents, one named mailbox, two messages. */
export const BOARD_MODEL: BoardModelConfig = {
  agents: ["a1", "a2"],
  boxes: ["bx1"],
  messages: ["m1", "m2"],
  posts: ["p1", "p2"],
  topics: ["t1"],
  mailboxCapacity: 2,
};

/** The complete abstract state. */
export interface AbstractBoardState {
  readonly registered: Readonly<Record<AgentId, boolean>>;
  /** The name each agent currently serves, or null. */
  readonly bound: Readonly<Record<AgentId, BoxId | null>>;
  /** The exclusive serving agent of each name, or null. */
  readonly owner: Readonly<Record<BoxId, AgentId | null>>;
  readonly sender: Readonly<Record<MessageId, AgentId | null>>;
  readonly origin: Readonly<Record<MessageId, AgentId | null>>;
  readonly recipient: Readonly<Record<MessageId, BoxId | null>>;
  readonly sentAt: Readonly<Record<MessageId, number>>;
  readonly mstatus: Readonly<Record<MessageId, MessageStatus>>;
  readonly mailbox: Readonly<Record<BoxId, readonly MessageId[]>>;
  readonly lease: Readonly<Record<BoxId, MessageId | null>>;
  readonly pstatus: Readonly<Record<PostId, PostStatus>>;
  readonly author: Readonly<Record<PostId, AgentId | null>>;
  readonly porigin: Readonly<Record<PostId, AgentId | null>>;
  readonly parent: Readonly<Record<PostId, PostId | null>>;
  readonly topic: Readonly<Record<PostId, string | null>>;
  readonly posted: readonly PostId[];
  readonly clock: number;
}

/** The event alphabet. */
export type BoardEvent =
  | { readonly type: "register"; readonly agent: AgentId }
  | { readonly type: "bind"; readonly agent: AgentId; readonly box: BoxId }
  | { readonly type: "unbind"; readonly agent: AgentId }
  | { readonly type: "send"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "recv"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "ack"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "rollback"; readonly agent: AgentId; readonly box: BoxId }
  | { readonly type: "reclaim"; readonly box: BoxId }
  | { readonly type: "post"; readonly agent: AgentId; readonly post: PostId; readonly topic: string; readonly parent: PostId | null };

export type BoardAction = BoardEvent["type"];

/** Every action of the product machine, in specification order. */
export const BOARD_ACTIONS: readonly BoardAction[] = [
  "register",
  "bind",
  "unbind",
  "send",
  "recv",
  "ack",
  "rollback",
  "reclaim",
  "post",
];

/** Construct the initial state. */
export function initAbstractBoardState(config: BoardModelConfig): AbstractBoardState {
  const registered: Record<AgentId, boolean> = {};
  const bound: Record<AgentId, BoxId | null> = {};
  for (const agent of config.agents) {
    registered[agent] = false;
    bound[agent] = null;
  }
  const owner: Record<BoxId, AgentId | null> = {};
  const mailbox: Record<BoxId, MessageId[]> = {};
  const lease: Record<BoxId, MessageId | null> = {};
  for (const box of config.boxes) {
    owner[box] = null;
    mailbox[box] = [];
    lease[box] = null;
  }
  const sender: Record<MessageId, AgentId | null> = {};
  const origin: Record<MessageId, AgentId | null> = {};
  const recipient: Record<MessageId, BoxId | null> = {};
  const sentAt: Record<MessageId, number> = {};
  const mstatus: Record<MessageId, MessageStatus> = {};
  for (const message of config.messages) {
    sender[message] = null;
    origin[message] = null;
    recipient[message] = null;
    sentAt[message] = 0;
    mstatus[message] = "absent";
  }
  const pstatus: Record<PostId, PostStatus> = {};
  const author: Record<PostId, AgentId | null> = {};
  const porigin: Record<PostId, AgentId | null> = {};
  const parent: Record<PostId, PostId | null> = {};
  const topic: Record<PostId, string | null> = {};
  for (const post of config.posts) {
    pstatus[post] = "absent";
    author[post] = null;
    porigin[post] = null;
    parent[post] = null;
    topic[post] = null;
  }
  return {
    registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
    mailbox, lease, pstatus, author, porigin, parent, topic, posted: [], clock: 0,
  };
}

/** Why a model step was refused. */
export class BoardStateError extends Error {
  public constructor(
    public readonly code: string,
    message: string,
  ) {
    super(message);
    this.name = "BoardStateError";
  }
}

function set<K extends string, V>(record: Readonly<Record<K, V>>, key: K, value: V): Record<K, V> {
  return { ...record, [key]: value };
}

/** The guards, one per action. */
export const guards = {
  register: (state: AbstractBoardState, agent: AgentId): boolean => state.registered[agent] !== true,

  bind: (state: AbstractBoardState, agent: AgentId, box: BoxId): boolean =>
    state.registered[agent] === true &&
    (state.bound[agent] ?? null) === null &&
    (state.owner[box] ?? null) === null,

  unbind: (state: AbstractBoardState, agent: AgentId): boolean =>
    state.registered[agent] === true && (state.bound[agent] ?? null) !== null,

  send: (state: AbstractBoardState, config: BoardModelConfig, agent: AgentId, box: BoxId, message: MessageId): boolean =>
    state.registered[agent] === true &&
    (state.mstatus[message] ?? "absent") === "absent" &&
    (state.mailbox[box]?.length ?? 0) < config.mailboxCapacity,

  recv: (state: AbstractBoardState, agent: AgentId, box: BoxId, message: MessageId): boolean =>
    state.registered[agent] === true &&
    state.bound[agent] === box &&
    state.owner[box] === agent &&
    state.lease[box] === null &&
    (state.mailbox[box]?.length ?? 0) > 0 &&
    state.mailbox[box]![0] === message &&
    state.mstatus[message] === "queued",

  ack: (state: AbstractBoardState, agent: AgentId, box: BoxId, message: MessageId): boolean =>
    state.bound[agent] === box && state.owner[box] === agent && state.lease[box] === message && state.mstatus[message] === "fetched",

  rollback: (state: AbstractBoardState, agent: AgentId, box: BoxId): boolean =>
    state.bound[agent] === box && state.owner[box] === agent && state.lease[box] !== null,

  /** A lease may be revoked at any time; the runtime triggers this on TTL expiry. */
  reclaim: (state: AbstractBoardState, box: BoxId): boolean => state.lease[box] !== null,

  post: (
    state: AbstractBoardState,
    config: BoardModelConfig,
    agent: AgentId,
    post: PostId,
    topic: string,
    parent: PostId | null,
  ): boolean =>
    state.registered[agent] === true &&
    (state.pstatus[post] ?? "absent") === "absent" &&
    config.topics.includes(topic) &&
    (parent === null || (state.pstatus[parent] === "posted" && state.topic[parent] === topic)),
} as const;

/** Apply one event to the abstract model. */
export function referenceReduceBoardState(
  state: AbstractBoardState,
  event: BoardEvent,
  config: BoardModelConfig,
): AbstractBoardState {
  switch (event.type) {
    case "register":
      require(guards.register(state, event.agent), "register-not-enabled", event.agent);
      return {
        ...state,
        registered: set(state.registered, event.agent, true),
        bound: state.bound[event.agent] === undefined ? set(state.bound, event.agent, null) : state.bound,
      };
    case "bind": {
      require(guards.bind(state, event.agent, event.box), "bind-not-enabled", event.box);
      return {
        ...state,
        bound: set(state.bound, event.agent, event.box),
        owner: set(state.owner, event.box, event.agent),
        mailbox: state.mailbox[event.box] === undefined ? set(state.mailbox, event.box, []) : state.mailbox,
        lease: state.lease[event.box] === undefined ? set(state.lease, event.box, null) : state.lease,
      };
    }
    case "unbind": {
      require(guards.unbind(state, event.agent), "unbind-not-enabled", event.agent);
      const box = state.bound[event.agent]!;
      const lease = state.lease[box] ?? null;
      const requeued = lease === null ? state.mailbox[box]! : [lease, ...state.mailbox[box]!];
      return {
        ...state,
        bound: set(state.bound, event.agent, null),
        owner: set(state.owner, box, null),
        mailbox: set(state.mailbox, box, requeued),
        lease: set(state.lease, box, null),
        mstatus: lease === null ? state.mstatus : set(state.mstatus, lease, "queued"),
      };
    }
    case "send": {
      require(guards.send(state, config, event.agent, event.box, event.message), "send-not-enabled", event.message);
      const clock = state.clock + 1;
      return {
        ...state,
        clock,
        mstatus: set(state.mstatus, event.message, "queued"),
        sender: set(state.sender, event.message, event.agent),
        origin: set(state.origin, event.message, event.agent),
        recipient: set(state.recipient, event.message, event.box),
        sentAt: set(state.sentAt, event.message, clock),
        mailbox: set(state.mailbox, event.box, [...(state.mailbox[event.box] ?? []), event.message]),
      };
    }
    case "recv": {
      require(guards.recv(state, event.agent, event.box, event.message), "recv-not-enabled", event.message);
      return {
        ...state,
        mstatus: set(state.mstatus, event.message, "fetched"),
        mailbox: set(state.mailbox, event.box, state.mailbox[event.box]!.slice(1)),
        lease: set(state.lease, event.box, event.message),
      };
    }
    case "ack": {
      require(guards.ack(state, event.agent, event.box, event.message), "ack-not-enabled", event.message);
      return {
        ...state,
        mstatus: set(state.mstatus, event.message, "acked"),
        lease: set(state.lease, event.box, null),
      };
    }
    case "rollback": {
      require(guards.rollback(state, event.agent, event.box), "rollback-not-enabled", event.agent);
      const message = state.lease[event.box]!;
      return {
        ...state,
        mstatus: set(state.mstatus, message, "queued"),
        mailbox: set(state.mailbox, event.box, [message, ...(state.mailbox[event.box] ?? [])]),
        lease: set(state.lease, event.box, null),
      };
    }
    case "reclaim": {
      require(guards.reclaim(state, event.box), "reclaim-not-enabled", event.box);
      const message = state.lease[event.box]!;
      return {
        ...state,
        mstatus: set(state.mstatus, message, "queued"),
        mailbox: set(state.mailbox, event.box, [message, ...(state.mailbox[event.box] ?? [])]),
        lease: set(state.lease, event.box, null),
      };
    }
    case "post": {
      require(
        guards.post(state, config, event.agent, event.post, event.topic, event.parent),
        "post-not-enabled",
        event.post,
      );
      return {
        ...state,
        posted: [...state.posted, event.post],
        pstatus: set(state.pstatus, event.post, "posted"),
        author: set(state.author, event.post, event.agent),
        porigin: set(state.porigin, event.post, event.agent),
        parent: set(state.parent, event.post, event.parent),
        topic: set(state.topic, event.post, event.topic),
      };
    }
  }
}

function require(condition: boolean, code: string, subject: string): asserts condition {
  if (!condition) throw new BoardStateError(code, `event not enabled: ${code} (${subject})`);
}

/** Enumerate every event enabled in a state. */
export function enabledEvents(state: AbstractBoardState, config: BoardModelConfig): BoardEvent[] {
  const events: BoardEvent[] = [];
  for (const agent of config.agents) {
    if (guards.register(state, agent)) events.push({ type: "register", agent });
    if (guards.unbind(state, agent)) events.push({ type: "unbind", agent });
    for (const box of config.boxes) {
      if (guards.bind(state, agent, box)) events.push({ type: "bind", agent, box });
      if (guards.rollback(state, agent, box)) events.push({ type: "rollback", agent, box });
      for (const message of config.messages) {
        if (guards.recv(state, agent, box, message)) events.push({ type: "recv", agent, box, message });
        if (guards.ack(state, agent, box, message)) events.push({ type: "ack", agent, box, message });
        if (guards.send(state, config, agent, box, message)) events.push({ type: "send", agent, box, message });
      }
    }
    for (const post of config.posts) {
      for (const topic of config.topics) {
        if (guards.post(state, config, agent, post, topic, null)) {
          events.push({ type: "post", agent, post, topic, parent: null });
        }
        for (const parent of config.posts) {
          if (guards.post(state, config, agent, post, topic, parent)) {
            events.push({ type: "post", agent, post, topic, parent });
          }
        }
      }
    }
  }
  for (const box of config.boxes) {
    if (guards.reclaim(state, box)) events.push({ type: "reclaim", box });
  }
  return events;
}

/** A single invariant failure. */
export interface BoardViolation {
  readonly invariant: string;
  readonly detail: string;
}

/** Check every safety invariant of the abstract board. */
export function boardInvariantViolations(state: AbstractBoardState, config: BoardModelConfig): BoardViolation[] {
  const out: BoardViolation[] = [];
  const push = (invariant: string, detail: string): void => {
    out.push({ invariant, detail });
  };

  // Binding exclusivity: bound and owner are inverse maps.
  for (const agent of config.agents) {
    const box = state.bound[agent] ?? null;
    if (box !== null) {
      if (state.owner[box] !== agent) push("BindExclusive", `${agent} bound to ${box} but owner is ${state.owner[box]}`);
    }
  }
  for (const box of config.boxes) {
    const owner = state.owner[box] ?? null;
    if (owner !== null) {
      if (state.bound[owner] !== box) push("BindExclusive", `${box} owned by ${owner} but bound is ${state.bound[owner]}`);
      if (state.registered[owner] !== true) push("OwnerRegistered", `${box} owned by unregistered ${owner}`);
    }
  }

  // Placement: every message is in exactly one place, or acked.
  const placements = new Map<MessageId, string[]>();
  for (const message of config.messages) placements.set(message, []);
  for (const box of config.boxes) {
    const queue = state.mailbox[box] ?? [];
    if (queue.length > config.mailboxCapacity) push("Bounded", `${box} mailbox ${queue.length} > capacity`);
    for (const message of queue) placements.get(message)?.push(`mailbox:${box}`);
    const lease = state.lease[box] ?? null;
    if (lease != null) placements.get(lease)?.push(`lease:${box}`);
  }
  for (const message of config.messages) {
    const status = state.mstatus[message] ?? "absent";
    const places = placements.get(message) ?? [];
    if (status === "absent" && places.length !== 0) push("Placement", `${message} absent but placed`);
    if (status === "queued" && places.length !== 1) push("Placement", `${message} queued in ${places.length} places`);
    if (status === "fetched" && places.length !== 1) push("Placement", `${message} fetched in ${places.length} places`);
    if (status === "acked" && places.length !== 0) push("Placement", `${message} acked but placed`);
    if (status === "fetched") {
      const owner = config.boxes.find((box) => (state.lease[box] ?? null) === message);
      if (owner === undefined || state.recipient[message] !== owner) {
        push("LeaseRecipient", `${message} leased by a non-recipient`);
      }
    }
    if (status !== "absent" && state.sender[message] !== state.origin[message]) {
      push("Unforgeable", `${message} sender ${state.sender[message]} != origin ${state.origin[message]}`);
    }
    for (const box of config.boxes) {
      const q = state.mailbox[box] ?? [];
      for (let i = 0; i + 1 < q.length; i += 1) {
        if ((state.sentAt[q[i]!] ?? 0) > (state.sentAt[q[i + 1]!] ?? 0)) {
          push("Fifo", `${box} mailbox out of send order`);
        }
      }
    }
  }

  // Forum invariants.
  const seen = new Set<PostId>();
  state.posted.forEach((post, index) => {
    if (seen.has(post)) push("BoardNoDuplicates", `post ${post} appears twice`);
    seen.add(post);
    if (state.pstatus[post] !== "posted") push("BoardAppendOnly", `${post} in log but not posted`);
    const parent = state.parent[post] ?? null;
    if (parent != null) {
      if (state.pstatus[parent] !== "posted") push("ParentPosted", `${post} parent ${parent} not posted`);
      else if (state.posted.indexOf(parent) >= index) push("ParentPosted", `${post} parent ${parent} is later`);
      if (state.topic[parent] !== state.topic[post]) push("ParentTopic", `${post} parent in another topic`);
    }
    if (state.author[post] !== state.porigin[post]) {
      push("Unforgeable", `post ${post} author ${state.author[post]} != origin ${state.porigin[post]}`);
    }
  });
  for (const post of config.posts) {
    if (state.pstatus[post] === "posted" && !seen.has(post)) push("BoardAppendOnly", `${post} posted but not in log`);
  }
  return out;
}

/** Names of every invariant checked above. */
export const BOARD_INVARIANT_NAMES: readonly string[] = [
  "BindExclusive",
  "OwnerRegistered",
  "Bounded",
  "Placement",
  "LeaseRecipient",
  "Unforgeable",
  "Fifo",
  "BoardNoDuplicates",
  "BoardAppendOnly",
  "ParentPosted",
  "ParentTopic",
];
