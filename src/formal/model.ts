/**
 * The executable abstract model of the message board (push revision).
 *
 * A message is queued and then either delivered or failed; both terminal
 * states are absorbing. There is no lease and no ack: the runtime that injects
 * a message commits the delivery, and failures (expiry, injection error) are
 * reported to the sender. Mailboxes are named, an agent binds a name to serve
 * it, and posting in a topic subscribes the author to that topic.
 *
 * Six machines:
 *
 *   RegistryMachine       registered          which agents may act
 *   BindingMachine        bound, owner        the exclusive agent<->name binding
 *   MailboxMachine        mailbox             per-name FIFO queue
 *   MessageMachine        mstatus             absent -> queued -> delivered | failed
 *   SubscriptionMachine   subscribed          topic watch list, auto on post
 *   ForumMachine          posted, ...         append-only threaded log
 *
 * An environment action (`fail`) has no acting agent: the runtime triggers it
 * on expiry or when injection throws, exactly as the previous revision's
 * `reclaim` was triggered outside the model.
 */

export type AgentId = string;
export type BoxId = string;
export type MessageId = string;
export type PostId = string;
export type TopicId = string;
export type MessageStatus = "absent" | "queued" | "delivered" | "failed";
export type PostStatus = "absent" | "posted";

/** The finite bounds the reference model is checked under. */
export interface BoardModelConfig {
  readonly agents: readonly AgentId[];
  readonly boxes: readonly BoxId[];
  readonly messages: readonly MessageId[];
  readonly posts: readonly PostId[];
  readonly topics: readonly TopicId[];
  readonly mailboxCapacity: number;
  /** TLA+ MaxClock; by default every configured message can be sent once. */
  readonly maxClock?: number;
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
  /** Undelivered messages, in send order. Delivered and failed are terminal. */
  readonly mailbox: Readonly<Record<BoxId, readonly MessageId[]>>;
  /** Topics each agent watches; posting in a topic subscribes the author. */
  readonly subscribed: Readonly<Record<AgentId, readonly TopicId[]>>;
  readonly pstatus: Readonly<Record<PostId, PostStatus>>;
  readonly author: Readonly<Record<PostId, AgentId | null>>;
  readonly porigin: Readonly<Record<PostId, AgentId | null>>;
  readonly parent: Readonly<Record<PostId, PostId | null>>;
  readonly topic: Readonly<Record<PostId, TopicId | null>>;
  readonly posted: readonly PostId[];
  readonly clock: number;
}

/** The event alphabet. */
export type BoardEvent =
  | { readonly type: "register"; readonly agent: AgentId }
  | { readonly type: "bind"; readonly agent: AgentId; readonly box: BoxId }
  | { readonly type: "unbind"; readonly agent: AgentId }
  | { readonly type: "send"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "deliver"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "fail"; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "subscribe"; readonly agent: AgentId; readonly topic: TopicId }
  | { readonly type: "unsubscribe"; readonly agent: AgentId; readonly topic: TopicId }
  | {
      readonly type: "post";
      readonly agent: AgentId;
      readonly post: PostId;
      readonly topic: TopicId;
      readonly parent: PostId | null;
    };

export type BoardAction = BoardEvent["type"];

/** Every action of the product machine, in specification order. */
export const BOARD_ACTIONS: readonly BoardAction[] = [
  "register",
  "bind",
  "unbind",
  "send",
  "deliver",
  "fail",
  "subscribe",
  "unsubscribe",
  "post",
];

/** Construct the initial state. */
export function initAbstractBoardState(config: BoardModelConfig): AbstractBoardState {
  const registered: Record<AgentId, boolean> = {};
  const bound: Record<AgentId, BoxId | null> = {};
  const subscribed: Record<AgentId, readonly TopicId[]> = {};
  for (const agent of config.agents) {
    registered[agent] = false;
    bound[agent] = null;
    subscribed[agent] = [];
  }
  const owner: Record<BoxId, AgentId | null> = {};
  const mailbox: Record<BoxId, MessageId[]> = {};
  for (const box of config.boxes) {
    owner[box] = null;
    mailbox[box] = [];
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
  const topic: Record<PostId, TopicId | null> = {};
  for (const post of config.posts) {
    pstatus[post] = "absent";
    author[post] = null;
    porigin[post] = null;
    parent[post] = null;
    topic[post] = null;
  }
  return {
    registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
    mailbox, subscribed, pstatus, author, porigin, parent, topic, posted: [], clock: 0,
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

/** Canonical set encoding: sorted, duplicate-free. Mirrors TLA+ `SUBSET Topics`. */
function sortedUnique(values: readonly string[]): string[] {
  return [...new Set(values)].sort();
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
    (state.mailbox[box]?.length ?? 0) < config.mailboxCapacity &&
    state.clock < (config.maxClock ?? config.messages.length),

  deliver: (state: AbstractBoardState, agent: AgentId, box: BoxId, message: MessageId): boolean =>
    state.registered[agent] === true &&
    state.bound[agent] === box &&
    state.owner[box] === agent &&
    state.mstatus[message] === "queued" &&
    (state.mailbox[box]?.length ?? 0) > 0 &&
    state.mailbox[box]![0] === message,

  /** A failure has no acting agent; the runtime triggers it on expiry or error. */
  fail: (state: AbstractBoardState, box: BoxId, message: MessageId): boolean =>
    state.mstatus[message] === "queued" &&
    state.recipient[message] === box &&
    (state.mailbox[box]?.length ?? 0) > 0 &&
    state.mailbox[box]![0] === message,

  subscribe: (state: AbstractBoardState, config: BoardModelConfig, agent: AgentId, topic: TopicId): boolean =>
    state.registered[agent] === true &&
    config.topics.includes(topic) &&
    !(state.subscribed[agent] ?? []).includes(topic),

  unsubscribe: (state: AbstractBoardState, agent: AgentId, topic: TopicId): boolean =>
    state.registered[agent] === true && (state.subscribed[agent] ?? []).includes(topic),

  post: (
    state: AbstractBoardState,
    config: BoardModelConfig,
    agent: AgentId,
    post: PostId,
    topic: TopicId,
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
        subscribed: state.subscribed[event.agent] === undefined ? set(state.subscribed, event.agent, []) : state.subscribed,
      };
    case "bind": {
      require(guards.bind(state, event.agent, event.box), "bind-not-enabled", event.box);
      return {
        ...state,
        bound: set(state.bound, event.agent, event.box),
        owner: set(state.owner, event.box, event.agent),
        mailbox: state.mailbox[event.box] === undefined ? set(state.mailbox, event.box, []) : state.mailbox,
      };
    }
    case "unbind": {
      require(guards.unbind(state, event.agent), "unbind-not-enabled", event.agent);
      const box = state.bound[event.agent]!;
      return {
        ...state,
        bound: set(state.bound, event.agent, null),
        owner: set(state.owner, box, null),
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
        // Materialize the Init defaults when the live instance admits a new box.
        owner: state.owner[event.box] === undefined ? set(state.owner, event.box, null) : state.owner,
      };
    }
    case "deliver": {
      require(guards.deliver(state, event.agent, event.box, event.message), "deliver-not-enabled", event.message);
      return {
        ...state,
        mstatus: set(state.mstatus, event.message, "delivered"),
        mailbox: set(state.mailbox, event.box, state.mailbox[event.box]!.slice(1)),
      };
    }
    case "fail": {
      require(guards.fail(state, event.box, event.message), "fail-not-enabled", event.message);
      return {
        ...state,
        mstatus: set(state.mstatus, event.message, "failed"),
        mailbox: set(state.mailbox, event.box, state.mailbox[event.box]!.slice(1)),
      };
    }
    case "subscribe": {
      require(guards.subscribe(state, config, event.agent, event.topic), "subscribe-not-enabled", event.topic);
      return {
        ...state,
        subscribed: set(
          state.subscribed,
          event.agent,
          sortedUnique([...(state.subscribed[event.agent] ?? []), event.topic]),
        ),
      };
    }
    case "unsubscribe": {
      require(guards.unsubscribe(state, event.agent, event.topic), "unsubscribe-not-enabled", event.topic);
      return {
        ...state,
        subscribed: set(
          state.subscribed,
          event.agent,
          (state.subscribed[event.agent] ?? []).filter((topic) => topic !== event.topic),
        ),
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
        // Participation is the default watch.
        subscribed: set(
          state.subscribed,
          event.agent,
          sortedUnique([...(state.subscribed[event.agent] ?? []), event.topic]),
        ),
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
      for (const message of config.messages) {
        if (guards.deliver(state, agent, box, message)) events.push({ type: "deliver", agent, box, message });
        if (guards.send(state, config, agent, box, message)) events.push({ type: "send", agent, box, message });
      }
    }
    for (const topic of config.topics) {
      if (guards.subscribe(state, config, agent, topic)) events.push({ type: "subscribe", agent, topic });
      if (guards.unsubscribe(state, agent, topic)) events.push({ type: "unsubscribe", agent, topic });
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
    for (const message of config.messages) {
      if (guards.fail(state, box, message)) events.push({ type: "fail", box, message });
    }
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

  // TypeOK: the state functions have exactly the configured domains and ranges.
  const functionOK = <T>(record: Readonly<Record<string, T>>, domain: readonly string[], accepts: (value: T) => boolean): boolean =>
    Object.keys(record).length === domain.length && domain.every((id) => Object.hasOwn(record, id) && accepts(record[id]!));
  const option = (domain: readonly string[]) => (value: string | null): boolean => value === null || domain.includes(value);
  const timestamp = (value: number): boolean => Number.isInteger(value) && value >= 0 && value <= (config.maxClock ?? config.messages.length);
  const topicSet = (topics: readonly TopicId[]): boolean =>
    topics.every((topic) => config.topics.includes(topic)) && new Set(topics).size === topics.length;
  const typed =
    functionOK(state.registered, config.agents, (value) => typeof value === "boolean") &&
    functionOK(state.bound, config.agents, option(config.boxes)) &&
    functionOK(state.owner, config.boxes, option(config.agents)) &&
    functionOK(state.sender, config.messages, option(config.agents)) &&
    functionOK(state.origin, config.messages, option(config.agents)) &&
    functionOK(state.recipient, config.messages, option(config.boxes)) &&
    functionOK(state.sentAt, config.messages, timestamp) &&
    functionOK(state.mstatus, config.messages, (value) => ["absent", "queued", "delivered", "failed"].includes(value)) &&
    functionOK(state.mailbox, config.boxes, (queue) => queue.every((message) => config.messages.includes(message))) &&
    functionOK(state.subscribed, config.agents, topicSet) &&
    functionOK(state.pstatus, config.posts, (value) => ["absent", "posted"].includes(value)) &&
    functionOK(state.author, config.posts, option(config.agents)) &&
    functionOK(state.porigin, config.posts, option(config.agents)) &&
    functionOK(state.parent, config.posts, option(config.posts)) &&
    functionOK(state.topic, config.posts, option(config.topics)) &&
    state.posted.every((post) => config.posts.includes(post)) && timestamp(state.clock);
  if (!typed) push("TypeOK", "state function domain or range differs from the model");

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

  // Subscriptions belong to registered agents only.
  for (const agent of config.agents) {
    if (state.registered[agent] !== true && (state.subscribed[agent] ?? []).length > 0) {
      push("SubsRegistered", `${agent} holds subscriptions while unregistered`);
    }
  }

  // Placement: every message is in exactly one place, or settled.
  const placements = new Map<MessageId, string[]>();
  for (const message of config.messages) placements.set(message, []);
  for (const box of config.boxes) {
    const queue = state.mailbox[box] ?? [];
    if (queue.length > config.mailboxCapacity) push("Bounded", `${box} mailbox ${queue.length} > capacity`);
    for (const message of queue) {
      placements.get(message)?.push(`mailbox:${box}`);
      if (state.recipient[message] !== box) push("QueueRecipient", `${message} queued in a non-recipient mailbox`);
      if (state.mstatus[message] !== "queued") push("Placement", `${message} in mailbox but not queued`);
    }
    for (let i = 0; i + 1 < queue.length; i += 1) {
      if ((state.sentAt[queue[i]!] ?? 0) >= (state.sentAt[queue[i + 1]!] ?? 0)) {
        push("Fifo", `${box} mailbox out of send order`);
      }
    }
  }
  for (const message of config.messages) {
    const status = state.mstatus[message] ?? "absent";
    const places = placements.get(message) ?? [];
    if (status === "absent" && places.length !== 0) push("Placement", `${message} absent but placed`);
    if (status === "queued" && places.length !== 1) push("Placement", `${message} queued in ${places.length} places`);
    if (status === "delivered" && places.length !== 0) push("Placement", `${message} delivered but placed`);
    if (status === "failed" && places.length !== 0) push("Placement", `${message} failed but placed`);
    if (status !== "absent" && state.sentAt[message]! > state.clock) {
      push("SentAtLeClock", `${message} sent after the current clock`);
    }
    if (status !== "absent" && state.sender[message] !== state.origin[message]) {
      push("Unforgeable", `${message} sender ${state.sender[message]} != origin ${state.origin[message]}`);
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
    // PostsInv constrains parent pointers even for posts outside the log.
    if (state.pstatus[post] !== "posted" && state.parent[post] !== null) {
      push("ParentPosted", `${post} has a parent but is not posted`);
    }
    if (state.pstatus[post] === "posted" && !seen.has(post)) push("BoardAppendOnly", `${post} posted but not in log`);
  }
  return out;
}

/** Names of every invariant checked above. */
export const BOARD_INVARIANT_NAMES: readonly string[] = [
  "TypeOK",
  "BindExclusive",
  "OwnerRegistered",
  "Bounded",
  "Placement",
  "QueueRecipient",
  "SentAtLeClock",
  "Unforgeable",
  "Fifo",
  "SubsRegistered",
  "BoardNoDuplicates",
  "BoardAppendOnly",
  "ParentPosted",
  "ParentTopic",
];
