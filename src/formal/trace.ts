/**
 * Trace generation for TLC trace validation.
 *
 * The traces are produced by driving the **production store** (`BoardStore`) one
 * command at a time and recording the abstract board state after each. The
 * store's transition IS `referenceReduceBoardState` (the mirror of
 * `spec/MessageBoard.tla`), so replaying these traces checks the production
 * command→event mapping and the store's bookkeeping against the one model.
 */

import { abstractBoardState, type BoardState } from "../engine/board.ts";
import { memoryBoard, type BoardStore } from "../extension/store.ts";
import {
  BOARD_MODEL,
  initAbstractBoardState,
  type AbstractBoardState,
  type BoardEvent,
  type BoxId,
  type MessageId,
  type PostId,
  type TopicId,
} from "./model.ts";

/** One recorded step. The first step has `event: null`. */
export interface TraceStep {
  readonly event: BoardEvent | null;
  readonly state: AbstractBoardState;
}

/** A step: one command applied to the production store, returning its event. */
export type Step = (store: BoardStore) => BoardEvent;

/** A named scenario. */
export interface Scenario {
  readonly name: string;
  readonly steps: readonly Step[];
}

/** The initial state of the fixed verification universe. */
function initialBoard(): BoardState {
  return {
    ...initAbstractBoardState(BOARD_MODEL),
    revision: 0,
    bodies: {},
    subjects: {},
    postBodies: {},
  };
}

const register = (agent: string): Step => (store) => {
  store.register(agent);
  return { type: "register", agent };
};
const unregister = (agent: string): Step => (store) => {
  store.unregister(agent);
  return { type: "unregister", agent };
};
const bind = (agent: string, box: BoxId): Step => (store) => {
  store.bind(agent, box);
  return { type: "bind", agent, box };
};
const unbind = (agent: string): Step => (store) => {
  store.unbind(agent);
  return { type: "unbind", agent };
};
const send = (agent: string, box: BoxId, message: MessageId): Step => (store) => {
  store.send(agent, box, `body:${message}`, message);
  return { type: "send", agent, box, message };
};
const deliver = (agent: string, box: BoxId, message: MessageId): Step => (store) => {
  store.deliver(agent, box, message);
  return { type: "deliver", agent, box, message };
};
const fail = (box: BoxId, message: MessageId): Step => (store) => {
  store.fail(box, message);
  return { type: "fail", box, message };
};
const subscribe = (agent: string, topic: TopicId): Step => (store) => {
  store.subscribe(agent, topic);
  return { type: "subscribe", agent, topic };
};
const unsubscribe = (agent: string, topic: TopicId): Step => (store) => {
  store.unsubscribe(agent, topic);
  return { type: "unsubscribe", agent, topic };
};
const post = (agent: string, id: PostId, topic: TopicId, parent: PostId | null): Step => (store) => {
  store.post(agent, topic, `subject:${id}`, `body:${id}`, parent, id);
  return { type: "post", agent, post: id, topic, parent };
};

/** The scenarios the validator replays, covering every action. */
export function scenarios(): Scenario[] {
  return [
    {
      name: "direct",
      steps: [
        register("a1"),
        register("a2"),
        bind("a2", "bx1"),
        send("a1", "bx1", "m1"),
        deliver("a2", "bx1", "m1"),
      ],
    },
    {
      name: "durable-unbound-inbox",
      steps: [
        register("a1"),
        register("a2"),
        send("a1", "bx1", "m1"),
        bind("a2", "bx1"),
        deliver("a2", "bx1", "m1"),
      ],
    },
    {
      name: "fifo-order",
      steps: [
        register("a1"),
        bind("a1", "bx1"),
        send("a1", "bx1", "m1"),
        send("a1", "bx1", "m2"),
        deliver("a1", "bx1", "m1"),
        deliver("a1", "bx1", "m2"),
      ],
    },
    {
      name: "expiry-failure",
      steps: [
        register("a1"),
        register("a2"),
        bind("a2", "bx1"),
        send("a1", "bx1", "m1"),
        fail("bx1", "m1"),
      ],
    },
    {
      name: "subscriptions",
      steps: [
        register("a1"),
        subscribe("a1", "t1"),
        unsubscribe("a1", "t1"),
        subscribe("a1", "t1"),
      ],
    },
    {
      name: "forum-thread",
      steps: [register("a1"), post("a1", "p1", "t1", null), post("a1", "p2", "t1", "p1")],
    },
    {
      name: "session-exit",
      steps: [register("a1"), subscribe("a1", "t1"), unregister("a1")],
    },
    {
      name: "mixed",
      steps: [
        register("a1"),
        register("a2"),
        bind("a2", "bx1"),
        send("a1", "bx1", "m1"),
        send("a1", "bx1", "m2"),
        post("a1", "p1", "t1", null),
        subscribe("a2", "t1"),
        deliver("a2", "bx1", "m1"),
        post("a2", "p2", "t1", "p1"),
        fail("bx1", "m2"),
        unsubscribe("a1", "t1"),
        unbind("a2"),
      ],
    },
  ];
}

/** Drive a scenario through the production store and record every state. */
export function runScenario(scenario: Scenario): TraceStep[] {
  const store = memoryBoard(initialBoard());
  const trace: TraceStep[] = [{ event: null, state: abstractBoardState(store.state) }];
  for (const step of scenario.steps) {
    const event = step(store);
    trace.push({ event, state: abstractBoardState(store.state) });
  }
  return trace;
}

/* -------------------------------------------------------------------------- */
/* TLA+ rendering                                                             */
/* -------------------------------------------------------------------------- */

const NONE = "none";

function quote(value: string): string {
  return `"${value.replaceAll("\\", "\\\\").replaceAll('"', '\\"')}"`;
}

function bool(value: boolean): string {
  return value ? "TRUE" : "FALSE";
}

function record(keys: readonly string[], render: (key: string) => string): string {
  return `[ ${keys.map((key) => `${key} |-> ${render(key)}`).join(", ")} ]`;
}

function sequence(items: readonly string[]): string {
  return `<<${items.map(quote).join(", ")}>>`;
}

/** Render a sorted string list as a TLA+ set. */
function setOf(items: readonly string[]): string {
  return `{${[...items].sort().map(quote).join(", ")}}`;
}

function tlaState(state: AbstractBoardState): string {
  const agents = BOARD_MODEL.agents;
  const boxes = BOARD_MODEL.boxes;
  const messages = BOARD_MODEL.messages;
  const posts = BOARD_MODEL.posts;
  return [
    "[",
    `registered |-> ${record(agents, (a) => bool(state.registered[a] === true))}`,
    `, bound |-> ${record(agents, (a) => quote(state.bound[a] ?? NONE))}`,
    `, owner |-> ${record(boxes, (b) => quote(state.owner[b] ?? NONE))}`,
    `, sender |-> ${record(messages, (m) => quote(state.sender[m] ?? NONE))}`,
    `, origin |-> ${record(messages, (m) => quote(state.origin[m] ?? NONE))}`,
    `, recipient |-> ${record(messages, (m) => quote(state.recipient[m] ?? NONE))}`,
    `, sentAt |-> ${record(messages, (m) => String(state.sentAt[m] ?? 0))}`,
    `, mstatus |-> ${record(messages, (m) => quote(state.mstatus[m] ?? "absent"))}`,
    `, mailbox |-> ${record(boxes, (b) => sequence(state.mailbox[b] ?? []))}`,
    `, subscribed |-> ${record(agents, (a) => setOf(state.subscribed[a] ?? []))}`,
    `, pstatus |-> ${record(posts, (p) => quote(state.pstatus[p] ?? "absent"))}`,
    `, author |-> ${record(posts, (p) => quote(state.author[p] ?? NONE))}`,
    `, porigin |-> ${record(posts, (p) => quote(state.porigin[p] ?? NONE))}`,
    `, parent |-> ${record(posts, (p) => quote(state.parent[p] ?? NONE))}`,
    `, topic |-> ${record(posts, (p) => quote(state.topic[p] ?? NONE))}`,
    `, posted |-> ${sequence(state.posted)}`,
    `, clock |-> ${state.clock}`,
    "]",
  ].join(" ");
}

function tlaEvent(event: BoardEvent | null): string {
  const fields: string[] = [`type |-> ${quote(event?.type ?? "init")}`];
  const get = (key: string): string => {
    const value = (event as unknown as Record<string, unknown> | null)?.[key];
    return quote(typeof value === "string" ? value : NONE);
  };
  for (const key of ["agent", "box", "message", "topic", "post", "parent"]) {
    fields.push(`${key} |-> ${get(key)}`);
  }
  return `[ ${fields.join(", ")} ]`;
}

function tlaTrace(steps: readonly TraceStep[]): string {
  const records = steps.map((step) => `[ event |-> ${tlaEvent(step.event)}, state |-> ${tlaState(step.state)} ]`);
  return `<<\n  ${records.join(",\n  ")}\n>>`;
}

/** Render the generated `TracesData` module TLC consumes. */
export function renderTracesModule(traces: readonly (readonly TraceStep[])[]): string {
  const rendered = traces.map((trace, index) => `\\* trace ${index}\n${tlaTrace(trace)}`);
  return [
    "---------------------------- MODULE TracesData ----------------------------",
    "\\* Generated by scripts/emit-traces.ts. Do not edit.",
    "",
    `Traces == <<\n${rendered.join(",\n")}\n>>`,
    "",
    "=============================================================================",
    "",
  ].join("\n");
}

/** Build every scenario trace from the production store. */
export function buildTraces(): { name: string; trace: TraceStep[] }[] {
  return scenarios().map((scenario) => ({ name: scenario.name, trace: runScenario(scenario) }));
}
