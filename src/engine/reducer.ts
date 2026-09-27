/**
 * The reducer (push revision).
 *
 * Every machine transition is `referenceReduceBoardState`, the executable model
 * TLC proves safe. `isEnabled` is the single source of truth for "is this
 * transition legal"; consumers ask, they do not re-derive.
 */

import {
  enabledEvents,
  guards,
  referenceReduceBoardState,
  type AbstractBoardState,
  type AgentId,
  type BoardEvent,
  type BoxId,
  type MessageId,
  type PostId,
  type TopicId,
} from "../formal/model.ts";
import { boardConfigOf, type BoardState } from "./board.ts";

/** A command the delivery machinery or the model-facing tool can issue. */
export type BoardCommand =
  | { readonly type: "register"; readonly agent: AgentId }
  | { readonly type: "bind"; readonly agent: AgentId; readonly box: BoxId }
  | { readonly type: "unbind"; readonly agent: AgentId }
  | { readonly type: "send"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId; readonly body: string }
  | { readonly type: "deliver"; readonly agent: AgentId; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "fail"; readonly box: BoxId; readonly message: MessageId }
  | { readonly type: "subscribe"; readonly agent: AgentId; readonly topic: TopicId }
  | { readonly type: "unsubscribe"; readonly agent: AgentId; readonly topic: TopicId }
  | {
      readonly type: "post";
      readonly agent: AgentId;
      readonly post: PostId;
      readonly topic: TopicId;
      readonly subject: string;
      readonly body: string;
      readonly parent: PostId | null;
    };

/** The result of one accepted command. */
export interface BoardReduceResult {
  readonly state: BoardState;
  readonly events: readonly BoardEvent[];
}

/** Map a command to the abstract events it applies. */
export function eventsForCommand(command: BoardCommand): BoardEvent[] {
  switch (command.type) {
    case "register":
      return [{ type: "register", agent: command.agent }];
    case "bind":
      return [{ type: "bind", agent: command.agent, box: command.box }];
    case "unbind":
      return [{ type: "unbind", agent: command.agent }];
    case "send":
      return [{ type: "send", agent: command.agent, box: command.box, message: command.message }];
    case "deliver":
      return [{ type: "deliver", agent: command.agent, box: command.box, message: command.message }];
    case "fail":
      return [{ type: "fail", box: command.box, message: command.message }];
    case "subscribe":
      return [{ type: "subscribe", agent: command.agent, topic: command.topic }];
    case "unsubscribe":
      return [{ type: "unsubscribe", agent: command.agent, topic: command.topic }];
    case "post":
      return [
        {
          type: "post",
          agent: command.agent,
          post: command.post,
          topic: command.topic,
          parent: command.parent,
        },
      ];
  }
}

function configFor(state: BoardState, event: BoardEvent): ReturnType<typeof boardConfigOf> {
  switch (event.type) {
    case "bind":
    case "send":
    case "deliver":
    case "fail":
      return boardConfigOf(state, { box: event.box });
    case "subscribe":
    case "unsubscribe":
    case "post":
      return boardConfigOf(state, { topic: event.topic });
    default:
      return boardConfigOf(state);
  }
}

/** Ask the verified model whether one event is enabled in a live board. */
export function isEnabled(state: BoardState, event: BoardEvent): boolean {
  const config = configFor(state, event);
  switch (event.type) {
    case "register":
      return guards.register(state, event.agent);
    case "bind":
      return guards.bind(state, event.agent, event.box);
    case "unbind":
      return guards.unbind(state, event.agent);
    case "send":
      return guards.send(state, config, event.agent, event.box, event.message);
    case "deliver":
      return guards.deliver(state, event.agent, event.box, event.message);
    case "fail":
      return guards.fail(state, event.box, event.message);
    case "subscribe":
      return guards.subscribe(state, config, event.agent, event.topic);
    case "unsubscribe":
      return guards.unsubscribe(state, event.agent, event.topic);
    case "post":
      return guards.post(state, config, event.agent, event.post, event.topic, event.parent);
  }
}

/** Reduce one command against the live board. */
export function reduceBoardCommand(state: BoardState, command: BoardCommand): BoardReduceResult {
  const events = eventsForCommand(command);
  let next: BoardState = state;
  for (const event of events) {
    const config = configFor(next, event);
    const reduced: AbstractBoardState = referenceReduceBoardState(next, event, config);
    next = { ...next, ...reduced };
  }
  let bodies = next.bodies;
  let subjects = next.subjects;
  let postBodies = next.postBodies;
  if (command.type === "send") bodies = { ...bodies, [command.message]: command.body };
  if (command.type === "post") {
    subjects = { ...subjects, [command.post]: command.subject };
    postBodies = { ...postBodies, [command.post]: command.body };
  }
  return {
    state: { ...next, revision: state.revision + events.length, bodies, subjects, postBodies },
    events,
  };
}

/** The events the verified model allows next. */
export function enabledBoardEvents(state: BoardState): BoardEvent[] {
  return enabledEvents(state, boardConfigOf(state));
}
