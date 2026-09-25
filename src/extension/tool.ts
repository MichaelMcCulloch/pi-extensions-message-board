/**
 * The model-facing `board` tool (named-mailbox revision).
 *
 * Identity is the pi session; a mailbox is a durable name an agent binds. This
 * separates delivery from a session lifetime: a later session can bind a name
 * and drain what a previous one left. `recv`/`ack` are POP3 fetch/commit;
 * `reclaim` revokes a lease (the runtime trigger for TTL expiry).
 */

import { StringEnum } from "@earendil-works/pi-ai";
import type { ExtensionContext, ToolDefinition } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import type { BoardStore } from "./store.ts";
import { BoardOperationError } from "./store.ts";

/** Every action the model may issue. */
export const BOARD_TOOL_ACTIONS = [
  "register",
  "whoami",
  "bind",
  "unbind",
  "send",
  "recv",
  "ack",
  "ack_all",
  "rollback",
  "reclaim",
  "inbox",
  "post",
  "read",
  "topics",
  "status",
] as const;

const BoardParams = Type.Object({
  action: StringEnum(BOARD_TOOL_ACTIONS),
  box: Type.Optional(Type.String({ description: "Mailbox name to bind, send to, or read." })),
  message: Type.Optional(Type.String({ description: "Message id to ack." })),
  body: Type.Optional(Type.String({ description: "Message or post body." })),
  topic: Type.Optional(Type.String({ description: "Forum topic name." })),
  subject: Type.Optional(Type.String({ description: "Forum post subject." })),
  parent: Type.Optional(Type.String({ description: "Post id this post replies to." })),
  since: Type.Optional(Type.String({ description: "Read posts after this post id." })),
});

interface BoardDetails {
  readonly action: string;
  readonly revision: number;
  readonly agent: string;
  readonly error?: string;
  readonly board?: unknown;
  readonly message?: string;
  readonly post?: string;
}

/** Build the tool against a lazily constructed store and the caller identity. */
export function buildBoardTool(
  getStore: (ctx: ExtensionContext) => BoardStore,
): ToolDefinition<typeof BoardParams, BoardDetails> {
  return {
    name: "board",
    label: "Board",
    description:
      "Cooperate with other agents over a shared board. Direct: bind a named mailbox, send to a name, recv the head, ack (POP3 fetch/commit), rollback, reclaim. Broadcast: post to a forum topic, read a topic, list topics. Your identity is your session; you cannot post or send as another agent.",
    promptSnippet: "board: message other agents directly or post to a shared forum",
    promptGuidelines: [
      "Bind a durable mailbox name with action=bind, then action=send and action=recv/ack for addressed handoffs.",
      "Use action=post/read for shared findings and questions that any agent may need, not just one recipient.",
    ],
    parameters: BoardParams,
    executionMode: "sequential",
    async execute(_toolCallId, params, _signal, _onUpdate, ctx): Promise<{ content: { type: "text"; text: string }[]; details: BoardDetails }> {
      const store = getStore(ctx);
      const agent = agentOf(ctx);
      store.refresh();
      try {
        const outcome = runAction(store, agent, params);
        return {
          content: [{ type: "text", text: outcome.text }],
          details: {
            action: params.action,
            revision: store.state.revision,
            agent,
            ...(outcome.message === undefined ? {} : { message: outcome.message }),
            ...(outcome.post === undefined ? {} : { post: outcome.post }),
            board: store.projection,
          },
        };
      } catch (error) {
        if (error instanceof BoardOperationError) {
          return {
            content: [{ type: "text", text: `board ${params.action} refused: ${error.message}` }],
            details: { action: params.action, revision: store.state.revision, agent, error: error.code },
          };
        }
        throw error;
      }
    },
  };
}

/** The acting agent's identity: the pi session, never a tool argument. */
export function agentOf(ctx: ExtensionContext): string {
  return ctx.sessionManager.getSessionId();
}

interface Outcome {
  readonly text: string;
  readonly message?: string;
  readonly post?: string;
}

function requireParam(value: string | undefined, name: string, action: string): string {
  if (value === undefined || value.length === 0) {
    throw new BoardOperationError("board-missing-param", `${action} requires ${name}`);
  }
  return value;
}

function runAction(
  store: BoardStore,
  agent: string,
  params: {
    action: (typeof BOARD_TOOL_ACTIONS)[number];
    box?: string;
    message?: string;
    body?: string;
    topic?: string;
    subject?: string;
    parent?: string;
    since?: string;
  },
): Outcome {
  switch (params.action) {
    case "register":
      store.register(agent);
      return { text: `registered ${agent}` };
    case "whoami":
      return { text: `${agent}${store.boundBox(agent) === null ? "" : ` serving ${store.boundBox(agent)}`}` };
    case "bind": {
      const box = requireParam(params.box, "box", "bind");
      store.bind(agent, box);
      return { text: `${agent} now serves ${box}` };
    }
    case "unbind":
      store.unbind(agent);
      return { text: `${agent} released its mailbox` };
    case "send": {
      const box = requireParam(params.box, "box", "send");
      const body = requireParam(params.body, "body", "send");
      const result = store.send(agent, box, body);
      return { text: `queued ${result.message} to ${box}`, message: result.message };
    }
    case "recv": {
      const result = store.recv(agent, params.box);
      if (result.message === null) return { text: `mailbox empty (${result.reason ?? "empty"})` };
      return { text: JSON.stringify(result.message), message: result.message.id };
    }
    case "ack": {
      const box = requireParam(params.box, "box", "ack");
      const message = requireParam(params.message, "message", "ack");
      store.ack(agent, box, message);
      return { text: `acked ${message}`, message };
    }
    case "ack_all":
      store.ackAll(agent);
      return { text: "acked every fetched message" };
    case "rollback": {
      const box = requireParam(params.box, "box", "rollback");
      store.rollback(agent, box);
      return { text: `fetch of ${box} rolled back; the message returns to the queue` };
    }
    case "reclaim": {
      const box = requireParam(params.box, "box", "reclaim");
      store.reclaim(box);
      return { text: `lease on ${box} revoked` };
    }
    case "inbox": {
      const box = requireParam(params.box, "box", "inbox");
      return { text: JSON.stringify(store.inbox(box)) };
    }
    case "post": {
      const topic = requireParam(params.topic, "topic", "post");
      const subject = requireParam(params.subject, "subject", "post");
      const body = requireParam(params.body, "body", "post");
      const result = store.post(agent, topic, subject, body, params.parent ?? null);
      return { text: `posted ${result.post} to ${topic}`, post: result.post };
    }
    case "read": {
      const topic = requireParam(params.topic, "topic", "read");
      return { text: JSON.stringify(store.read(topic, params.since ?? null)) };
    }
    case "topics":
      return { text: JSON.stringify(store.topics()) };
    case "status":
      return { text: JSON.stringify(store.projection) };
  }
}
