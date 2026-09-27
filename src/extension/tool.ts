/**
 * The model-facing `board` tool (push revision).
 *
 * Identity is the pi session; a mailbox is a durable name an agent binds.
 * Messages are pushed into the recipient's context by the runtime, so the tool
 * has no fetch/ack handshake: sending, watching topics, and reading are the
 * surface. Posting in a topic subscribes the author automatically.
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
  "inbox",
  "subscribe",
  "unsubscribe",
  "post",
  "read",
  "topics",
  "status",
] as const;

const BoardParams = Type.Object({
  action: StringEnum(BOARD_TOOL_ACTIONS),
  box: Type.Optional(Type.String({ description: "Mailbox name to bind or send to." })),
  body: Type.Optional(Type.String({ description: "Message or post body." })),
  topic: Type.Optional(Type.String({ description: "Forum topic to post in, read, watch, or stop watching." })),
  subject: Type.Optional(Type.String({ description: "Forum post subject." })),
  parent: Type.Optional(Type.String({ description: "Post id this post replies to." })),
  since: Type.Optional(Type.String({ description: "Read posts after this post id." })),
});

interface BoardDetails {
  readonly action: string;
  readonly revision: number;
  readonly agent: string;
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
      "Cooperate with other agents over a shared board. Direct: bind a durable mailbox name, send to a name; messages are pushed into the recipient's context. Broadcast: post to a forum topic, read a topic, list topics; posting in a topic subscribes you to it, and each new post is pushed to subscribers. Your identity is your session; you cannot post or send as another agent.",
    promptSnippet: "board: message other agents directly or post to a shared forum",
    promptGuidelines: [
      "Bind a durable mailbox name with action=bind so other agents can send you messages; they arrive as push notifications and do not need to be fetched.",
      "Use action=post/read for shared findings and questions that any agent may need, not just one recipient; posting subscribes you to that topic.",
      "Use action=subscribe/unsubscribe to watch topics you have not posted in, or to stop notifications from ones you have.",
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
          // The agent runtime only marks a tool result as an error when
          // `execute` throws; a refusal returned as ordinary content is
          // reported to the model as success. Rethrow with the action and the
          // stable code so the failure is visible and actionable.
          throw new BoardOperationError(
            error.code,
            `board ${params.action} refused (${error.code}): ${error.message}`,
          );
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
      return { text: `${agent} now serves ${box}; messages sent to it will be pushed` };
    }
    case "unbind":
      store.unbind(agent);
      return { text: `${agent} released its mailbox` };
    case "send": {
      const box = requireParam(params.box, "box", "send");
      const body = requireParam(params.body, "body", "send");
      const result = store.send(agent, box, body);
      return { text: `queued ${result.message} to ${box}; it is pushed when the name is served`, message: result.message };
    }
    case "inbox": {
      const box = requireParam(params.box, "box", "inbox");
      return { text: JSON.stringify(store.inbox(box)) };
    }
    case "subscribe": {
      const topic = requireParam(params.topic, "topic", "subscribe");
      store.subscribe(agent, topic);
      return { text: `${agent} now watches #${topic}` };
    }
    case "unsubscribe": {
      const topic = requireParam(params.topic, "topic", "unsubscribe");
      store.unsubscribe(agent, topic);
      return { text: `${agent} stopped watching #${topic}` };
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
