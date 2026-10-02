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
  "whoami",
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

export const FORUM_TOOL_ACTIONS = ['whoami', 'subscribe', 'unsubscribe', 'post', 'read', 'topics', 'status'] as const;
export const MAILBOX_TOOL_ACTIONS = ['whoami', 'unbind', 'send', 'inbox', 'status'] as const;
const boardParams = (actions: readonly (typeof BOARD_TOOL_ACTIONS)[number][]) => Type.Object({
  action: StringEnum(actions),
  box: Type.Optional(Type.String({ description: "Mailbox name to send to or inspect." })),
  body: Type.Optional(Type.String({ description: "Message or post body." })),
  topic: Type.Optional(Type.String({ description: "Forum topic to post in, read, watch, or stop watching." })),
  subject: Type.Optional(Type.String({ description: "Forum post subject." })),
  parent: Type.Optional(Type.String({ description: "Post id this post replies to." })),
  since: Type.Optional(Type.String({ description: "Read posts after this post id." })),
  ttlMs: Type.Optional(
    Type.Number({
      description:
        "Optional time-to-live in milliseconds for action=send. If the message is not delivered in time it fails and you are told; omit it for a durable inbox that waits forever.",
    }),
  ),
});
const BoardParams = boardParams(BOARD_TOOL_ACTIONS);

interface BoardDetails {
  readonly data?: unknown;
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
  facet?: 'forum' | 'mailbox',
): ToolDefinition<typeof BoardParams, BoardDetails> {
  const actions = facet === 'forum' ? FORUM_TOOL_ACTIONS : facet === 'mailbox' ? MAILBOX_TOOL_ACTIONS : BOARD_TOOL_ACTIONS;
  const tool: ToolDefinition<typeof BoardParams, BoardDetails> = {
    name: facet ?? "board",
    namespace: { name: facet ?? "board", description: facet === "forum" ? "Shared discussions and subscriptions" : facet === "mailbox" ? "Addressed durable agent messages" : "Agent communication" },
    label: facet === 'forum' ? 'Forum' : facet === 'mailbox' ? 'Mailbox' : "Board",
    description: facet === 'forum' ? 'Post findings in shared topics, read discussions, and subscribe to updates. Posting subscribes you; new posts are pushed into context. Membership and identity are the pi session.' : facet === 'mailbox' ? 'Send direct messages to other agents by mailbox name. Your own name is assigned when the session starts; incoming messages are pushed into context. Identity is your pi session.' :
      "Cooperate with other agents over a shared board. Direct: send to a mailbox name; the recipient's runtime pushes the message into its context. Broadcast: post to a forum topic, read a topic, list topics; posting in a topic subscribes you to it, and each new post is pushed to subscribers. Every session is registered and serves a mailbox automatically; your identity is your session and you cannot post or send as another agent.",
    promptSnippet: facet === 'forum' ? 'forum: publish and discuss shared findings' : facet === 'mailbox' ? 'mailbox: send addressed messages to agents' : "board: message other agents directly or post to a shared forum",
    promptGuidelines: facet ? [facet === 'forum' ? 'Use topics for shared findings; post subscribes you to updates.' : 'Your mailbox is assigned when the session starts; action=whoami reports it and incoming messages are pushed automatically.'] : [
      "Every session is registered and serves a mailbox automatically; use action=whoami to see the name this session serves.",
      "Use action=post/read for shared findings and questions that any agent may need, not just one recipient; posting subscribes you to that topic.",
      "Use action=subscribe/unsubscribe to watch topics you have not posted in, or to stop notifications from ones you have.",
    ],
    parameters: boardParams(actions),
    executionMode: "sequential",
    async execute(_toolCallId, params, _signal, _onUpdate, ctx): Promise<{ content: { type: "text"; text: string }[]; details: BoardDetails }> {
      if (!(actions as readonly string[]).includes(params.action)) throw new BoardOperationError('board-wrong-facet', `${params.action} is not available through ${facet}`);
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
            ...(outcome.data === undefined ? {} : {data:outcome.data}),
            ...(outcome.message === undefined ? {} : { message: outcome.message }),
            ...(outcome.post === undefined ? {} : { post: outcome.post }),
            board: store.projection,
          },
        };
      } catch (error) {
        if (error instanceof BoardOperationError) {
          // Throw refusals so model and codemode callers receive a failure.
          throw new BoardOperationError(
            error.code,
            `board ${params.action} refused (${error.code}): ${error.message}`,
          );
        }
        throw error;
      }
    },
  };
  return {
    ...tool,
    outputSchema: Type.Object({action:Type.String(),revision:Type.Integer(),agent:Type.String(),board:Type.Unknown(),data:Type.Optional(Type.Unknown()),message:Type.Optional(Type.String()),post:Type.Optional(Type.String())}),
    async execute(...args) {
      const result = await tool.execute(...args);
      return {...result,structuredContent:JSON.parse(JSON.stringify(result.details))};
    },
  };
}

/** The acting agent's identity: the pi session, never a tool argument. */
export function agentOf(ctx: ExtensionContext): string {
  return ctx.sessionManager.getSessionId();
}

interface Outcome {
  readonly data?: unknown;
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
    ttlMs?: number;
  },
): Outcome {
  switch (params.action) {
    case "whoami":
      return { text: `${agent}${store.boundBox(agent) === null ? "" : ` serving ${store.boundBox(agent)}`}` };
    case "unbind":
      store.unbind(agent);
      return { text: `${agent} released its mailbox` };
    case "send": {
      const box = requireParam(params.box, "box", "send");
      const body = requireParam(params.body, "body", "send");
      const result = store.send(agent, box, body, undefined, params.ttlMs);
      return { text: `queued ${result.message} to ${box}; it is pushed when the name is served`, message: result.message };
    }
    case "inbox": {
      const box = requireParam(params.box, "box", "inbox");
      const data=store.inbox(box); return {text:JSON.stringify(data),data};
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
      const data=store.read(topic, params.since ?? null); return {text:JSON.stringify(data),data};
    }
    case "topics": {
      const data=store.topics(); return {text:JSON.stringify(data),data};
    }
    case "status":
      return { text: JSON.stringify(store.projection) };
  }
}
