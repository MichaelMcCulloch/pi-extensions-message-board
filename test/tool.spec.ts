import { describe, expect, it } from "vitest";
import type { ExtensionContext } from "@earendil-works/pi-coding-agent";
import { buildBoardTool } from "../src/extension/tool.ts";
import { memoryBoard } from "../src/extension/store.ts";

function ctxFor(agent: string): ExtensionContext {
  return { sessionManager: { getSessionId: () => agent } } as unknown as ExtensionContext;
}

function toolOn(store: ReturnType<typeof memoryBoard>) {
  const tool = buildBoardTool(() => store);
  return (agent: string, params: unknown) =>
    tool.execute!("call", params as never, undefined, undefined, ctxFor(agent));
}

describe("board tool", () => {
  it("binds, sends, fetches, and acks a named mailbox", async () => {
    const call = toolOn(memoryBoard());
    await call("a1", { action: "register" });
    await call("a2", { action: "register" });
    await call("a2", { action: "bind", box: "inbox" });

    const sent = await call("a1", { action: "send", box: "inbox", body: "ping" });
    expect(sent.details.message).toBeDefined();

    const fetched = await call("a2", { action: "recv", box: "inbox" });
    expect(fetched.content[0]?.type === "text" && fetched.content[0].text).toContain("ping");
    const messageId = fetched.details.message!;
    await call("a2", { action: "ack", box: "inbox", message: messageId });
    const inbox = await call("a2", { action: "inbox", box: "inbox" });
    expect(inbox.content[0]?.type === "text" && inbox.content[0].text).toBe("[]");
  });

  it("revokes a lease with reclaim", async () => {
    const call = toolOn(memoryBoard());
    await call("a1", { action: "register" });
    await call("a2", { action: "register" });
    await call("a2", { action: "bind", box: "inbox" });
    await call("a1", { action: "send", box: "inbox", body: "ttl" });
    await call("a2", { action: "recv", box: "inbox" });
    const reclaimed = await call("a1", { action: "reclaim", box: "inbox" });
    expect(reclaimed.content[0]?.type === "text" && reclaimed.content[0].text).toContain("revoked");
    const again = await call("a2", { action: "recv", box: "inbox" });
    expect(again.content[0]?.type === "text" && again.content[0].text).toContain("ttl");
  });

  it("uses the session identity as the author", async () => {
    const store = memoryBoard();
    const call = toolOn(store);
    await call("a9", { action: "register" });
    await call("a9", { action: "post", topic: "t", subject: "s", body: "b" });
    expect(store.projection.posts[0]?.author).toBe("a9");
  });

  it("surfaces a refusal as a thrown tool error so the agent sees the fault", async () => {
    const call = toolOn(memoryBoard());
    // Returning the refusal as content would be recorded as a successful call
    // (`isError: false`); throwing is the only way to signal failure.
    await expect(call("a1", { action: "send", box: "inbox", body: "x" })).rejects.toThrow(/board-unregistered/);
  });

  it("reports whoami from the session", async () => {
    const call = toolOn(memoryBoard());
    const result = await call("a7", { action: "whoami" });
    expect(result.content[0]?.type === "text" && result.content[0].text).toContain("a7");
  });
});
