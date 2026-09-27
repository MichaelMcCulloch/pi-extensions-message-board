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
  it("binds, sends, and queues the message for push delivery", async () => {
    const store = memoryBoard();
    const call = toolOn(store);
    await call("a1", { action: "register" });
    await call("a2", { action: "register" });
    await call("a2", { action: "bind", box: "inbox" });

    const sent = await call("a1", { action: "send", box: "inbox", body: "ping" });
    expect(sent.details.message).toBeDefined();
    expect(store.pending("a2")[0]).toMatchObject({ from: "a1", body: "ping" });

    const inbox = await call("a2", { action: "inbox", box: "inbox" });
    expect(inbox.content[0]?.type === "text" && inbox.content[0].text).toContain("ping");

    // The runtime injects and then commits; the tool never fetches.
    store.deliver("a2", "inbox", sent.details.message!);
    const after = await call("a2", { action: "inbox", box: "inbox" });
    expect(after.content[0]?.type === "text" && after.content[0].text).toBe("[]");
  });

  it("subscribes and unsubscribes topics", async () => {
    const store = memoryBoard();
    const call = toolOn(store);
    await call("a1", { action: "register" });
    const watched = await call("a1", { action: "subscribe", topic: "design" });
    expect(watched.content[0]?.type === "text" && watched.content[0].text).toContain("#design");
    expect(store.subscriptions("a1")).toEqual(["design"]);
    await call("a1", { action: "unsubscribe", topic: "design" });
    expect(store.subscriptions("a1")).toEqual([]);
  });

  it("posting subscribes the author and uses the session identity", async () => {
    const store = memoryBoard();
    const call = toolOn(store);
    await call("a9", { action: "register" });
    await call("a9", { action: "post", topic: "t", subject: "s", body: "b" });
    expect(store.projection.posts[0]?.author).toBe("a9");
    expect(store.subscriptions("a9")).toEqual(["t"]);
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
