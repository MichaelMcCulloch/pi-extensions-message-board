import { describe, expect, it } from "vitest";
import { memoryBoard } from "../src/extension/store.ts";

describe("board store (push delivery)", () => {
  it("pushes through bind, send, and deliver", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    const sent = board.send("a1", "inbox", "hello");
    expect(board.inbox("inbox")).toHaveLength(1);

    const pending = board.pending("a2");
    expect(pending).toHaveLength(1);
    expect(pending[0]).toMatchObject({ box: "inbox", id: sent.message, from: "a1", body: "hello" });

    board.deliver("a2", "inbox", sent.message);
    expect(board.state.mstatus[sent.message]).toBe("delivered");
    expect(board.inbox("inbox")).toHaveLength(0);
    expect(board.pending("a2")).toHaveLength(0);
    expect(board.violations()).toEqual([]);
  });

  it("keeps a send to an unbound name until someone binds it", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    const sent = board.send("a1", "inbox", "durable");
    expect(board.inbox("inbox")).toHaveLength(1);
    // a2 serves nothing, so there is nothing to push.
    expect(board.pending("a2")).toEqual([]);
    board.bind("a2", "inbox");
    expect(board.pending("a2")).toEqual([
      { box: "inbox", id: sent.message, from: "a1", body: "durable" },
    ]);
    board.deliver("a2", "inbox", sent.message);
    expect(board.state.mstatus[sent.message]).toBe("delivered");
    expect(board.violations()).toEqual([]);
  });

  it("delivers heads in send order", () => {
    const board = memoryBoard();
    board.register("a1");
    board.bind("a1", "inbox");
    board.send("a1", "inbox", "one", "m-1");
    board.send("a1", "inbox", "two", "m-2");
    expect(board.pending("a1").map((entry) => entry.id)).toEqual(["m-1"]);
    board.deliver("a1", "inbox", "m-1");
    expect(board.pending("a1").map((entry) => entry.id)).toEqual(["m-2"]);
    board.deliver("a1", "inbox", "m-2");
    expect(board.pending("a1")).toEqual([]);
    expect(board.violations()).toEqual([]);
  });

  it("fails a queued message instead of redelivering it forever", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    const sent = board.send("a1", "inbox", "expired");
    board.fail("inbox", sent.message);
    expect(board.state.mstatus[sent.message]).toBe("failed");
    expect(board.inbox("inbox")).toHaveLength(0);
    expect(board.pending("a2")).toEqual([]);
    expect(board.violations()).toEqual([]);
  });

  it("hands queued messages to the next binder on unbind", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    const sent = board.send("a1", "inbox", "handover");
    board.unbind("a2");
    expect(board.inbox("inbox")).toHaveLength(1);
    expect(board.state.owner["inbox"]).toBe(null);
    board.bind("a1", "inbox");
    expect(board.pending("a1")[0]?.id).toBe(sent.message);
    expect(board.violations()).toEqual([]);
  });

  it("loads snapshots that predate the owner and subscribed fields", () => {
    const original = memoryBoard();
    original.register("a1");
    original.send("a1", "inbox", "durable");
    const legacy = { ...original.state } as unknown as Record<string, unknown>;
    delete legacy["owner"];
    delete legacy["subscribed"];
    const board = memoryBoard(legacy as never);
    expect(board.violations()).toEqual([]);
    board.register("a2");
    board.bind("a2", "inbox");
    expect(board.pending("a2")[0]?.body).toBe("durable");
    expect(board.violations()).toEqual([]);
  });

  it("subscribes the author on post; explicit watch and unwatch override", () => {
    const board = memoryBoard();
    board.register("a1");
    expect(board.subscriptions("a1")).toEqual([]);
    board.post("a1", "design", "root", "first");
    expect(board.subscriptions("a1")).toEqual(["design"]);
    board.unsubscribe("a1", "design");
    expect(board.subscriptions("a1")).toEqual([]);
    board.post("a1", "design", "again", "second");
    // Posting again is participation, so it re-subscribes.
    expect(board.subscriptions("a1")).toEqual(["design"]);
    board.subscribe("a1", "alerts");
    expect(board.subscriptions("a1")).toEqual(["alerts", "design"]);
    board.unsubscribe("a1", "alerts");
    expect(board.subscriptions("a1")).toEqual(["design"]);
    expect(board.violations()).toEqual([]);
  });

  it("does not subscribe a reader", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.post("a1", "design", "root", "first");
    board.read("design");
    expect(board.subscriptions("a2")).toEqual([]);
  });

  it("derives authorship from the acting agent", () => {
    const board = memoryBoard();
    board.register("a1");
    board.bind("a1", "inbox");
    board.send("a1", "inbox", "from a1", "m-1");
    expect(board.state.sender["m-1"]).toBe("a1");
    expect(board.state.origin["m-1"]).toBe("a1");
  });

  it("appends forum posts and rejects an unknown parent", () => {
    const board = memoryBoard();
    board.register("a1");
    const root = board.post("a1", "alerts", "root", "first");
    board.post("a1", "alerts", "reply", "second", root.post);
    expect(board.read("alerts").map((post) => post.subject)).toEqual(["root", "reply"]);
    expect(() => board.post("a1", "alerts", "bad", "x", "p-missing")).toThrow();
    expect(board.violations()).toEqual([]);
  });

  it("refuses an unregistered sender", () => {
    const board = memoryBoard();
    board.register("a1");
    expect(() => board.send("ghost", "inbox", "boo")).toThrow();
  });
});
