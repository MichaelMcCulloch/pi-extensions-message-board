import { describe, expect, it } from "vitest";
import { memoryBoard } from "../src/extension/store.ts";

describe("board store (named mailboxes)", () => {
  it("delivers through bind, send, recv, ack", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    board.send("a1", "inbox", "hello");
    expect(board.inbox("inbox")).toHaveLength(1);

    const fetched = board.recv("a2", "inbox");
    expect(fetched.message?.body).toBe("hello");
    expect(fetched.message?.from).toBe("a1");
    board.ack("a2", "inbox", fetched.message!.id);
    expect(board.state.mstatus[fetched.message!.id]).toBe("acked");
    expect(board.inbox("inbox")).toHaveLength(0);
    expect(board.violations()).toEqual([]);
  });

  it("keeps a send to an unbound name until someone binds it", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.send("a1", "inbox", "durable");
    expect(board.inbox("inbox")).toHaveLength(1);
    // a2 cannot recv without binding.
    expect(() => board.recv("a2", "inbox")).toThrow();
    board.bind("a2", "inbox");
    const fetched = board.recv("a2", "inbox");
    expect(fetched.message?.body).toBe("durable");
    expect(board.violations()).toEqual([]);
  });

  it("loads legacy unbound mailboxes with implicit owner and lease defaults", () => {
    const original = memoryBoard();
    original.register("a1");
    original.send("a1", "inbox", "durable");
    const board = memoryBoard({ ...original.state, owner: {}, lease: {} });
    expect(board.violations()).toEqual([]);
    board.register("a2");
    board.bind("a2", "inbox");
    expect(board.recv("a2", "inbox").message?.body).toBe("durable");
    expect(board.violations()).toEqual([]);
  });

  it("reclaims a lease and redelivers", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    board.send("a1", "inbox", "ttl");
    const first = board.recv("a2", "inbox");
    board.reclaim("inbox");
    expect(board.state.mstatus[first.message!.id]).toBe("queued");
    const second = board.recv("a2", "inbox");
    board.ack("a2", "inbox", second.message!.id);
    expect(board.state.mstatus[second.message!.id]).toBe("acked");
    expect(board.violations()).toEqual([]);
  });

  it("requeues a fetched message when the binder releases the name", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    board.send("a1", "inbox", "handover");
    board.recv("a2", "inbox");
    board.unbind("a2");
    expect(board.inbox("inbox")).toHaveLength(1);
    expect(board.state.owner["inbox"]).toBe(null);
    expect(board.violations()).toEqual([]);
  });

  it("derives authorship from the acting agent", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    board.send("a1", "inbox", "from a1");
    const fetched = board.recv("a2", "inbox");
    expect(board.state.sender[fetched.message!.id]).toBe("a1");
    expect(board.state.origin[fetched.message!.id]).toBe("a1");
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
