import { describe, expect, it } from "vitest";
import { memoryBoard } from "../src/extension/store.ts";

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

describe("delivery failures", () => {
  it("expires a message past its deadline and reports it exactly once", async () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    const sent = board.send("a1", "inbox", "late", undefined, 1);
    await sleep(5);
    expect(board.expire()).toEqual([sent.message]);
    expect(board.state.mstatus[sent.message]).toBe("failed");
    expect(board.outboundFailures("a1")).toEqual([{ id: sent.message, box: "inbox", reason: "expired" }]);
    board.markFailureNotified(sent.message);
    expect(board.outboundFailures("a1")).toEqual([]);
    // A second janitor pass must not touch settled messages.
    expect(board.expire()).toEqual([]);
  });

  it("leaves a message with no deadline queued", () => {
    const board = memoryBoard();
    board.register("a1");
    board.bind("a1", "inbox");
    board.send("a1", "inbox", "durable");
    expect(board.expire(Date.now() + 10_000_000)).toEqual([]);
    expect(board.inbox("inbox")).toHaveLength(1);
  });

  it("records the injection failure reason on the message", () => {
    const board = memoryBoard();
    board.register("a1");
    board.register("a2");
    board.bind("a2", "inbox");
    const sent = board.send("a1", "inbox", "boom");
    board.fail("inbox", sent.message, "injection-failed: session gone");
    expect(board.outboundFailures("a1")).toEqual([
      { id: sent.message, box: "inbox", reason: "injection-failed: session gone" },
    ]);
    // The recipient is not told about messages it did not send.
    expect(board.outboundFailures("a2")).toEqual([]);
  });

  it("delivers the head and leaves the rest queued", () => {
    const board = memoryBoard();
    board.register("a1");
    board.bind("a1", "inbox");
    board.send("a1", "inbox", "first", "m-1");
    board.send("a1", "inbox", "second", "m-2");
    board.deliver("a1", "inbox", "m-1");
    expect(board.inbox("inbox").map((entry) => entry.id)).toEqual(["m-2"]);
    expect(board.state.mstatus["m-1"]).toBe("delivered");
  });
});
