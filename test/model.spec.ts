import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import {
  BOARD_MODEL,
  boardInvariantViolations,
  enabledEvents,
  guards,
  initAbstractBoardState,
  referenceReduceBoardState,
  type AbstractBoardState,
} from "../src/formal/model.ts";

/**
 * Exhaustive exploration of the same relation TLC checks; the reachable-set
 * size is asserted equal to TLC's, so the spec and this transcription cannot
 * drift apart silently.
 */

const MAX_STATES = 500_000;

function key(state: AbstractBoardState): string {
  const agents = Object.keys(state.registered).sort();
  const boxes = Object.keys(state.owner).sort();
  const messages = Object.keys(state.mstatus).sort();
  const posts = Object.keys(state.pstatus).sort();
  return JSON.stringify([
    agents.map((a) => state.registered[a]),
    agents.map((a) => state.bound[a]),
    agents.map((a) => state.subscribed[a]),
    boxes.map((b) => state.owner[b]),
    boxes.map((b) => state.mailbox[b]),
    messages.map((m) => state.sender[m]),
    messages.map((m) => state.origin[m]),
    messages.map((m) => state.recipient[m]),
    messages.map((m) => state.sentAt[m]),
    messages.map((m) => state.mstatus[m]),
    posts.map((p) => state.pstatus[p]),
    posts.map((p) => state.author[p]),
    posts.map((p) => state.porigin[p]),
    posts.map((p) => state.parent[p]),
    posts.map((p) => state.topic[p]),
    state.posted,
    state.clock,
  ]);
}

function explore(): { visited: Map<string, AbstractBoardState>; actions: Set<string> } {
  const start = initAbstractBoardState(BOARD_MODEL);
  const queue: AbstractBoardState[] = [start];
  const visited = new Map<string, AbstractBoardState>([[key(start), start]]);
  const actions = new Set<string>();
  while (queue.length > 0) {
    const state = queue.shift()!;
    if (visited.size > MAX_STATES) throw new Error("state cap exceeded");
    expect(boardInvariantViolations(state, BOARD_MODEL), `invariant at ${key(state)}`).toEqual([]);
    for (const event of enabledEvents(state, BOARD_MODEL)) {
      actions.add(event.type);
      const next = referenceReduceBoardState(state, event, BOARD_MODEL);
      const k = key(next);
      if (!visited.has(k)) {
        visited.set(k, next);
        queue.push(next);
      }
    }
  }
  return { visited, actions };
}

describe("abstract message board (push delivery)", () => {
  const exploration = explore();

  it("never leaves the invariant", () => {
    for (const state of exploration.visited.values()) {
      expect(boardInvariantViolations(state, BOARD_MODEL)).toEqual([]);
    }
  });

  it("reaches every action", () => {
    expect([...exploration.actions].sort()).toEqual(
      ["bind", "deliver", "fail", "post", "register", "send", "subscribe", "unbind", "unsubscribe"].sort(),
    );
  });

  it("reaches exactly the state set TLC model-checked", () => {
    const countPath = fileURLToPath(new URL("../spec/.tlc-state-count.json", import.meta.url));
    expect(existsSync(countPath), "run `node scripts/tla.mjs model` first").toBe(true);
    const { distinctStates } = JSON.parse(readFileSync(countPath, "utf8")) as { distinctStates: number };
    expect(exploration.visited.size).toBe(distinctStates);
  });

  it("leaves a send to an unbound name durable, then delivers after bind", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a2" }, BOARD_MODEL);
    // a2 is not bound yet: the message waits in the durable inbox.
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, BOARD_MODEL);
    expect(state.mstatus["m1"]).toBe("queued");
    expect(state.owner["bx1"]).toBe(null);
    // A later agent binds the name and the runtime delivers the head.
    state = referenceReduceBoardState(state, { type: "bind", agent: "a2", box: "bx1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "deliver", agent: "a2", box: "bx1", message: "m1" }, BOARD_MODEL);
    expect(state.mstatus["m1"]).toBe("delivered");
    expect(state.mailbox["bx1"]).toEqual([]);
  });

  it("fails only the head, preserving queue order", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "bind", agent: "a1", box: "bx1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m2" }, BOARD_MODEL);
    expect(guards.fail(state, "bx1", "m2")).toBe(false);
    expect(guards.fail(state, "bx1", "m1")).toBe(true);
    state = referenceReduceBoardState(state, { type: "fail", box: "bx1", message: "m1" }, BOARD_MODEL);
    expect(state.mstatus["m1"]).toBe("failed");
    expect(state.mailbox["bx1"]).toEqual(["m2"]);
    state = referenceReduceBoardState(state, { type: "fail", box: "bx1", message: "m2" }, BOARD_MODEL);
    expect(state.mstatus["m2"]).toBe("failed");
    expect(state.mailbox["bx1"]).toEqual([]);
    expect(boardInvariantViolations(state, BOARD_MODEL)).toEqual([]);
  });

  it("uses the same MaxClock send guard as the spec", () => {
    const config = { ...BOARD_MODEL, maxClock: 1 };
    let state = initAbstractBoardState(config);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, config);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, config);
    expect(guards.send(state, config, "a1", "bx1", "m2")).toBe(false);
    expect(boardInvariantViolations(state, config)).toEqual([]);
  });

  it("checks the typing, ordering, placement, subscription, and forum strengthenings", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "bind", agent: "a1", box: "bx1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m2" }, BOARD_MODEL);
    const names = (candidate: AbstractBoardState) => boardInvariantViolations(candidate, BOARD_MODEL).map((v) => v.invariant);
    expect(names({ ...state, sentAt: { ...state.sentAt, m2: state.sentAt.m1! } })).toContain("Fifo");
    expect(names({ ...state, clock: 1 })).toContain("SentAtLeClock");
    expect(names({ ...state, sentAt: { ...state.sentAt, m2: 0.5 } })).toContain("TypeOK");
    expect(names({ ...state, subscribed: { ...state.subscribed, a2: ["t1"] } })).toContain("SubsRegistered");
    expect(names({ ...state, mailbox: { bx1: [] } })).toContain("Placement");
    expect(names({ ...state, parent: { ...state.parent, p2: "p1" } })).toContain("ParentPosted");
  });

  it("rejects a queued message in a non-recipient mailbox", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, BOARD_MODEL);
    const corrupt = { ...state, recipient: { ...state.recipient, m1: null } };
    expect(boardInvariantViolations(corrupt, BOARD_MODEL).map((v) => v.invariant)).toContain("QueueRecipient");
  });

  it("bounds the mailbox and drains it by delivery, not by requeue", () => {
    const config = { ...BOARD_MODEL, messages: ["m1", "m2", "m3"] };
    let state = initAbstractBoardState(config);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, config);
    state = referenceReduceBoardState(state, { type: "bind", agent: "a1", box: "bx1" }, config);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m1" }, config);
    state = referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m2" }, config);
    // Two queued = Cap, so a third send is not enabled ...
    expect(guards.send(state, config, "a1", "bx1", "m3")).toBe(false);
    expect(() =>
      referenceReduceBoardState(state, { type: "send", agent: "a1", box: "bx1", message: "m3" }, config),
    ).toThrow();
    // ... until the head is delivered.
    state = referenceReduceBoardState(state, { type: "deliver", agent: "a1", box: "bx1", message: "m1" }, config);
    expect(state.mailbox["bx1"]).toEqual(["m2"]);
    expect(guards.send(state, config, "a1", "bx1", "m3")).toBe(true);
    expect(boardInvariantViolations(state, config)).toEqual([]);
  });

  it("excludes a second binder of the same name", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a2" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "bind", agent: "a1", box: "bx1" }, BOARD_MODEL);
    expect(() =>
      referenceReduceBoardState(state, { type: "bind", agent: "a2", box: "bx1" }, BOARD_MODEL),
    ).toThrow();
  });

  it("subscribes the author on post and honors explicit unsubscribe", () => {
    let state = initAbstractBoardState(BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "register", agent: "a1" }, BOARD_MODEL);
    state = referenceReduceBoardState(state, { type: "post", agent: "a1", post: "p1", topic: "t1", parent: null }, BOARD_MODEL);
    expect(state.subscribed["a1"]).toEqual(["t1"]);
    state = referenceReduceBoardState(state, { type: "unsubscribe", agent: "a1", topic: "t1" }, BOARD_MODEL);
    expect(state.subscribed["a1"]).toEqual([]);
    state = referenceReduceBoardState(state, { type: "post", agent: "a1", post: "p2", topic: "t1", parent: "p1" }, BOARD_MODEL);
    expect(state.subscribed["a1"]).toEqual(["t1"]);
    expect(boardInvariantViolations(state, BOARD_MODEL)).toEqual([]);
  });
});
