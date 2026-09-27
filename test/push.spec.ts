import { describe, expect, it } from "vitest";
import { BOARD_CHANGED, BOARD_DELIVERED, BOARD_FAILED, BOARD_POST } from "../src/extension/bus.ts";
import { BoardPusher, type BoardNotification } from "../src/extension/push.ts";
import { memoryBoard, type BoardStore } from "../src/extension/store.ts";

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

interface Harness {
  readonly pusher: BoardPusher;
  readonly notifications: BoardNotification[];
  readonly events: { channel: string; data: unknown }[];
}

function harness(store: BoardStore, agent: string, options: { failInjection?: boolean } = {}): Harness {
  const notifications: BoardNotification[] = [];
  const events: { channel: string; data: unknown }[] = [];
  const pusher = new BoardPusher({
    store,
    agent,
    notify: (notification) => {
      if (options.failInjection === true) throw new Error("session gone");
      notifications.push(notification);
    },
    emit: (channel, data) => events.push({ channel, data }),
  });
  return { pusher, notifications, events };
}

describe("push watcher", () => {
  it("injects a direct message before marking it delivered", () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    store.bind("a2", "inbox");
    const sent = store.send("a1", "inbox", "hello");

    let statusAtInjection: string | undefined;
    const notifications: BoardNotification[] = [];
    const events: { channel: string; data: unknown }[] = [];
    const pusher = new BoardPusher({
      store,
      agent: "a2",
      notify: (notification) => {
        statusAtInjection = store.state.mstatus[sent.message];
        notifications.push(notification);
      },
      emit: (channel, data) => events.push({ channel, data }),
    });

    pusher.tick();
    // The message was still queued when it reached the context: inject first.
    expect(statusAtInjection).toBe("queued");
    expect(store.state.mstatus[sent.message]).toBe("delivered");
    expect(notifications[0]?.kind).toBe("dm");
    expect(notifications[0]?.text).toContain("hello");
    expect(events).toContainEqual({
      channel: BOARD_DELIVERED,
      data: { box: "inbox", message: sent.message, from: "a1" },
    });
    // A second tick does not redeliver.
    pusher.tick();
    expect(notifications).toHaveLength(1);
    expect(store.violations()).toEqual([]);
  });

  it("fails an un-injectable message and tells the sender", () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    store.bind("a2", "inbox");
    const sent = store.send("a1", "inbox", "poison");

    const recipient = harness(store, "a2", { failInjection: true });
    recipient.pusher.tick();
    expect(store.state.mstatus[sent.message]).toBe("failed");
    expect(recipient.events).toContainEqual({
      channel: BOARD_FAILED,
      data: { box: "inbox", message: sent.message, reason: "injection-failed" },
    });

    const sender = harness(store, "a1");
    sender.pusher.tick();
    expect(sender.notifications[0]?.kind).toBe("failure");
    expect(sender.notifications[0]?.text).toContain("injection-failed");
    // The notice is reported once.
    sender.pusher.tick();
    expect(sender.notifications).toHaveLength(1);
  });

  it("coalesces forum activity per topic for subscribers, never the author", () => {
    const store = memoryBoard();
    for (const agent of ["a1", "a2", "a3"]) store.register(agent);
    store.subscribe("a2", "design");

    const author = harness(store, "a1");
    const subscriber = harness(store, "a2");
    const bystander = harness(store, "a3");

    store.post("a1", "design", "first", "one");
    store.post("a1", "design", "second", "two");
    for (const who of [author, subscriber, bystander]) who.pusher.tick();

    expect(subscriber.notifications).toHaveLength(1);
    expect(subscriber.notifications[0]?.kind).toBe("post");
    expect(subscriber.notifications[0]?.text).toContain("2 new posts");
    expect(subscriber.notifications[0]?.text).toContain("first");
    expect(author.notifications.filter((n) => n.kind === "post")).toHaveLength(0);
    expect(bystander.notifications).toHaveLength(0);
    // The bus reports every post regardless of subscription.
    expect(author.events.filter((e) => e.channel === BOARD_POST)).toHaveLength(2);
  });

  it("does not replay posts that predate the session", () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    store.post("a1", "design", "before you arrived", "old");
    store.subscribe("a2", "design");
    const late = harness(store, "a2");
    late.pusher.tick();
    expect(late.notifications).toHaveLength(0);
  });

  it("expires an undeliverable message and tells its sender", async () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    const sender = harness(store, "a1");
    const sent = store.send("a1", "inbox", "slow", undefined, 1);
    await sleep(5);

    sender.pusher.tick();
    expect(store.state.mstatus[sent.message]).toBe("failed");
    expect(sender.notifications[0]?.kind).toBe("failure");
    expect(sender.notifications[0]?.text).toContain("expired");

    // Everyone can see the settled state; nobody re-notifies.
    sender.pusher.tick();
    expect(sender.notifications).toHaveLength(1);
  });

  it("delivers instead of failing when a recipient arrives after the deadline", async () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    const sender = harness(store, "a1");
    const sent = store.send("a1", "inbox", "late but wanted", undefined, 1);
    await sleep(5);

    // The deadline bounds how long the sender waits, not whether a message
    // that can still be delivered should be thrown away.
    store.bind("a2", "inbox");
    const recipient = harness(store, "a2");
    recipient.pusher.tick();
    expect(store.state.mstatus[sent.message]).toBe("delivered");
    expect(recipient.notifications[0]?.text).toContain("late but wanted");

    sender.pusher.tick();
    expect(sender.notifications).toHaveLength(0);
  });

  it("reports local commits and observed foreign commits as different origins", () => {
    const store = memoryBoard();
    store.register("a1");
    store.register("a2");
    const watcher = harness(store, "a1");

    store.send("a2", "somewhere", "from elsewhere");
    watcher.pusher.tick();
    expect(watcher.events).toContainEqual({
      channel: BOARD_CHANGED,
      data: { revision: store.state.revision, origin: "observed" },
    });

    const eventsBefore = watcher.events.length;
    store.send("a1", "somewhere", "from here");
    watcher.pusher.notifyLocal();
    const local = watcher.events.slice(eventsBefore).filter((e) => e.channel === BOARD_CHANGED);
    expect(local).toHaveLength(1);
    expect(local[0]?.data).toMatchObject({ origin: "local" });
    expect(store.violations()).toEqual([]);
  });
});
