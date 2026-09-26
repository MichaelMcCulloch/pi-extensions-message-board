import { describe, expect, it } from "vitest";
import { visibleWidth } from "@earendil-works/pi-tui";
import { memoryBoard } from "../src/extension/store.ts";
import { BoardWidget, renderBoardDetail, renderBoardWidget } from "../src/extension/hud.ts";

function populated(): ReturnType<typeof memoryBoard> {
  const store = memoryBoard();
  store.register("alice");
  store.register("bob");
  store.bind("bob", "inbox");
  store.send("alice", "inbox", "the payload is ready", "m-1");
  store.post("alice", "design", "Why not a HUD?", "Because coupling.", null, "p-1");
  return store;
}

describe("board hud renderers", () => {
  it("renders nothing for an unused board", () => {
    expect(renderBoardWidget(memoryBoard())).toEqual([]);
  });

  it("summarizes agents, mailboxes, and topics in the widget", () => {
    const lines = renderBoardWidget(populated()).join("\n");
    expect(lines).toContain("2 agents");
    expect(lines).toContain("inbox · 1 queued");
    expect(lines).toContain("design(1)");
  });

  it("lists queues and forum bodies in the explorer", () => {
    const detail = renderBoardDetail(populated(), 80).join("\n");
    expect(detail).toContain("AGENTS");
    expect(detail).toContain("MAILBOXES");
    expect(detail).toContain("the payload is ready");
    expect(detail).toContain("FORUM");
    expect(detail).toContain("#design");
    expect(detail).toContain("Because coupling.");
  });
});

describe("BoardWidget", () => {
  it("fits lines and caps with a hint", () => {
    const widget = new BoardWidget(() => ["one", "two", "three"], 1);
    const lines = widget.render(40);
    expect(lines).toHaveLength(2);
    for (const line of lines) expect(visibleWidth(line)).toBe(40);
    expect(lines[1]).toContain("+2 more");
  });

  it("activates on a left click", () => {
    let clicks = 0;
    const widget = new BoardWidget(() => ["one"], 8, () => {
      clicks += 1;
    });
    const event = { type: "click", button: "left", x: 1, y: 1, screenX: 1, screenY: 1, width: 40, height: 1, shift: false, alt: false, ctrl: false } as const;
    expect(widget.handleMouse(event)).toEqual({ handled: true });
    expect(clicks).toBe(1);
  });
});
