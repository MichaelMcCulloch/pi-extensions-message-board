import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { BOARD_ACTIONS } from "../src/formal/model.ts";

/** The TLA+ `Next` action list must equal the executable action alphabet. */
function tlaActions(): string[] {
  const path = fileURLToPath(new URL("../spec/MessageBoard.tla", import.meta.url));
  const text = readFileSync(path, "utf8");
  const start = text.indexOf("Next ==");
  const end = text.indexOf("Inv ==");
  const block = text.slice(start, end);
  const names: string[] = [];
  for (const match of block.matchAll(/:\s*(\w+)\(/g)) {
    names.push(match[1]!.toLowerCase());
  }
  return [...new Set(names)];
}

describe("TLA+ / TypeScript parity", () => {
  it("the spec's Next lists exactly the model actions", () => {
    expect(tlaActions().sort()).toEqual([...BOARD_ACTIONS].sort());
  });

  it("every action has a guard in the spec", () => {
    const path = fileURLToPath(new URL("../spec/MessageBoard.tla", import.meta.url));
    const text = readFileSync(path, "utf8");
    const guardName: Record<string, string> = {
      register: "GuardRegister",
      bind: "GuardBind",
      unbind: "GuardUnbind",
      send: "GuardSend",
      deliver: "GuardDeliver",
      fail: "GuardFail",
      subscribe: "GuardSubscribe",
      unsubscribe: "GuardUnsubscribe",
      post: "GuardPost",
    };
    for (const action of BOARD_ACTIONS) {
      expect(text, `missing ${guardName[action]}`).toContain(`${guardName[action]}(`);
    }
  });
});
