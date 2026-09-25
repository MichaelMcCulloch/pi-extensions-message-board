import { describe, expect, it } from "vitest";
import { ACTIONS_BY_MACHINE, ALL_MACHINES, coveredActions, machineErrors } from "../src/formal/machines.ts";
import { BOARD_ACTIONS } from "../src/formal/model.ts";

describe("machine vocabulary", () => {
  it("every machine is internally consistent", () => {
    for (const machine of ALL_MACHINES) expect(machineErrors(machine), machine.name).toEqual([]);
  });

  it("the product covers every model action", () => {
    expect(coveredActions().sort()).toEqual([...BOARD_ACTIONS].sort());
  });

  it("names every machine that contributes actions", () => {
    expect(Object.keys(ACTIONS_BY_MACHINE).sort()).toEqual([
      "BindingMachine",
      "ForumMachine",
      "MailboxMachine",
      "MessageMachine",
      "RegistryMachine",
    ]);
  });
});
