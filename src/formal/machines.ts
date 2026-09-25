/**
 * Machine vocabulary (named-mailbox revision).
 *
 * The board is the synchronous product of five machines. `test/machines.spec.ts`
 * and `test/spec-parity.spec.ts` check this against the executable model and the
 * TLA+ actions.
 */

import { BOARD_ACTIONS, type BoardAction } from "./model.ts";

/** One machine edge, with no guards (guards live in the product state). */
export interface MachineEdge {
  readonly from: string;
  readonly on: BoardAction;
  readonly to: string;
}

/** One state machine in the product. */
export interface MachineSpec {
  readonly name: string;
  readonly role: string;
  readonly states: readonly string[];
  readonly edges: readonly MachineEdge[];
}

/** Registry: which agents may act. */
export const REGISTRY_MACHINE: MachineSpec = {
  name: "RegistryMachine",
  role: "agent registration",
  states: ["unregistered", "registered"],
  edges: [{ from: "unregistered", on: "register", to: "registered" }],
};

/** Binding: the exclusive agent<->name mapping. */
export const BINDING_MACHINE: MachineSpec = {
  name: "BindingMachine",
  role: "exclusive named-mailbox binding",
  states: ["unbound", "bound"],
  edges: [
    { from: "unbound", on: "bind", to: "bound" },
    { from: "bound", on: "unbind", to: "unbound" },
  ],
};

/** Mailbox: a per-name FIFO plus its single lease. */
export const MAILBOX_MACHINE: MachineSpec = {
  name: "MailboxMachine",
  role: "per-name queue and lease",
  states: ["idle", "queued", "fetched"],
  edges: [
    { from: "idle", on: "send", to: "queued" },
    { from: "queued", on: "recv", to: "fetched" },
    { from: "fetched", on: "ack", to: "idle" },
    { from: "fetched", on: "rollback", to: "queued" },
    { from: "fetched", on: "reclaim", to: "queued" },
  ],
};

/** Message: the durable lifecycle of one direct message. */
export const MESSAGE_MACHINE: MachineSpec = {
  name: "MessageMachine",
  role: "direct message lifecycle",
  states: ["absent", "queued", "fetched", "acked"],
  edges: [
    { from: "absent", on: "send", to: "queued" },
    { from: "queued", on: "recv", to: "fetched" },
    { from: "fetched", on: "ack", to: "acked" },
    { from: "fetched", on: "rollback", to: "queued" },
    { from: "fetched", on: "reclaim", to: "queued" },
  ],
};

/** Forum: an append-only, provenance-carrying post log. */
export const FORUM_MACHINE: MachineSpec = {
  name: "ForumMachine",
  role: "append-only threaded log",
  states: ["empty", "posted"],
  edges: [{ from: "empty", on: "post", to: "posted" }],
};

/** Every machine in the product. */
export const ALL_MACHINES: readonly MachineSpec[] = [
  REGISTRY_MACHINE,
  BINDING_MACHINE,
  MAILBOX_MACHINE,
  MESSAGE_MACHINE,
  FORUM_MACHINE,
];

/** The action names contributed by each machine. */
export const ACTIONS_BY_MACHINE: Readonly<Record<string, readonly BoardAction[]>> = {
  RegistryMachine: ["register"],
  BindingMachine: ["bind", "unbind"],
  MailboxMachine: ["send", "recv", "ack", "rollback", "reclaim"],
  MessageMachine: ["send", "recv", "ack", "rollback", "reclaim"],
  ForumMachine: ["post"],
};

/** The union of all machine actions, filtered to the model alphabet. */
export function coveredActions(): BoardAction[] {
  const covered = new Set<BoardAction>();
  for (const machine of ALL_MACHINES) for (const edge of machine.edges) covered.add(edge.on);
  return BOARD_ACTIONS.filter((action) => covered.has(action));
}

/** Validate that a machine's edges are internally consistent. */
export function machineErrors(machine: MachineSpec): string[] {
  const errors: string[] = [];
  const states = new Set(machine.states);
  for (const edge of machine.edges) {
    if (!states.has(edge.from)) errors.push(`${machine.name}: unknown from ${edge.from}`);
    if (!states.has(edge.to)) errors.push(`${machine.name}: unknown to ${edge.to}`);
  }
  return errors;
}
