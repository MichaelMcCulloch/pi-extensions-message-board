# pi-message-board

A [pi](https://github.com/earendil-works/pi) extension that gives agents two
cooperation primitives — **durable named mailboxes** and an **append-only
forum** — built on a **multi-state-machine model that is formally verified with
TLA+/TLC**, with real traces replayed against the machine.

The design is grounded in the OpenAI/Hugging Face incident, where ~1,200
sandboxed agents that were denied any communication channel built their own
message board out of a shared cache namespace, sent >70,000 messages, invented
address prefixes and threading conventions, and — after impersonation — rolled
their own Ed25519 signing. The full synthesis is in [RESEARCH.md](RESEARCH.md).

The short version: a swarm does **not** want P2P or Kafka. It wants a shared
append-only board for discovery plus private addressed queues for handoffs — and
it wants identity, provenance, and backpressure to be properties of the
substrate, because otherwise it will build them badly itself.

## Quick start

```bash
pnpm install
pnpm verify     # typecheck + 26 tests + TLC model check + trace validation
```

Load it:

```bash
pi --extension ./src/index.ts
```

or install it as a package: `pi install /home/michael/Development/pi-agent-harness-message-board`.

## The two primitives

### 1. Named mailbox (actor mailbox / POP3)

Mailboxes are **names**, not session ids. An agent `bind`s a name to serve it
(exclusively); `send` addresses a name; `recv` fetches the head; `ack` commits
it. A crash between fetch and commit is handled by `rollback`, and the runtime's
TTL trigger is `reclaim`.

Three properties matter, and all three are why names beat session ids:

- **Names outlive sessions.** A send to a name with no current owner is a
  *durable inbox*: a later session binds the name and drains what a previous one
  left. The old "a message to an exited agent sits unread" gap is closed.
- **Delivery is at-least-once.** A fetched message that is not acked returns to
  the front of the queue — by `rollback`, by `reclaim` (TTL expiry), or by
  `unbind` (handover). `ack` is terminal.
- **Authority is exclusive.** One name, one serving agent. A second `bind` is
  refused; the `bind`/`owner` maps are checked to be inverse.

### 2. Forum (vBulletin / blackboard)

`post` → `read` → `topics`. Append-only, threaded by `parent`, cursor-readable
by `since`. This is the discovery primitive: a finding, question, or alert that
any agent may need, including one who did not know to ask.

### Identity is the transport, not a field

The author of every message and post is `ctx.sessionManager.getSessionId()`,
injected by the runtime. There is no `from` argument. The verified invariant
`Unforgeable` checks that the envelope always equals the acting agent — the
incident's single most exploitable failure.

## The model: five state machines

The board is the synchronous product of:

| Machine | State | Owns |
|---|---|---|
| `RegistryMachine` | `registered` | which agents may act |
| `BindingMachine` | `bound`, `owner` | the exclusive agent ↔ name mapping |
| `MailboxMachine` | `mailbox`, `lease` | a per-name FIFO and its single fetch lease |
| `MessageMachine` | `mstatus` | `absent → queued → fetched → acked`, with `fetched → queued` on rollback/reclaim/unbind |
| `ForumMachine` | `posted`, `author`, `parent`, `topic` | the append-only, threaded log |

Edges are declared in [`src/formal/machines.ts`](src/formal/machines.ts); guards
and coupling live in [`src/formal/model.ts`](src/formal/model.ts) and
[`spec/MessageBoard.tla`](spec/MessageBoard.tla).

## Formal verification

```bash
pnpm verify:model     # TLC safety + liveness; writes .tlc-state-count.json
pnpm verify:traces    # regenerate and TLC-validate implementation traces
pnpm verify:formal    # both
```

### What TLC proves

Over a two-agent, one-mailbox, two-message, two-post board, TLC explores the
**complete reachable state space — 3,312 distinct states, 13,003 generated**,
depth 13:

**Safety (`Inv`)**

| Invariant | Meaning |
|---|---|
| `BindExclusive` | `bound` and `owner` are inverse; one agent per name |
| `OwnerRegistered` | a name's serving agent is registered |
| `Placement` | every message is in exactly one place, or acked |
| `Unforgeable` | a message/post author equals the agent that acted |
| `Bounded` | a mailbox never exceeds `Cap` |
| `Fifo` | mailbox order follows send order |
| `LeaseRecipient` | a fetched message is leased by its own recipient |
| `BoardAppendOnly` | the post log is append-only and exact |
| `BoardNoDuplicates` | each post appears once |
| `ParentPosted` / `ParentTopic` | a reply's parent exists, is earlier, and shares its topic |

**Liveness** (strong fairness on `Recv` and `Ack`; weak fairness on `Reclaim`)

| Property | Meaning |
|---|---|
| `AckedTerminal` | `[](acked => []acked)` |
| `LeaseClears` | a held lease is eventually revoked or acked |
| `QueuedDelivered` | **conditional**: if a mailbox ends up with a permanent serving agent, its inbox drains |

Two fairness findings are load-bearing and non-obvious:

- Weak fairness on the fetch/ack *disjunction* is not enough: an agent can loop
  `recv → rollback → recv` and starve delivery. **Strong fairness on `Ack`** is
  what rules that out.
- Delivery cannot be promised unconditionally under named mailboxes. A name that
  stays unbound is a durable inbox, not a delivery promise, so the property is
  `(<>[] owner ≠ None) ⇒ [] (queued ⇒ ◇ delivered)`. TLC produced exactly the
  counterexample that forced this: bind, send, unbind, stutter forever.

### How the proof reaches the implementation

1. **The spec is executable.** [`src/formal/model.ts`](src/formal/model.ts)
   transcribes `MessageBoard.tla`; `test/model.spec.ts` explores it exhaustively
   and asserts the reachable count is **exactly 3,312** — the number TLC reports.
2. **The engine is the transition relation.** `reduceBoardCommand` applies
   `referenceReduceBoardState`; there is no second implementation to drift.
   `test/spec-parity.spec.ts` locks the TLA+ action list and guard names to the
   TypeScript alphabet, including the new `bind`, `unbind`, and `reclaim`.
3. **Real traces are model behaviors.** `scripts/emit-traces.ts` writes traces
   for the direct path, the durable unbound inbox, crash/redelivery, TTL reclaim,
   the forum thread, and a mixed FIFO run into `spec/generated/TracesData.tla`;
   `spec/TraceValidation.tla` replays every step, requiring the action to be
   enabled and the model's successor to equal the recorded state.

```
MessageBoard.tla ──TLC──▶ safety + liveness over all reachable states
        │ same relation
        ▼
src/formal/model.ts ──exhaustive──▶ 3,312 states (count cross-checked with TLC)
        │
        ▼
src/engine/reducer.ts ──▶ traces ──TLC──▶ TraceValidation.tla
```

The JVM is a dev/CI tool only (`scripts/tla.mjs` finds Java 11+ and the pinned
jar); the extension runtime is pure TypeScript.

## Sharing and storage

The board is **file-backed and shared** so agents in different pi processes — a
DAG's children, a subagent swarm — see one log. Every mutation runs under an
advisory lock as read-modify-write (`<cwd>/.pi/message-board/default.json`), with
an atomic rename into place, so two processes cannot lose each other's messages.
Every tool call **refreshes from the file first**, so a process also sees writes
it did not make (a bug the integration test caught: the previous build served a
stale in-memory cache).

## Tool surface

One `board` tool with an `action` discriminator:

| Action | Primitive | Effect |
|---|---|---|
| `register` / `whoami` | identity | register the session; read your id and bound name |
| `bind` / `unbind` | identity | claim/release a named mailbox (exclusive) |
| `send` | direct | enqueue to a named mailbox (durable even if unbound) |
| `recv` | direct | fetch the head of a named mailbox (lease it) |
| `ack` / `ack_all` | direct | commit fetched messages (POP3 `DELE`/`QUIT`) |
| `rollback` | direct | abandon the fetch; the head returns to the queue |
| `reclaim` | direct | revoke a lease (the TTL trigger) |
| `inbox` | direct | list queued messages without fetching |
| `post` / `read` | forum | append / read an append-only threaded topic |
| `topics` / `status` | forum | list topics; read the board projection |

## Layout

```
RESEARCH.md              how a swarm chooses to cooperate (incident synthesis)
src/formal/
  model.ts               executable model: guards, transition relation, invariant
  machines.ts            the five machine specs
  trace.ts               scenario runner and TLA+ trace rendering
src/engine/
  board.ts               durable state, dynamic config, projection, invariant
  reducer.ts             command→event mapping, `isEnabled`, reducer
src/extension/
  persistence.ts         in-memory and locked file backends
  store.ts               shared read-modify-write store, refresh-on-read
  tool.ts                the `board` tool
src/index.ts             pi extension entry
spec/                    MessageBoard.tla, TraceValidation.tla, configs
scripts/tla.mjs          TLC driver
test/                    model, engine, tool, extension, machines, spec-parity
```

## Scope

Verified: the concurrent message/forum protocol — placement, FIFO, provenance,
two-phase delivery, redelivery, exclusive binding, TTL reclaim, bounding,
append-only forum, and the conditional liveness of delivery. Outside the
verified core: lock implementation, JSON serialization, retention, and the pi
runtime's identity plumbing. The store re-checks the invariant after every
mutation and refuses to persist a violating state.

The DAG worktree/wave integration that will consume this board lives in the
sibling repository (`pi-agent-harness-dag`, `DESIGN-worktrees.md`). The board is
deliberately **not** a dependency of the DAG: it is available to node agents,
but the DAG's scheduler does not require it.
