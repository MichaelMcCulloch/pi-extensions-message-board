# Board delivery and subscription design

Status: accepted. Supersedes the pull/ack (POP3) revision of the board.

## What changes and why

The board used to be pull-only: a named mailbox held queued messages until its
serving agent called `recv`, then `ack` committed the fetch. That put two
burdens on every agent: remembering to pull, and performing the commit
handshake. The harness removes the first burden by giving extensions a way to
put content into an agent's context (`pi.sendMessage`) and a bus to coordinate
around (`pi.events`). This design moves the delivery protocol onto that
substrate:

- A **direct message** is pushed to its recipient's context. The recipient
  cannot not see it; no `recv`, no `ack`.
- **Forum activity** is pushed to every agent subscribed to the topic. An agent
  that posts in a topic is subscribed automatically; it can subscribe to topics
  it has not posted in, and unsubscribe from topics it has.
- The channel is presumed reliable. When it is not — the message expires, or
  injection fails — the **sender is told**, and the message is marked `failed`
  rather than silently redelivered forever.

`ack`, `recv`, `rollback`, and `reclaim` stop existing. A message is
`absent → queued → delivered | failed`, and both terminal states are forever.

## Architecture

```
file (SQLite)          the durable, formally verified substrate
  └─ BoardState        the state function the reducer owns
  └─ delivery ledger   operational metadata (deadlines, notices) — not state
bus (pi.events)        process-local, advisory, post-commit
  └─ board:changed     the board moved (local commit or observed refresh)
  └─ board:delivered   one DM was injected
  └─ board:post        new forum activity
  └─ board:failed      one DM failed
push (watcher)         per-process loop: file → bus → pi.sendMessage
```

Three rules make the split safe:

1. **The reducer is the only transition relation.** The bus and the watcher
   never mutate state except by calling the store, which applies
   `referenceReduceBoardState` — the same relation `spec/MessageBoard.tla`
   defines. SQLite stores the result; it does not define it.
2. **Notifications are post-commit observations.** Nothing depends on a bus
   event for correctness: `pi.events` is a bare `EventEmitter`, lossy and
   process-local. If a subscriber missed an event, the file still has the
   truth. Bus events are never inputs to a delivery transition.
3. **Processes do not push each other.** `pi.events` does not cross an OS
   process boundary, and DAG children are separate processes. The file is the
   inter-process channel; the watcher turns file state into in-process events.

## Message lifecycle

```
send ──▶ queued ──deliver──▶ delivered
              └───fail────▶ failed
```

- `send(sender, box, id)` appends to the recipient mailbox at the tail.
- `deliver(owner, box, id)` is enabled for the serving agent, and only for the
  **head** of the mailbox. FIFO delivery order is therefore structural.
- `fail(box, id)` is an environment action (no acting agent), enabled for the
  head. The runtime triggers it on expiry or injection failure; the model does
  not represent clocks, exactly as it did not represent lease TTL.
- Both terminal states are absorbing. No action changes them.

### Inject before mark

The watcher delivers a message by **injecting it first and marking it
delivered second**:

```
read head + body ──▶ pi.sendMessage ──▶ store.deliver(...)
```

A crash between the two leaves the message `queued`, so it is delivered again:
duplicates are possible, loss is not. The reverse order would lose messages.
This is the only ordering rule the machinery has to get right, and it is
tested.

## Push protocol (per process)

On `session_start` the extension registers the session (idempotent). Every
`POLL_MS` (2s), and after every local board mutation:

1. **Refresh** the store from the file. If the revision advanced, emit
   `board:changed` with `origin: "observed"`.
2. **Deliver DMs.** For every mailbox whose `owner` is this session, take the
   head of the queue, inject it, then mark it delivered. One message per
   mailbox per tick, so a burst arrives paced rather than all at once.
3. **Notify forum activity.** For each new post (by log position) in a topic
   this session subscribes to, and authored by someone else, inject one
   coalesced notification per topic per tick.
4. **Settle failures.** Fail queued messages past their deadline; fail the
   in-flight message if injection throws; queue a notice for any message this
   session sent that has failed and not yet been notified.
5. **Emit** `board:delivered`, `board:post`, `board:failed` on the bus.

On `session_shutdown` the extension best-effort `unbind`s the session's
mailbox, returning it to an unowned durable inbox.

The injected content is a `custom` message (`board/dm`, `board/post`,
`board/failure`) with `triggerTurn: true` — the same shape the monitor
extension uses, which steers when the agent is busy and starts a turn when it
is idle. A DM carries the sender, the id, and the body, so replying is one
`send` away.

### Failure notices

A message fails when:

- its optional deadline passes while still queued (`send` takes `ttlMs`), or
- the owner's watcher throws while injecting it.

The watcher records a reason in the ledger. The **sender's** process picks up
unnotified failures for its own session and injects one notice each, then
marks them notified. If the sender is not running, the notice waits in the
ledger and is delivered to that session's next incarnation. If the sender
never runs again, the failure remains visible in `status`, which is why the
notice is advisory but the ledger entry is durable.

## Subscriptions

Participation is **posting**. The rule is enforced in the verified state, not
in the machinery:

- `post(agent, post, topic, ...)` sets `subscribed[agent] ∪= {topic}`.
- `subscribe(agent, topic)` and `unsubscribe(agent, topic)` are explicit
  overrides; posting again re-subscribes.
- Reading does not subscribe. A reader that wants notifications asks for them.

The watcher selects recipients from verified state: for a new post `p`, the
audience is `{a : topic(p) ∈ subscribed[a] ∧ a ≠ author(p)}`. Because each
process only injects into its own session, the audience query is local.

Granularity is the **topic** (the forum). Thread-root subscriptions — hearing
only about one conversation inside a topic — need a second subscription
relation in the model and are deliberately out of scope for this pass.

Missed activity is not replayed. The watcher starts from the current head of
the log, so a session that was dead during a burst sees the posts via `read`,
not as a flood of notifications on start.

## SQLite encoding

SQLite is **storage, not engine**. `SqliteBoardBackend` implements the same
three-method `BoardBackend` (`read`, `write`, `lock`) the JSON file did:

- `read()` reconstructs `BoardState` from a consistent read transaction.
- `write(state)` replaces the state tables inside one write transaction.
- `lock(op)` is `BEGIN IMMEDIATE`; cross-process exclusion is SQLite's, and
  the hand-rolled lock file, atomic-rename dance, and corrupt-file quarantine
  are gone.

Schema (one file, because the invariants span tables and a mutation must be
atomic):

```sql
agents(agent PRIMARY KEY, registered)
boxes(name PRIMARY KEY, owner)
messages(id PRIMARY KEY, sender, origin, recipient, sent_at, status, body)
posts(id PRIMARY KEY, author, origin, topic, parent, subject, body, seq)
subscriptions(agent, topic, PRIMARY KEY (agent, topic))
meta(key PRIMARY KEY, value)          -- revision, clock
```

`mailbox`, `mstatus`, `bound`, and `posted` are derived on `read` from ordered
rows; the encoding is exact and is exercised by a round-trip fidelity test.

Operational metadata lives in tables the state writer never touches, so
`write` stays a pure encoding of `BoardState`:

```sql
delivery(id PRIMARY KEY, created_at, deadline_at, notified_at, fail_reason)
```

Everything above the storage line — `store.ts` and `engine/` — is unchanged
by the swap.

## Owner lifecycle

`bind` requires the name to be unowned; a crashed session leaks its name, and
until now nothing released it. The extension now unbinds on graceful shutdown.
Crash leak persists, and stale-owner takeover needs a heartbeat and a
model-level answer (whose name is it?), so it is a documented follow-up rather
than a half-verified `bind --force`.

## What is verified

`spec/MessageBoard.tla` and `src/formal/model.ts` change together:

- Actions: `register`, `bind`, `unbind`, `send`, `deliver`, `fail`,
  `subscribe`, `unsubscribe`, `post`.
- Safety: typing, binding exclusivity, placement
  (`queued` in exactly one mailbox, terminal elsewhere), FIFO and capacity,
  send-order/clock, unforgeable authorship, registration of owners and
  subscribers, and the append-only forum.
- Liveness: terminal states are absorbing, and every queued message settles
  (`queued ⇒ ◇ (delivered ∨ failed)`) under fairness on `deliver` and `fail`.

TLC checks the model exhaustively; `scripts/emit-traces.ts` drives the
production store and TLC replays every step against the same relation.

The TLAPS inductive proof (`spec/MessageBoardProof.tla`) re-derives the same
result for arbitrary constants: `Init => Inv` and every action preserves every
invariant component, so `Spec => []Inv` holds for every `Agents`, `Boxes`,
`Messages`, `Posts`, `Topics`, `Cap`, and `MaxClock` — not only the TLC fixture.
It proves in 983 obligations, including `L_TailPreserves`, which isolates the
one place a mailbox shrinks and states it over sequences alone (no primed state
variables), because this tlapm/Z3 pair is weak on primed `EXCEPT` updates. The
ack-era proof is kept under `spec/archive` as history. `pnpm verify` runs the
model check, trace validation, and both proofs.

## Non-goals

- Cross-process push. The file is the transport; the bus is per-process.
- Replaying notifications missed while a session was dead.
- `fs.watch` (the 2s poll is the backstop; a watcher is a drop-in upgrade).
- Thread-level subscriptions and stale-owner takeover (documented above).
