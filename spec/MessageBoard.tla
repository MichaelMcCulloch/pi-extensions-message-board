------------------------------ MODULE MessageBoard ------------------------------
\* The push revision. A message is queued and then either delivered to the
\* recipient's context or failed; both terminal states are absorbing. There is
\* no lease and no ack: the runtime that injects a message commits the delivery,
\* and a failure (expiry, injection error) is reported to the sender. Posting
\* in a topic subscribes the author to it, and only registration gates explicit
\* subscribe/unsubscribe.
\*
\* Machines: Registry, Binding, Mailbox (queue only), Message lifecycle,
\* Subscriptions, plus the append-only Forum. Sync with src/formal/model.ts.
\* --------------------------------------------------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Agents, Boxes, Messages, Posts, Topics, Cap, MaxClock

\* The "no value" sentinel of an option type. It must be FRESH: no agent, box,
\* message, post, or topic may be named "none", or options become ambiguous.
None     == "none"

MStatus == {"absent", "queued", "delivered", "failed"}
PStatus == {"absent", "posted"}

VARIABLES
    registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
    mailbox, subscribed, pstatus, author, porigin, parent, topic, posted, clock

vars == <<registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
          mailbox, subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Members(s) == {s[i] : i \in DOMAIN s}
Occ(m) == {b \in Boxes : m \in Members(mailbox[b])}

TypeOK ==
    /\ registered \in [Agents -> BOOLEAN]
    /\ bound \in [Agents -> Boxes \cup {None}]
    /\ owner \in [Boxes -> Agents \cup {None}]
    /\ sender \in [Messages -> Agents \cup {None}]
    /\ origin \in [Messages -> Agents \cup {None}]
    /\ recipient \in [Messages -> Boxes \cup {None}]
    /\ sentAt \in [Messages -> 0..MaxClock]
    /\ mstatus \in [Messages -> MStatus]
    /\ mailbox \in [Boxes -> Seq(Messages)]
    /\ subscribed \in [Agents -> SUBSET Topics]
    /\ pstatus \in [Posts -> PStatus]
    /\ author \in [Posts -> Agents \cup {None}]
    /\ porigin \in [Posts -> Agents \cup {None}]
    /\ parent \in [Posts -> Posts \cup {None}]
    /\ topic \in [Posts -> Topics \cup {None}]
    /\ posted \in Seq(Posts)
    /\ clock \in 0..MaxClock

Init ==
    /\ registered = [a \in Agents |-> FALSE]
    /\ bound = [a \in Agents |-> None]
    /\ owner = [b \in Boxes |-> None]
    /\ sender = [m \in Messages |-> None]
    /\ origin = [m \in Messages |-> None]
    /\ recipient = [m \in Messages |-> None]
    /\ sentAt = [m \in Messages |-> 0]
    /\ mstatus = [m \in Messages |-> "absent"]
    /\ mailbox = [b \in Boxes |-> <<>>]
    /\ subscribed = [a \in Agents |-> {}]
    /\ pstatus = [p \in Posts |-> "absent"]
    /\ author = [p \in Posts |-> None]
    /\ porigin = [p \in Posts |-> None]
    /\ parent = [p \in Posts |-> None]
    /\ topic = [p \in Posts |-> None]
    /\ posted = <<>>
    /\ clock = 0

\* ---------------------------------------------------------------------------
\* Guards
\* ---------------------------------------------------------------------------

GuardRegister(a) == ~registered[a]
GuardBind(a, b) == registered[a] /\ bound[a] = None /\ owner[b] = None
GuardUnbind(a) == registered[a] /\ bound[a] # None
GuardSend(s, b, m) == registered[s] /\ mstatus[m] = "absent" /\ Len(mailbox[b]) < Cap /\ clock < MaxClock
GuardDeliver(a, b, m) ==
    /\ registered[a] /\ bound[a] = b /\ owner[b] = a
    /\ mstatus[m] = "queued" /\ Len(mailbox[b]) > 0 /\ Head(mailbox[b]) = m
\* A failure has no acting agent: the runtime triggers it on expiry or when
\* injection throws. Only the head can fail, so the queue stays a queue.
GuardFail(b, m) ==
    /\ mstatus[m] = "queued" /\ recipient[m] = b
    /\ Len(mailbox[b]) > 0 /\ Head(mailbox[b]) = m
GuardSubscribe(a, t) == registered[a] /\ t \in Topics /\ t \notin subscribed[a]
GuardUnsubscribe(a, t) == registered[a] /\ t \in subscribed[a]
GuardPost(a, p, t, par) ==
    /\ registered[a] /\ pstatus[p] = "absent" /\ t \in Topics
    /\ (par = None \/ (par \in Posts /\ pstatus[par] = "posted" /\ topic[par] = t))

\* ---------------------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------------------

Register(a) ==
    /\ GuardRegister(a)
    /\ registered' = [registered EXCEPT ![a] = TRUE]
    /\ UNCHANGED <<bound, owner, sender, origin, recipient, sentAt, mstatus,
                   mailbox, subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Bind(a, b) ==
    /\ GuardBind(a, b)
    /\ bound' = [bound EXCEPT ![a] = b]
    /\ owner' = [owner EXCEPT ![b] = a]
    /\ UNCHANGED <<registered, sender, origin, recipient, sentAt, mstatus,
                   mailbox, subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Unbind(a) ==
    /\ GuardUnbind(a)
    /\ LET b == bound[a] IN
       /\ bound' = [bound EXCEPT ![a] = None]
       /\ owner' = [owner EXCEPT ![b] = None]
    /\ UNCHANGED <<registered, sender, origin, recipient, sentAt, mstatus,
                   mailbox, subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Send(s, b, m) ==
    /\ GuardSend(s, b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "queued"]
    /\ sender' = [sender EXCEPT ![m] = s]
    /\ origin' = [origin EXCEPT ![m] = s]
    /\ recipient' = [recipient EXCEPT ![m] = b]
    /\ sentAt' = [sentAt EXCEPT ![m] = clock + 1]
    /\ mailbox' = [mailbox EXCEPT ![b] = Append(mailbox[b], m)]
    /\ clock' = clock + 1
    /\ UNCHANGED <<registered, bound, owner, subscribed, pstatus, author, porigin, parent, topic, posted>>

Deliver(a, b, m) ==
    /\ GuardDeliver(a, b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "delivered"]
    /\ mailbox' = [mailbox EXCEPT ![b] = Tail(mailbox[b])]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Fail(b, m) ==
    /\ GuardFail(b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "failed"]
    /\ mailbox' = [mailbox EXCEPT ![b] = Tail(mailbox[b])]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   subscribed, pstatus, author, porigin, parent, topic, posted, clock>>

Subscribe(a, t) ==
    /\ GuardSubscribe(a, t)
    /\ subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \cup {t}]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   mstatus, mailbox, pstatus, author, porigin, parent, topic, posted, clock>>

Unsubscribe(a, t) ==
    /\ GuardUnsubscribe(a, t)
    /\ subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \ {t}]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   mstatus, mailbox, pstatus, author, porigin, parent, topic, posted, clock>>

\* Voice in a topic subscribes the author: participation is the default watch.
Post(a, p, t, par) ==
    /\ GuardPost(a, p, t, par)
    /\ pstatus' = [pstatus EXCEPT ![p] = "posted"]
    /\ author' = [author EXCEPT ![p] = a]
    /\ porigin' = [porigin EXCEPT ![p] = a]
    /\ parent' = [parent EXCEPT ![p] = par]
    /\ topic' = [topic EXCEPT ![p] = t]
    /\ posted' = Append(posted, p)
    /\ subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \cup {t}]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   mstatus, mailbox, clock>>

Next ==
    \/ \E a \in Agents: Register(a)
    \/ \E a \in Agents, b \in Boxes: Bind(a, b)
    \/ \E a \in Agents: Unbind(a)
    \/ \E s \in Agents, b \in Boxes, m \in Messages: Send(s, b, m)
    \/ \E a \in Agents, b \in Boxes, m \in Messages: Deliver(a, b, m)
    \/ \E b \in Boxes, m \in Messages: Fail(b, m)
    \/ \E a \in Agents, t \in Topics: Subscribe(a, t)
    \/ \E a \in Agents, t \in Topics: Unsubscribe(a, t)
    \/ \E a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Post(a, p, t, par)

\* ---------------------------------------------------------------------------
\* Safety
\* ---------------------------------------------------------------------------

BoundConsistent ==
    \A a \in Agents: (bound[a] # None => owner[bound[a]] = a)

OwnerConsistent ==
    \A b \in Boxes: (owner[b] # None => bound[owner[b]] = b /\ registered[owner[b]])

\* Every message is in exactly one place, or settled; delivery never changes
\* authorship; a sent message was sent at or before the current clock.
MessageStatus ==
    \A m \in Messages:
         /\ (mstatus[m] = "absent"    => Cardinality(Occ(m)) = 0)
         /\ (mstatus[m] = "queued"    => Cardinality(Occ(m)) = 1)
         /\ (mstatus[m] = "delivered" => Cardinality(Occ(m)) = 0)
         /\ (mstatus[m] = "failed"    => Cardinality(Occ(m)) = 0)
         /\ Cardinality(Occ(m)) <= 1
         /\ (mstatus[m] # "absent" => sender[m] = origin[m])
         /\ (mstatus[m] # "absent" => sentAt[m] <= clock)

MailboxInv ==
    \A b \in Boxes:
         /\ Len(mailbox[b]) <= Cap
         /\ \A i \in DOMAIN mailbox[b]: recipient[mailbox[b][i]] = b
         \* Needed by Deliver and Fail: the head is removed, never the middle,
         \* so the mailbox stays sorted by send order.
         /\ \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]

\* Only registered agents hold subscriptions.
SubsRegistered ==
    \A a \in Agents: registered[a] \/ subscribed[a] = {}

PostsInv ==
    \A p \in Posts:
         /\ (pstatus[p] = "posted" => author[p] = porigin[p])
         /\ (parent[p] = None \/ (parent[p] \in Posts /\
               pstatus[parent[p]] = "posted" /\ topic[parent[p]] = topic[p] /\
               \E i, j \in DOMAIN posted: i < j /\ posted[i] = parent[p] /\ posted[j] = p))

PostedDistinct ==
    \A i, j \in DOMAIN posted: i # j => posted[i] # posted[j]

PostedMembership ==
    \A p \in Posts: (pstatus[p] = "posted") <=> (p \in Members(posted))

Inv == TypeOK /\ BoundConsistent /\ OwnerConsistent /\ MessageStatus
       /\ MailboxInv /\ SubsRegistered /\ PostsInv /\ PostedDistinct /\ PostedMembership

\* ---------------------------------------------------------------------------
\* Liveness
\* ---------------------------------------------------------------------------

\* Delivery and failure are terminal.
DeliveredTerminal == \A m \in Messages: [] (mstatus[m] = "delivered" => [] (mstatus[m] = "delivered"))
FailedTerminal == \A m \in Messages: [] (mstatus[m] = "failed" => [] (mstatus[m] = "failed"))
\* The runtime keeps working: a queued message is eventually delivered or
\* reported failed. Which of the two is a runtime policy (expiry, injection
\* error), not a property of the protocol.
QueuedSettles ==
    \A m \in Messages: [](mstatus[m] = "queued" => <>(mstatus[m] \in {"delivered", "failed"}))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A a \in Agents, b \in Boxes, m \in Messages: WF_vars(Deliver(a, b, m))
    /\ \A b \in Boxes, m \in Messages: WF_vars(Fail(b, m))

=============================================================================
