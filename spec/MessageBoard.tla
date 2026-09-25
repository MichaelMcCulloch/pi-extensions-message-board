------------------------------ MODULE MessageBoard ------------------------------
\* The named-mailbox revision: mailboxes are named, an agent binds a name to
\* serve it, and a lease may be reclaimed (the runtime triggers reclaim on TTL
\* expiry). Binding decouples delivery from a session id, so a fresh session can
\* drain a mailbox a previous session left; reclaim means a fetched-but-unacked
\* message is never stranded when its consumer dies.
\*
\* Four machines: Registry, Binding, Mailbox (queue + lease), Message lifecycle,
\* plus the append-only Forum. Sync with src/formal/model.ts.
\* --------------------------------------------------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Cap, MaxClock

Agents   == {"a1", "a2"}
Boxes    == {"bx1"}
Messages == {"m1", "m2"}
Posts    == {"p1", "p2"}
Topics   == {"t1"}
None     == "none"

MStatus == {"absent", "queued", "fetched", "acked"}
PStatus == {"absent", "posted"}

VARIABLES
    registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
    mailbox, lease, pstatus, author, porigin, parent, topic, posted, clock

vars == <<registered, bound, owner, sender, origin, recipient, sentAt, mstatus,
          mailbox, lease, pstatus, author, porigin, parent, topic, posted, clock>>

Members(s) == {s[i] : i \in DOMAIN s}
Occ(m) == {b \in Boxes : m \in Members(mailbox[b])}
Lea(m) == {b \in Boxes : lease[b] = m}

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
    /\ lease \in [Boxes -> Messages \cup {None}]
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
    /\ lease = [b \in Boxes |-> None]
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
GuardRecv(a, b, m) ==
    /\ registered[a] /\ bound[a] = b /\ owner[b] = a
    /\ lease[b] = None /\ Len(mailbox[b]) > 0 /\ Head(mailbox[b]) = m /\ mstatus[m] = "queued"
GuardAck(a, b, m) == bound[a] = b /\ owner[b] = a /\ lease[b] = m /\ mstatus[m] = "fetched"
GuardRollback(a, b) == bound[a] = b /\ owner[b] = a /\ lease[b] # None
GuardReclaim(b) == lease[b] # None
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
                   mailbox, lease, pstatus, author, porigin, parent, topic, posted, clock>>

Bind(a, b) ==
    /\ GuardBind(a, b)
    /\ bound' = [bound EXCEPT ![a] = b]
    /\ owner' = [owner EXCEPT ![b] = a]
    /\ UNCHANGED <<registered, sender, origin, recipient, sentAt, mstatus,
                   mailbox, lease, pstatus, author, porigin, parent, topic, posted, clock>>

Unbind(a) ==
    /\ GuardUnbind(a)
    /\ LET b == bound[a] IN
       /\ mstatus' = IF lease[b] = None THEN mstatus ELSE [mstatus EXCEPT ![lease[b]] = "queued"]
       /\ mailbox' = [mailbox EXCEPT ![b] = IF lease[b] = None THEN mailbox[b] ELSE <<lease[b]>> \o mailbox[b]]
       /\ bound' = [bound EXCEPT ![a] = None]
       /\ owner' = [owner EXCEPT ![b] = None]
       /\ lease' = [lease EXCEPT ![b] = None]
    /\ UNCHANGED <<registered, sender, origin, recipient, sentAt,
                   pstatus, author, porigin, parent, topic, posted, clock>>

Send(s, b, m) ==
    /\ GuardSend(s, b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "queued"]
    /\ sender' = [sender EXCEPT ![m] = s]
    /\ origin' = [origin EXCEPT ![m] = s]
    /\ recipient' = [recipient EXCEPT ![m] = b]
    /\ sentAt' = [sentAt EXCEPT ![m] = clock + 1]
    /\ mailbox' = [mailbox EXCEPT ![b] = Append(mailbox[b], m)]
    /\ clock' = clock + 1
    /\ UNCHANGED <<registered, bound, owner, lease, pstatus, author, porigin, parent, topic, posted>>

Recv(a, b, m) ==
    /\ GuardRecv(a, b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "fetched"]
    /\ mailbox' = [mailbox EXCEPT ![b] = Tail(mailbox[b])]
    /\ lease' = [lease EXCEPT ![b] = m]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   pstatus, author, porigin, parent, topic, posted, clock>>

Ack(a, b, m) ==
    /\ GuardAck(a, b, m)
    /\ mstatus' = [mstatus EXCEPT ![m] = "acked"]
    /\ lease' = [lease EXCEPT ![b] = None]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   mailbox, pstatus, author, porigin, parent, topic, posted, clock>>

Rollback(a, b) ==
    /\ GuardRollback(a, b)
    /\ LET m == lease[b] IN
       /\ mstatus' = [mstatus EXCEPT ![m] = "queued"]
       /\ mailbox' = [mailbox EXCEPT ![b] = <<m>> \o mailbox[b]]
    /\ lease' = [lease EXCEPT ![b] = None]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   pstatus, author, porigin, parent, topic, posted, clock>>

Reclaim(b) ==
    /\ GuardReclaim(b)
    /\ LET m == lease[b] IN
       /\ mstatus' = [mstatus EXCEPT ![m] = "queued"]
       /\ mailbox' = [mailbox EXCEPT ![b] = <<m>> \o mailbox[b]]
    /\ lease' = [lease EXCEPT ![b] = None]
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   pstatus, author, porigin, parent, topic, posted, clock>>

Post(a, p, t, par) ==
    /\ GuardPost(a, p, t, par)
    /\ pstatus' = [pstatus EXCEPT ![p] = "posted"]
    /\ author' = [author EXCEPT ![p] = a]
    /\ porigin' = [porigin EXCEPT ![p] = a]
    /\ parent' = [parent EXCEPT ![p] = par]
    /\ topic' = [topic EXCEPT ![p] = t]
    /\ posted' = Append(posted, p)
    /\ UNCHANGED <<registered, bound, owner, sender, origin, recipient, sentAt,
                   mstatus, mailbox, lease, clock>>

Next ==
    \/ \E a \in Agents: Register(a)
    \/ \E a \in Agents, b \in Boxes: Bind(a, b)
    \/ \E a \in Agents: Unbind(a)
    \/ \E s \in Agents, b \in Boxes, m \in Messages: Send(s, b, m)
    \/ \E a \in Agents, b \in Boxes, m \in Messages: Recv(a, b, m)
    \/ \E a \in Agents, b \in Boxes, m \in Messages: Ack(a, b, m)
    \/ \E a \in Agents, b \in Boxes: Rollback(a, b)
    \/ \E b \in Boxes: Reclaim(b)
    \/ \E a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Post(a, p, t, par)

\* ---------------------------------------------------------------------------
\* Safety
\* ---------------------------------------------------------------------------

Inv ==
    /\ TypeOK
    /\ \A a \in Agents: (bound[a] # None => owner[bound[a]] = a)
    /\ \A b \in Boxes: (owner[b] # None => bound[owner[b]] = b /\ registered[owner[b]])
    /\ \A m \in Messages:
         /\ (mstatus[m] = "absent"  => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 0)
         /\ (mstatus[m] = "queued"  => Cardinality(Occ(m)) = 1 /\ Cardinality(Lea(m)) = 0)
         /\ (mstatus[m] = "fetched" => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 1)
         /\ (mstatus[m] = "acked"   => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 0)
         /\ Cardinality(Occ(m)) + Cardinality(Lea(m)) <= 1
         /\ (mstatus[m] # "absent" => sender[m] = origin[m])
    /\ \A b \in Boxes:
         /\ Len(mailbox[b]) <= Cap
         /\ (lease[b] = None \/ (lease[b] \in Messages /\ mstatus[lease[b]] = "fetched" /\ recipient[lease[b]] = b))
         /\ \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]
    /\ \A p \in Posts:
         /\ (pstatus[p] = "posted" => author[p] = porigin[p])
         /\ (parent[p] = None \/ (parent[p] \in Posts /\
               pstatus[parent[p]] = "posted" /\ topic[parent[p]] = topic[p] /\
               \E i, j \in DOMAIN posted: i < j /\ posted[i] = parent[p] /\ posted[j] = p))
    /\ \A i, j \in DOMAIN posted: i # j => posted[i] # posted[j]
    /\ \A p \in Posts: (pstatus[p] = "posted") <=> (p \in Members(posted))

\* ---------------------------------------------------------------------------
\* Liveness
\* ---------------------------------------------------------------------------

AckedTerminal == \A m \in Messages: [] (mstatus[m] = "acked" => [] (mstatus[m] = "acked"))
LeaseClears == \A b \in Boxes: [] (lease[b] # None => <> (lease[b] = None))
\* If a mailbox ends up with a permanent serving agent, its inbox drains.
\* A name that stays unbound is a durable inbox, not a delivery promise.
QueuedDelivered ==
    \A b \in Boxes:
        (<>[] (owner[b] # None)) =>
        ([] (owner[b] # None =>
              \A m \in Messages:
                  (recipient[m] = b /\ mstatus[m] = "queued"
                   => <> (mstatus[m] \in {"fetched", "acked"}))))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A b \in Boxes: WF_vars(Reclaim(b))
    /\ \A a \in Agents, b \in Boxes, m \in Messages: SF_vars(Recv(a, b, m))
    /\ \A a \in Agents, b \in Boxes, m \in Messages: SF_vars(Ack(a, b, m))

=============================================================================
