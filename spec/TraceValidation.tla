------------------------- MODULE TraceValidation --------------------------
\* Replay implementation traces against the verified named-mailbox machine.
\* `spec/generated/TracesData.tla` defines `Traces`; each trace step names an
\* action and the state the model should be in afterwards. A disabled action
\* sets `error`, rejected by `TraceInv` with a counterexample naming the step.
\* -------------------------------------------------------------------------

EXTENDS MessageBoard, TracesData, Naturals, Sequences, FiniteSets

VARIABLES traceNo, traceIndex, error

Trace == Traces[traceNo]

state ==
    [ registered |-> registered, bound |-> bound, owner |-> owner,
      sender |-> sender, origin |-> origin, recipient |-> recipient,
      sentAt |-> sentAt, mstatus |-> mstatus, mailbox |-> mailbox,
      lease |-> lease, pstatus |-> pstatus, author |-> author,
      porigin |-> porigin, parent |-> parent, topic |-> topic,
      posted |-> posted, clock |-> clock ]

machineVars == <<registered, bound, owner, sender, origin, recipient, sentAt,
                mstatus, mailbox, lease, pstatus, author, porigin, parent,
                topic, posted, clock>>

ActionOf(ev) ==
    \/ (ev.type = "register" /\ Register(ev.agent))
    \/ (ev.type = "bind"     /\ Bind(ev.agent, ev.box))
    \/ (ev.type = "unbind"   /\ Unbind(ev.agent))
    \/ (ev.type = "send"     /\ Send(ev.agent, ev.box, ev.message))
    \/ (ev.type = "recv"     /\ Recv(ev.agent, ev.box, ev.message))
    \/ (ev.type = "ack"      /\ Ack(ev.agent, ev.box, ev.message))
    \/ (ev.type = "rollback" /\ Rollback(ev.agent, ev.box))
    \/ (ev.type = "reclaim"  /\ Reclaim(ev.box))
    \/ (ev.type = "post"     /\ Post(ev.agent, ev.post, ev.topic, ev.parent))

GuardOf(ev) ==
    \/ (ev.type = "register" /\ GuardRegister(ev.agent))
    \/ (ev.type = "bind"     /\ GuardBind(ev.agent, ev.box))
    \/ (ev.type = "unbind"   /\ GuardUnbind(ev.agent))
    \/ (ev.type = "send"     /\ GuardSend(ev.agent, ev.box, ev.message))
    \/ (ev.type = "recv"     /\ GuardRecv(ev.agent, ev.box, ev.message))
    \/ (ev.type = "ack"      /\ GuardAck(ev.agent, ev.box, ev.message))
    \/ (ev.type = "rollback" /\ GuardRollback(ev.agent, ev.box))
    \/ (ev.type = "reclaim"  /\ GuardReclaim(ev.box))
    \/ (ev.type = "post"     /\ GuardPost(ev.agent, ev.post, ev.topic, ev.parent))

AssignState(s) ==
    /\ registered = s.registered
    /\ bound = s.bound
    /\ owner = s.owner
    /\ sender = s.sender
    /\ origin = s.origin
    /\ recipient = s.recipient
    /\ sentAt = s.sentAt
    /\ mstatus = s.mstatus
    /\ mailbox = s.mailbox
    /\ lease = s.lease
    /\ pstatus = s.pstatus
    /\ author = s.author
    /\ porigin = s.porigin
    /\ parent = s.parent
    /\ topic = s.topic
    /\ posted = s.posted
    /\ clock = s.clock

TraceInit ==
    /\ traceNo \in 1..Len(Traces)
    /\ traceIndex = 1
    /\ error = FALSE
    /\ AssignState(Trace[1].state)

TraceStep ==
    LET ev == Trace[traceIndex + 1].event IN
      \/ (GuardOf(ev) /\ ActionOf(ev) /\ UNCHANGED error)
      \/ (~GuardOf(ev) /\ UNCHANGED machineVars /\ error' = TRUE)

TraceNext ==
    \/ /\ traceIndex < Len(Trace)
       /\ TraceStep
       /\ traceIndex' = traceIndex + 1
       /\ UNCHANGED traceNo
    \/ /\ traceIndex = Len(Trace)
       /\ UNCHANGED <<machineVars, traceNo, traceIndex, error>>

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<machineVars, traceNo, traceIndex, error>>

TraceInv ==
    /\ error = FALSE
    /\ (traceIndex > 0 => state = Trace[traceIndex].state)

=============================================================================
