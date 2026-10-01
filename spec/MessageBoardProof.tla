---------------------- MODULE MessageBoardProof ----------------------
\* The inductive safety proof for the parameterized push-revision board.
\*
\* `Init => Inv` and every action preserves every invariant component, so
\* `Spec => []Inv` holds for arbitrary constants, not only the TLC fixture.
\*
\* From spec/: tlapm --threads 4 -I "$HOME/.local/tlapm/lib/tlapm/stdlib" MessageBoardProof.tla
\* ---------------------------------------------------------------------

EXTENDS MessageBoard, TLAPS, FiniteSetTheorems, SequenceTheorems

\* ---------------------------------------------------------------------------
\* Helper lemmas: the sequence/cardinality algebra the action proofs need.
\* ---------------------------------------------------------------------------

LEMMA L_EmptyMembers == Members(<<>>) = {}
  BY SMT DEF Members

LEMMA L_MembersRange == ASSUME NEW q \in Seq(Messages)
  PROVE Members(q) = Range(q)
  BY SMT DEF Members, Range

LEMMA L_MembersAppend == ASSUME NEW q \in Seq(Messages), NEW m \in Messages
  PROVE Members(Append(q, m)) = Members(q) \cup {m}
  <1>1. Members(q) = Range(q) BY SMT DEF Members, Range
  <1>2. Members(Append(q, m)) = Range(Append(q, m)) BY SMT DEF Members, Range
  <1>3. Range(Append(q, m)) = Range(q) \cup {m} BY SMT, AppendProperties
  <1>4. QED BY SMT, <1>1, <1>2, <1>3

LEMMA L_MembersTail == ASSUME NEW q \in Seq(Messages), IsInjective(q), q # <<>>
  PROVE Members(Tail(q)) = Members(q) \ {Head(q)}
  <1>1. Range(Tail(q)) = Range(q) \ {Head(q)} BY SMT, TailInjectiveSeq
  <1>2. Members(Tail(q)) = Range(Tail(q)) BY SMT DEF Members, Range
  <1>3. Members(q) = Range(q) BY SMT DEF Members, Range
  <1>4. QED BY SMT, <1>1, <1>2, <1>3

LEMMA L_HeadNotInTail == ASSUME NEW q \in Seq(Messages), IsInjective(q), q # <<>>
  PROVE Head(q) \notin Members(Tail(q))
  <1>1. Range(Tail(q)) = Range(q) \ {Head(q)} BY SMT, TailInjectiveSeq
  <1>2. Members(Tail(q)) = Range(Tail(q)) BY SMT DEF Members, Range
  <1>3. QED BY SMT, <1>1, <1>2

LEMMA L_SortedInjective ==
  ASSUME NEW q \in Seq(Messages), \A i, j \in DOMAIN q: i < j => sentAt[q[i]] < sentAt[q[j]]
  PROVE IsInjective(q)
  <1>1. SUFFICES ASSUME NEW i \in DOMAIN q, NEW j \in DOMAIN q, q[i] = q[j] PROVE i = j
    BY SMT DEF IsInjective
  <1>2. i < j => FALSE BY SMT, <1>1
  <1>3. j < i => FALSE BY SMT, <1>1
  <1>4. QED BY SMT, <1>2, <1>3

LEMMA L_Card0Empty == ASSUME IsFiniteSet(Boxes), NEW S \in SUBSET Boxes, Cardinality(S) = 0
  PROVE S = {}
  <1>1. IsFiniteSet(S) BY SMT, FS_Subset
  <1>2. QED BY SMT, <1>1, FS_EmptySet

LEMMA L_Card0NotMember == ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages, NEW b \in Boxes,
    Cardinality(Occ(m)) = 0
  PROVE m \notin Members(mailbox[b])
  <1>1. Occ(m) \in SUBSET Boxes BY SMT DEF Occ, Members, Range
  <1>2. Occ(m) = {} BY SMT, <1>1, L_Card0Empty
  <1>3. QED BY SMT, <1>2 DEF Occ, Members, Range

LEMMA L_Card1Singleton == ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages, Cardinality(Occ(m)) = 1
  PROVE \E b \in Boxes : Occ(m) = {b}
  <1>1. Occ(m) \in SUBSET Boxes BY SMT DEF Occ, Members, Range
  <1>2. IsFiniteSet(Occ(m)) BY SMT, <1>1, FS_Subset
  <1>3. PICK b : Occ(m) = {b} BY SMT, <1>2, FS_Singleton
  <1>4. b \in Boxes BY SMT, <1>1, <1>3
  <1>5. QED BY SMT, <1>3, <1>4

LEMMA L_UniqueLocation ==
  ASSUME IsFiniteSet(Boxes), NEW S \in SUBSET Boxes,
         Cardinality(S) = 1, NEW b \in S
  PROVE S = {b}
  <1>1. IsFiniteSet(S) BY SMT, FS_Subset
  <1>2. \E x: S = {x} BY SMT, <1>1, FS_Singleton
  <1>3. QED BY SMT, <1>2

\* A settled (absent, delivered, or failed) message occupies no mailbox.
LEMMA L_EmptyPlacements ==
  ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages,
         mstatus[m] \in {"absent", "delivered", "failed"}
  PROVE Occ(m) = {}
  <1>1. Occ(m) \in SUBSET Boxes BY SMT DEF Occ, Members, Range
  <1>2. Cardinality(Occ(m)) = 0 BY SMT DEF Inv, MessageStatus
  <1>3. QED BY SMT, <1>1, <1>2, L_Card0Empty

\* A queued message sits in exactly one mailbox.
LEMMA L_QueuedOcc == ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages, mstatus[m] = "queued",
    NEW b \in Boxes, m \in Members(mailbox[b])
  PROVE Occ(m) = {b}
  <1>1. Occ(m) \in SUBSET Boxes BY SMT DEF Occ, Members, Range
  <1>2. Cardinality(Occ(m)) = 1 BY SMT DEF Inv, MessageStatus
  <1>3. b \in Occ(m) BY SMT DEF Occ
  <1>4. QED BY SMT, <1>1, <1>2, <1>3, L_UniqueLocation

Sorted(q, t) == \A i, j \in DOMAIN q: i < j => t[q[i]] < t[q[j]]

LEMMA L_SortedAppend ==
  ASSUME NEW q \in Seq(Messages), NEW m \in Messages, NEW t,
         Sorted(q, t), \A i \in DOMAIN q: t[q[i]] < t[m]
  PROVE Sorted(Append(q, m), t)
  <1>1. DOMAIN q = 1..Len(q) /\ Len(q) \in Nat
    BY SMT, LenProperties
  <1>2. Append(q, m) \in Seq(Messages) /\ Len(Append(q, m)) = Len(q) + 1
            /\ (\A i \in DOMAIN q: Append(q, m)[i] = q[i])
            /\ Append(q, m)[Len(q)+1] = m
    BY SMT, <1>1, AppendProperties
  <1>3. QED BY SMTT(30), <1>1, <1>2, LenProperties DEF Sorted

LEMMA L_SortedTail ==
  ASSUME NEW q \in Seq(Messages), q # <<>>, NEW t, Sorted(q, t)
  PROVE Sorted(Tail(q), t) /\ (\A i \in DOMAIN Tail(q): t[Head(q)] < t[Tail(q)[i]])
  <1>1. DOMAIN q = 1..Len(q) /\ Len(q) \in Nat BY SMT, LenProperties
  <1>2. Tail(q) \in Seq(Messages) /\ Len(Tail(q)) = Len(q)-1
    /\ (\A i \in 1..Len(Tail(q)): Tail(q)[i] = q[i+1])
    BY SMT, HeadTailProperties
  <1>3. DOMAIN Tail(q) = 1..(Len(q)-1) /\ 1 \in DOMAIN q /\ Head(q) = q[1]
    BY SMTT(30), <1>1, <1>2, LenProperties, EmptySeq DEF Head
  <1>4. Sorted(Tail(q), t)
    <2>1. SUFFICES ASSUME NEW i \in DOMAIN Tail(q), NEW j \in DOMAIN Tail(q), i < j
      PROVE t[Tail(q)[i]] < t[Tail(q)[j]] BY SMT DEF Sorted
    <2>2. QED BY SMTT(30), <1>1, <1>2, <1>3, <2>1 DEF Sorted
  <1>5. \A i \in DOMAIN Tail(q): t[Head(q)] < t[Tail(q)[i]]
    <2>1. SUFFICES ASSUME NEW i \in DOMAIN Tail(q) PROVE t[Head(q)] < t[Tail(q)[i]]
      BY SMT
    <2>2. QED BY SMTT(30), <1>1, <1>2, <1>3, <2>1 DEF Sorted
  <1>6. QED BY SMT, <1>4, <1>5

\* Every queued message in a mailbox was sent at or before the clock.
LEMMA L_QueueFacts ==
  ASSUME Inv, IsFiniteSet(Boxes)
  PROVE \A b \in Boxes: \A i \in DOMAIN mailbox[b]:
       /\ mailbox[b][i] \in Messages
       /\ mstatus[mailbox[b][i]] = "queued"
       /\ sentAt[mailbox[b][i]] <= clock
  <1>1. SUFFICES ASSUME NEW b \in Boxes, NEW i \in DOMAIN mailbox[b]
    PROVE /\ mailbox[b][i] \in Messages
          /\ mstatus[mailbox[b][i]] = "queued"
          /\ sentAt[mailbox[b][i]] <= clock
    BY SMT
  <1>2. mailbox[b][i] \in Messages BY SMT DEF Inv, TypeOK
  <1>3. mailbox[b][i] \in Members(mailbox[b]) BY SMT DEF Members
  <1>4. Occ(mailbox[b][i]) \in SUBSET Boxes
    BY SMT DEF Occ, Members, Range
  <1>5. b \in Occ(mailbox[b][i]) BY SMT, <1>3 DEF Occ
  <1>6. mstatus[mailbox[b][i]] \in MStatus
    BY SMT, <1>2 DEF Inv, TypeOK, MStatus
  <1>7. mstatus[mailbox[b][i]] = "absent" => FALSE
    BY SMT, L_Card0Empty, <1>2, <1>4, <1>5 DEF Inv, MessageStatus
  <1>8. mstatus[mailbox[b][i]] = "delivered" => FALSE
    BY SMT, L_Card0Empty, <1>2, <1>4, <1>5 DEF Inv, MessageStatus
  <1>9. mstatus[mailbox[b][i]] = "failed" => FALSE
    BY SMT, L_Card0Empty, <1>2, <1>4, <1>5 DEF Inv, MessageStatus
  <1>10. QED
    <2>1. mstatus[mailbox[b][i]] # "absent" BY Isa, <1>7
    <2>2. mstatus[mailbox[b][i]] # "delivered" BY Isa, <1>8
    <2>3. mstatus[mailbox[b][i]] # "failed" BY Isa, <1>9
    <2>4. mstatus[mailbox[b][i]] = "queued" BY SMT, <1>6, <2>1, <2>2, <2>3 DEF MStatus
    <2>5. QED BY SMT, <1>2, <2>4 DEF Inv, MessageStatus

\* ---------------------------------------------------------------------------
\* Occurrence algebra for the two mailbox mutations: append and tail.
\* ---------------------------------------------------------------------------

LEMMA OccAfterAppend ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, mailbox[b] \in Seq(Messages)
  PROVE \A x \in Boxes :
          (m \in Members([mailbox EXCEPT ![b] = Append(mailbox[b], m)][x]))
          <=> (m \in Members(mailbox[x]) \/ x = b)
  BY SMTT(30), L_MembersAppend DEF Inv, TypeOK, Members, Range

LEMMA OccAfterAppendOther ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW m2 \in Messages, m2 # m
  PROVE \A x \in Boxes:
    (m2 \in Members([mailbox EXCEPT ![b] = Append(mailbox[b], m)][x]))
    <=> (m2 \in Members(mailbox[x]))
  <1>1. SUFFICES ASSUME NEW x \in Boxes PROVE
    (m2 \in Members([mailbox EXCEPT ![b] = Append(mailbox[b], m)][x]))
    <=> (m2 \in Members(mailbox[x]))
    BY SMT
  <1>2. [mailbox EXCEPT ![b] = Append(mailbox[b], m)][x]
        = IF x = b THEN Append(mailbox[b], m) ELSE mailbox[x]
    BY SMTT(30) DEF Inv, TypeOK
  <1>3. Members(Append(mailbox[b], m)) = Members(mailbox[b]) \cup {m}
    BY SMT, L_MembersAppend DEF Inv, TypeOK
  <1>4. QED BY SMT, <1>2, <1>3

LEMMA OccAfterTail ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, mailbox[b] \in Seq(Messages),
         Head(mailbox[b]) = m, IsInjective(mailbox[b]), mailbox[b] # <<>>
  PROVE \A x \in Boxes :
          (m \in Members([mailbox EXCEPT ![b] = Tail(mailbox[b])][x]))
          <=> (m \in Members(mailbox[x]) /\ x # b)
  <1>1. Members(Tail(mailbox[b])) = Members(mailbox[b]) \ {m} BY SMT, L_MembersTail
  <1>2. QED BY <1>1, SMTT(30) DEF Inv, TypeOK, Members, Range

LEMMA OccAfterTailOther ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW m2 \in Messages, m2 # m,
         Head(mailbox[b]) = m, IsInjective(mailbox[b]), mailbox[b] # <<>>
  PROVE \A x \in Boxes:
    (m2 \in Members([mailbox EXCEPT ![b] = Tail(mailbox[b])][x]))
    <=> (m2 \in Members(mailbox[x]))
  <1>1. Members(Tail(mailbox[b])) = Members(mailbox[b]) \ {m}
    BY SMT, L_MembersTail DEF Inv, TypeOK
  <1>2. QED BY SMTT(30), <1>1 DEF Inv, TypeOK

\* ---------------------------------------------------------------------------
\* MessageStatus, clause by clause.
\* ---------------------------------------------------------------------------

MessageClause(m) ==
         /\ (mstatus[m] = "absent"    => Cardinality(Occ(m)) = 0)
         /\ (mstatus[m] = "queued"    => Cardinality(Occ(m)) = 1)
         /\ (mstatus[m] = "delivered" => Cardinality(Occ(m)) = 0)
         /\ (mstatus[m] = "failed"    => Cardinality(Occ(m)) = 0)
         /\ Cardinality(Occ(m)) <= 1
         /\ (mstatus[m] # "absent" => sender[m] = origin[m])
         /\ (mstatus[m] # "absent" => sentAt[m] <= clock)

LEMMA L_MessageClauseSplit ==
  MessageStatus <=> \A m \in Messages: MessageClause(m)
  BY SMT DEF MessageStatus, MessageClause

\* ---------------------------------------------------------------------------
\* MailboxInv, box by box.
\* ---------------------------------------------------------------------------

BoxClause(b) ==
         /\ Len(mailbox[b]) <= Cap
         /\ \A i \in DOMAIN mailbox[b]: recipient[mailbox[b][i]] = b
         /\ \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]

LEMMA L_BoxClauseSplit ==
  MailboxInv <=> \A b \in Boxes: BoxClause(b)
  BY SMT DEF MailboxInv, BoxClause

LEMMA L_RecipientMembers ==
  ASSUME Inv
  PROVE \A b \in Boxes: \A n \in Members(mailbox[b]): recipient[n] = b
  BY SMTT(30) DEF Inv, MailboxInv, Members

LEMMA L_MailboxSorted ==
  ASSUME Inv, NEW b \in Boxes
  PROVE Sorted(mailbox[b], sentAt)
  BY SMT DEF Inv, MailboxInv, Sorted

LEMMA L_TailRecipients ==
  ASSUME Inv, NEW b \in Boxes, IsInjective(mailbox[b]), mailbox[b] # <<>>
  PROVE \A n \in Members(Tail(mailbox[b])): recipient[n] = b
  BY SMT, L_MembersTail, L_RecipientMembers DEF Inv, TypeOK, MailboxInv, Members

\* ---------------------------------------------------------------------------
\* The safety theorem.
\* ---------------------------------------------------------------------------

\* Appending and removing the head are the only mailbox mutations, and this
\* lemma covers removal in the language of sequences alone: no state variables
\* are primed, so the SMT backend never has to reason about EXCEPT.
LEMMA L_TailPreserves ==
  ASSUME Cap \in Nat, NEW b \in Boxes, NEW q \in Seq(Messages), q # <<>>,
         Len(q) <= Cap,
         \A i \in DOMAIN q: recipient[q[i]] = b,
         \A i, j \in DOMAIN q: i < j => sentAt[q[i]] < sentAt[q[j]]
  PROVE /\ Len(Tail(q)) <= Cap
        /\ \A i \in DOMAIN Tail(q): recipient[Tail(q)[i]] = b
        /\ \A i, j \in DOMAIN Tail(q): i < j => sentAt[Tail(q)[i]] < sentAt[Tail(q)[j]]
  <1>1. Len(Tail(q)) = Len(q) - 1 BY SMT, HeadTailProperties
  <1>2. Len(Tail(q)) <= Cap BY SMT, <1>1
  <1>3. \A i \in DOMAIN Tail(q): Tail(q)[i] = q[i+1] BY SMTT(30), HeadTailProperties
  <1>4. \A i \in DOMAIN Tail(q): recipient[Tail(q)[i]] = b
    <2>1. SUFFICES ASSUME NEW i \in DOMAIN Tail(q) PROVE recipient[Tail(q)[i]] = b
      BY SMT
    <2>2. i + 1 \in DOMAIN q BY SMT, <1>3, HeadTailProperties
    <2>3. Tail(q)[i] = q[i+1] BY SMT, <1>3
    <2>4. recipient[q[i+1]] = b BY SMT, <2>2
    <2>5. QED BY SMT, <2>3, <2>4
  <1>5. \A i, j \in DOMAIN Tail(q): i < j => sentAt[Tail(q)[i]] < sentAt[Tail(q)[j]]
    BY SMT, <1>3
  <1>6. QED BY SMT, <1>2, <1>4, <1>5

LEMMA L_DeliverMailbox ==
  ASSUME Inv, Cap \in Nat, NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages, Deliver(a, b, m)
  PROVE MailboxInv'
  <1>1. mailbox \in [Boxes -> Seq(Messages)] BY SMT DEF Inv, TypeOK
  <1>2. MailboxInv BY SMT DEF Inv
  <1>3. mailbox[b] # <<>> BY SMT DEF Deliver, GuardDeliver
  <1>4. mailbox' = [mailbox EXCEPT ![b] = Tail(mailbox[b])] BY SMT DEF Deliver
  <1>5. UNCHANGED <<recipient, sentAt>> BY SMT DEF Deliver
  <1>6. mailbox[b] \in Seq(Messages) BY SMT, <1>1
  <1>7. Len(mailbox[b]) <= Cap BY SMT, <1>2 DEF MailboxInv
  <1>8. \A i \in DOMAIN mailbox[b]: recipient[mailbox[b][i]] = b BY SMT, <1>2 DEF MailboxInv
  <1>9. \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]
    BY SMT, <1>2 DEF MailboxInv, Sorted
  <1>10. /\ Len(Tail(mailbox[b])) <= Cap
         /\ \A i \in DOMAIN Tail(mailbox[b]): recipient[Tail(mailbox[b])[i]] = b
         /\ \A i, j \in DOMAIN Tail(mailbox[b]):
               i < j => sentAt[Tail(mailbox[b])[i]] < sentAt[Tail(mailbox[b])[j]]
    BY Isa, <1>3, <1>6, <1>7, <1>8, <1>9, L_TailPreserves
  <1>11. BoxClause(b)'
    <2>1. mailbox'[b] = Tail(mailbox[b]) BY SMT, <1>1, <1>4
    <2>2. QED BY SMT, <2>1, <1>5, <1>10 DEF BoxClause
  <1>12. \A x \in Boxes \ {b}: BoxClause(x)'
    BY SMT, <1>1, <1>2, <1>4, <1>5 DEF MailboxInv, BoxClause
  <1>13. QED BY SMT, <1>11, <1>12 DEF BoxClause, MailboxInv

LEMMA L_FailMailbox ==
  ASSUME Inv, Cap \in Nat, NEW b \in Boxes, NEW m \in Messages, Fail(b, m)
  PROVE MailboxInv'
  <1>1. mailbox \in [Boxes -> Seq(Messages)] BY SMT DEF Inv, TypeOK
  <1>2. MailboxInv BY SMT DEF Inv
  <1>3. mailbox[b] # <<>> BY SMT DEF Fail, GuardFail
  <1>4. mailbox' = [mailbox EXCEPT ![b] = Tail(mailbox[b])] BY SMT DEF Fail
  <1>5. UNCHANGED <<recipient, sentAt>> BY SMT DEF Fail
  <1>6. mailbox[b] \in Seq(Messages) BY SMT, <1>1
  <1>7. Len(mailbox[b]) <= Cap BY SMT, <1>2 DEF MailboxInv
  <1>8. \A i \in DOMAIN mailbox[b]: recipient[mailbox[b][i]] = b BY SMT, <1>2 DEF MailboxInv
  <1>9. \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]
    BY SMT, <1>2 DEF MailboxInv, Sorted
  <1>10. /\ Len(Tail(mailbox[b])) <= Cap
         /\ \A i \in DOMAIN Tail(mailbox[b]): recipient[Tail(mailbox[b])[i]] = b
         /\ \A i, j \in DOMAIN Tail(mailbox[b]):
               i < j => sentAt[Tail(mailbox[b])[i]] < sentAt[Tail(mailbox[b])[j]]
    BY Isa, <1>3, <1>6, <1>7, <1>8, <1>9, L_TailPreserves
  <1>11. BoxClause(b)'
    <2>1. mailbox'[b] = Tail(mailbox[b]) BY SMT, <1>1, <1>4
    <2>2. QED BY SMT, <2>1, <1>5, <1>10 DEF BoxClause
  <1>12. \A x \in Boxes \ {b}: BoxClause(x)'
    BY SMT, <1>1, <1>2, <1>4, <1>5 DEF MailboxInv, BoxClause
  <1>13. QED BY SMT, <1>11, <1>12 DEF BoxClause, MailboxInv

THEOREM Safety ==
  ASSUME Cap \in Nat, MaxClock \in Nat, IsFiniteSet(Boxes),
         \* `None` is the "no value" sentinel of an option type; it must be fresh,
         \* or options become ambiguous.
         None \notin (Agents \cup Boxes \cup Messages \cup Posts \cup Topics)
  PROVE SafetySpec => []Inv

  <1>1. Init => Inv
    <2>1. Init => TypeOK
      BY SMT DEF MStatus, PStatus, Init, TypeOK
    <2>2. Init => BoundConsistent
      BY SMT DEF MStatus, PStatus, Init, BoundConsistent
    <2>3. Init => OwnerConsistent
      BY SMT DEF MStatus, PStatus, Init, OwnerConsistent
    <2>4. Init => MessageStatus
      <3>1. SUFFICES ASSUME Init PROVE MessageStatus
        BY SMT
      <3>2. \A m \in Messages: Occ(m) = {}
        BY <3>1, SMTT(30), L_EmptyMembers DEF Init, Occ
      <3>3. QED BY SMT, <3>1, <3>2, FS_EmptySet DEF Init, MessageStatus
    <2>5. Init => MailboxInv
      BY SMT DEF MStatus, PStatus, Init, MailboxInv
    <2>6. Init => SubsRegistered
      BY SMT DEF MStatus, PStatus, Init, SubsRegistered
    <2>7. Init => PostsInv
      BY SMT DEF MStatus, PStatus, Init, PostsInv
    <2>8. Init => PostedDistinct
      BY SMT DEF MStatus, PStatus, Init, PostedDistinct
    <2>9. Init => PostedMembership
      BY SMT, L_EmptyMembers DEF MStatus, PStatus, Init, PostedMembership
    <2>10. QED
      BY Isa, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv

  <1>2. Inv /\ [Next]_vars => Inv'
    <2>1. \A a \in Agents: Inv /\ Register(a) => Inv'
      <3>1. \A a \in Agents: Inv /\ Register(a) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Register, GuardRegister, vars
      <3>2. \A a \in Agents: Inv /\ Register(a) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>3. \A a \in Agents: Inv /\ Register(a) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>4. \A a \in Agents: Inv /\ Register(a) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>5. \A a \in Agents: Inv /\ Register(a) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>6. \A a \in Agents: Inv /\ Register(a) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>7. \A a \in Agents: Inv /\ Register(a) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>8. \A a \in Agents: Inv /\ Register(a) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>9. \A a \in Agents: Inv /\ Register(a) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Register, GuardRegister, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>2. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => Inv'
      <3>1. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Bind, GuardBind, vars
      <3>2. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => BoundConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Bind, GuardBind
      <3>3. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => OwnerConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Bind, GuardBind
      <3>4. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>5. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>6. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>7. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>8. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>9. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Bind, GuardBind, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>3. \A a \in Agents: Inv /\ Unbind(a) => Inv'
      <3>1. \A a \in Agents: Inv /\ Unbind(a) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Unbind, GuardUnbind, vars
      <3>2. \A a \in Agents: Inv /\ Unbind(a) => BoundConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Unbind, GuardUnbind
      <3>3. \A a \in Agents: Inv /\ Unbind(a) => OwnerConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Unbind, GuardUnbind
      <3>4. \A a \in Agents: Inv /\ Unbind(a) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>5. \A a \in Agents: Inv /\ Unbind(a) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>6. \A a \in Agents: Inv /\ Unbind(a) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>7. \A a \in Agents: Inv /\ Unbind(a) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>8. \A a \in Agents: Inv /\ Unbind(a) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>9. \A a \in Agents: Inv /\ Unbind(a) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unbind, GuardUnbind, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>4. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => Inv'
      <3>1. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Send, GuardSend, vars
      <3>2. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>3. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>4. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW s \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Send(s, b, m) PROVE MessageStatus'
          BY SMT
        <4>2. Occ(m) = {}
          BY SMT, <4>1, L_EmptyPlacements DEF Send, GuardSend
        <4>3. Occ(m)' = {b}
          <5>1. \A x \in Boxes: (m \in Members(mailbox'[x])) <=> (m \in Members(mailbox[x]) \/ x = b)
            BY SMT, <4>1, OccAfterAppend DEF Send, Inv, TypeOK
          <5>2. \A x \in Boxes: (m \in Members(mailbox[x])) <=> FALSE
            BY SMT, <4>2 DEF Occ
          <5>3. QED BY SMT, <5>1, <5>2 DEF Occ, Send
        <4>4. MessageClause(m)'
          BY SMTT(30), <4>1, <4>3, FS_EmptySet, FS_Singleton DEF MessageClause, Send, Inv, TypeOK
        <4>5. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
            BY <4>1, <5>1, SMTT(30), OccAfterAppendOther DEF Send, Inv, TypeOK
          <5>3. Occ(n)' = Occ(n)
            BY SMT, <5>1, <5>2 DEF Occ, Send
          <5>4. QED BY <4>1, <5>1, <5>3 DEF Inv, TypeOK, MessageStatus, MessageClause, Send
        <4>6. QED BY SMT, <4>4, <4>5 DEF MessageStatus, MessageClause
      <3>5. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => MailboxInv'
        <4>1. SUFFICES ASSUME NEW s \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Send(s, b, m) PROVE MailboxInv'
          BY SMT
        <4>2. \A x \in Boxes: \A i \in DOMAIN mailbox[x]:
           /\ mailbox[x][i] # m
           /\ sentAt'[mailbox[x][i]] = sentAt[mailbox[x][i]]
           /\ sentAt'[mailbox[x][i]] < sentAt'[m]
          BY <4>1, SMTT(30), L_QueueFacts DEF Inv, TypeOK, Send, GuardSend
        <4>3. \A x \in Boxes: Sorted(mailbox[x], sentAt')
          BY SMT, <4>1, <4>2 DEF Sorted, Inv, MailboxInv
        <4>4. Sorted(Append(mailbox[b], m), sentAt')
          BY SMT, <4>1, <4>2, <4>3, L_SortedAppend DEF Inv, TypeOK
        <4>5. Len(Append(mailbox[b], m)) = Len(mailbox[b])+1
          BY SMT, <4>1, AppendProperties DEF Inv, TypeOK
        <4>6. \A n \in Members(Append(mailbox[b], m)): recipient'[n] = b
          <5>1. SUFFICES ASSUME NEW n \in Members(Append(mailbox[b], m)) PROVE recipient'[n] = b
            BY SMT
          <5>2. n \in Members(mailbox[b]) \/ n = m
            BY SMT, <4>1, <5>1, L_MembersAppend DEF Inv, TypeOK
          <5>3. n \in Messages /\ (n = m \/ recipient[n] = b)
            BY SMT, <4>1, <5>2, L_RecipientMembers DEF Inv, TypeOK, Members
          <5>4. QED BY SMT, <4>1, <5>1, <5>3 DEF Inv, TypeOK, Send
        <4>7. BoxClause(b)'
          BY <4>1, SMTT(30), <4>4, <4>5, <4>6
            DEF BoxClause, Sorted, Inv, TypeOK, MailboxInv, Send, GuardSend, Members
        <4>8. \A x \in Boxes \ {b}: BoxClause(x)'
          BY <4>1, SMTT(30), <4>2, <4>3
            DEF BoxClause, Sorted, Inv, TypeOK, MailboxInv, Send
        <4>9. QED BY SMT, <4>7, <4>8 DEF BoxClause, MailboxInv
      <3>6. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>7. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>8. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>9. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Send, GuardSend, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>5. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => Inv'
      <3>1. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Deliver, GuardDeliver, vars
      <3>2. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>3. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>4. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Deliver(a, b, m) PROVE MessageStatus'
          BY SMT
        <4>2. mailbox[b] # <<>> /\ IsInjective(mailbox[b]) /\ m \in Members(mailbox[b])
          BY <4>1, SMTT(30), L_SortedInjective, HeadTailProperties
            DEF Inv, TypeOK, MailboxInv, Deliver, GuardDeliver, Members, Range
        <4>3. Occ(m) = {b}
          BY <4>1, SMTT(30), <4>2, L_QueuedOcc DEF Inv, MessageStatus, Deliver, GuardDeliver
        <4>4. \A x \in Boxes: m \notin Members(mailbox'[x])
          BY <4>1, SMTT(30), <4>2, <4>3, OccAfterTail, L_HeadNotInTail
            DEF Deliver, GuardDeliver, Occ, Inv, TypeOK
        <4>5. Occ(m)' = {}
          <5>1. SUFFICES ASSUME NEW x \in Boxes PROVE m \notin Members(mailbox'[x])
            BY SMT DEF Occ
          <5>2. QED BY SMT, <4>4
        <4>6. MessageClause(m)'
          BY <4>1, SMTT(30), <4>5, FS_EmptySet DEF MessageClause, Inv, TypeOK, MessageStatus, Deliver, GuardDeliver
        <4>7. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
            BY <4>1, <5>1, SMTT(30), <4>2, OccAfterTailOther DEF Deliver, GuardDeliver
          <5>3. Occ(n)' = Occ(n)
            BY SMT, <5>1, <5>2 DEF Occ, Deliver
          <5>4. QED BY <4>1, <5>1, <5>3 DEF Inv, TypeOK, MessageStatus, MessageClause, Deliver
        <4>8. QED BY SMT, <4>6, <4>7 DEF MessageStatus, MessageClause
      <3>5. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => MailboxInv'
        BY SMT, L_DeliverMailbox

      <3>6. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>7. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>8. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>9. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Deliver(a, b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Deliver, GuardDeliver, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>6. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => Inv'
      <3>1. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None,
          Inv, TypeOK, Fail, GuardFail, vars
      <3>2. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>3. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>4. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW b \in Boxes, NEW m \in Messages,
                    Inv, Fail(b, m) PROVE MessageStatus'
          BY SMT
        <4>2. mailbox[b] # <<>> /\ IsInjective(mailbox[b]) /\ m \in Members(mailbox[b])
          BY <4>1, SMTT(30), L_SortedInjective, HeadTailProperties
            DEF Inv, TypeOK, MailboxInv, Fail, GuardFail, Members, Range
        <4>3. Occ(m) = {b}
          BY <4>1, SMTT(30), <4>2, L_QueuedOcc DEF Inv, MessageStatus, Fail, GuardFail
        <4>4. \A x \in Boxes: m \notin Members(mailbox'[x])
          BY <4>1, SMTT(30), <4>2, <4>3, OccAfterTail, L_HeadNotInTail
            DEF Fail, GuardFail, Occ, Inv, TypeOK
        <4>5. Occ(m)' = {}
          <5>1. SUFFICES ASSUME NEW x \in Boxes PROVE m \notin Members(mailbox'[x])
            BY SMT DEF Occ
          <5>2. QED BY SMT, <4>4
        <4>6. MessageClause(m)'
          BY <4>1, SMTT(30), <4>5, FS_EmptySet DEF MessageClause, Inv, TypeOK, MessageStatus, Fail, GuardFail
        <4>7. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
            BY <4>1, <5>1, SMTT(30), <4>2, OccAfterTailOther DEF Fail, GuardFail
          <5>3. Occ(n)' = Occ(n)
            BY SMT, <5>1, <5>2 DEF Occ, Fail
          <5>4. QED BY <4>1, <5>1, <5>3 DEF Inv, TypeOK, MessageStatus, MessageClause, Fail
        <4>8. QED BY SMT, <4>6, <4>7 DEF MessageStatus, MessageClause
      <3>5. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => MailboxInv'
        BY SMT, L_FailMailbox

      <3>6. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>7. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>8. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>9. \A b \in Boxes, m \in Messages: Inv /\ Fail(b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Fail, GuardFail, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>7. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => Inv'
      <3>1. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => TypeOK'
        BY SMT DEF MStatus, PStatus, None, Inv, TypeOK, Subscribe, GuardSubscribe, vars
      <3>2. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>3. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>4. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>5. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>6. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => SubsRegistered'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW t \in Topics, Inv, Subscribe(a, t) PROVE SubsRegistered'
          BY SMT
        <4>2. subscribed \in [Agents -> SUBSET Topics] BY SMT, <4>1 DEF Inv, TypeOK
        <4>3. registered \in [Agents -> BOOLEAN] BY SMT, <4>1 DEF Inv, TypeOK
        <4>4. SubsRegistered BY SMT, <4>1 DEF Inv
        <4>5. registered[a] BY SMT, <4>1 DEF Subscribe, GuardSubscribe
        <4>6. registered' = registered BY SMT, <4>1 DEF Subscribe
        <4>7. subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \cup {t}] BY SMT, <4>1 DEF Subscribe
        <4>8. QED BY SMT, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF SubsRegistered
      <3>7. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>8. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>9. \A a \in Agents, t \in Topics: Inv /\ Subscribe(a, t) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Subscribe, GuardSubscribe, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>8. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => Inv'
      <3>1. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => TypeOK'
        BY SMT DEF MStatus, PStatus, None, Inv, TypeOK, Unsubscribe, GuardUnsubscribe, vars
      <3>2. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>3. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>4. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>5. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>6. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => SubsRegistered'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW t \in Topics, Inv, Unsubscribe(a, t) PROVE SubsRegistered'
          BY SMT
        <4>2. subscribed \in [Agents -> SUBSET Topics] BY SMT, <4>1 DEF Inv, TypeOK
        <4>3. registered \in [Agents -> BOOLEAN] BY SMT, <4>1 DEF Inv, TypeOK
        <4>4. SubsRegistered BY SMT, <4>1 DEF Inv
        <4>5. registered' = registered BY SMT, <4>1 DEF Unsubscribe
        <4>6. subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \ {t}] BY SMT, <4>1 DEF Unsubscribe
        <4>7. QED BY SMT, <4>2, <4>3, <4>4, <4>5, <4>6 DEF SubsRegistered
      <3>7. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>8. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>9. \A a \in Agents, t \in Topics: Inv /\ Unsubscribe(a, t) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Unsubscribe, GuardUnsubscribe, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>9. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
            Inv /\ Post(a, p, t, par) => Inv'
      <3>1. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => TypeOK'
        BY SMT DEF MStatus, PStatus, None, Inv, TypeOK, Post, GuardPost, vars
      <3>2. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>3. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>4. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>5. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>6. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => SubsRegistered'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW p \in Posts, NEW t \in Topics,
                    NEW par \in Posts \cup {None}, Inv, Post(a, p, t, par) PROVE SubsRegistered'
          BY SMT
        <4>2. subscribed \in [Agents -> SUBSET Topics] BY SMT, <4>1 DEF Inv, TypeOK
        <4>3. registered \in [Agents -> BOOLEAN] BY SMT, <4>1 DEF Inv, TypeOK
        <4>4. SubsRegistered BY SMT, <4>1 DEF Inv
        <4>5. registered[a] BY SMT, <4>1 DEF Post, GuardPost
        <4>6. registered' = registered BY SMT, <4>1 DEF Post
        <4>7. subscribed' = [subscribed EXCEPT ![a] = subscribed[a] \cup {t}] BY SMT, <4>1 DEF Post
        <4>8. QED BY SMT, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF SubsRegistered
      <3>7. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>8. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>9. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}:
              Inv /\ Post(a, p, t, par) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, Post, GuardPost, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>10. Inv /\ UNCHANGED vars => Inv'
      <3>1. Inv /\ UNCHANGED vars => TypeOK'
        BY SMT DEF MStatus, PStatus, None, Inv, TypeOK, vars
      <3>2. Inv /\ UNCHANGED vars => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>3. Inv /\ UNCHANGED vars => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>4. Inv /\ UNCHANGED vars => MessageStatus'
        BY Isa DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>5. Inv /\ UNCHANGED vars => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>6. Inv /\ UNCHANGED vars => SubsRegistered'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>7. Inv /\ UNCHANGED vars => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>8. Inv /\ UNCHANGED vars => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>9. Inv /\ UNCHANGED vars => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None,
          Members, Occ, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, SubsRegistered, PostsInv, PostedDistinct,
          PostedMembership, vars
      <3>10. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv

    <2>11. QED
      BY SMT, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
         DEF Next, vars

  <1>3. QED
    BY <1>1, <1>2, PTL DEF SafetySpec

=======================================================================
