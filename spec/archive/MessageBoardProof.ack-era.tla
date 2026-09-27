---------------------- MODULE MessageBoardProof ----------------------
\* ARCHIVED: this inductive proof covers the ack-era revision of the board
\* (leases, fetch/ack/rollback/reclaim), whose spec is in git history at
\* commit 7147f70. The push revision replaced that transition relation and this
\* proof must be re-derived against it; see DESIGN-bus.md. Not part of CI.
\* The inductive safety proof for the parameterized MessageBoard.
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

LEMMA L_MembersPrepend == ASSUME NEW q \in Seq(Messages), NEW m \in Messages
  PROVE Members(<<m>> \o q) = {m} \cup Members(q)
  <1>1. Range(<<m>> \o q) = Range(<<m>>) \cup Range(q) BY SMT, RangeConcatenation
  <1>2. Range(<<m>>) = {m} BY SMT DEF Range
  <1>3. Members(<<m>> \o q) = Range(<<m>> \o q) BY SMT DEF Members, Range
  <1>4. Members(q) = Range(q) BY SMT DEF Members, Range
  <1>5. QED BY SMT, <1>1, <1>2, <1>3, <1>4

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

LEMMA L_CardAddNew == ASSUME IsFiniteSet(Boxes), NEW S \in SUBSET Boxes, NEW b \in Boxes, b \notin S
  PROVE Cardinality(S \cup {b}) = Cardinality(S) + 1
  <1>1. IsFiniteSet(S) BY SMT, FS_Subset
  <1>2. QED BY SMT, <1>1, FS_AddElement

LEMMA L_QueueMailboxNotAcked == ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages, NEW b \in Boxes,
    m \in Members(mailbox[b]), mstatus[m] # "queued"
  PROVE FALSE
  <1>0. Occ(m) \in SUBSET Boxes BY SMT DEF Occ, Members, Range
  <1>1. b \in Occ(m) BY SMT DEF Occ
  <1>2. Cardinality(Occ(m)) = 0 BY SMT DEF Inv, TypeOK, MStatus, MessageStatus
  <1>3. Occ(m) = {} BY SMT, <1>0, <1>2, L_Card0Empty
  <1>4. QED BY SMT, <1>1, <1>3

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

LEMMA OccAfterPrepend ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, mailbox[b] \in Seq(Messages)
  PROVE \A x \in Boxes :
          (m \in Members([mailbox EXCEPT ![b] = <<m>> \o mailbox[b]][x]))
          <=> (m \in Members(mailbox[x]) \/ x = b)
  BY SMTT(30), L_MembersPrepend DEF Inv, TypeOK, Members, Range

LEMMA OccAfterTail ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, mailbox[b] \in Seq(Messages),
         Head(mailbox[b]) = m, IsInjective(mailbox[b]), mailbox[b] # <<>>
  PROVE \A x \in Boxes :
          (m \in Members([mailbox EXCEPT ![b] = Tail(mailbox[b])][x]))
          <=> (m \in Members(mailbox[x]) /\ x # b)
  <1>1. Members(Tail(mailbox[b])) = Members(mailbox[b]) \ {m} BY SMT, L_MembersTail
  <1>2. QED BY <1>1, SMTT(30) DEF Inv, TypeOK, Members, Range

LEMMA LeaAfterLease ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW v \in (Messages \cup {None})
  PROVE \A x \in Boxes:
    ([lease EXCEPT ![b] = v][x] = m)
    <=> ((x # b /\ lease[x] = m) \/ (x = b /\ v = m))
  BY SMT DEF Inv, TypeOK

LEMMA L_LeaseUpdateSet ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW v \in (Messages \cup {None})
  PROVE {x \in Boxes : ([lease EXCEPT ![b] = v][x]) = m}
        = ({x \in Boxes : lease[x] = m} \ {b}) \cup (IF v = m THEN {b} ELSE {})
  <1>1. \A x \in Boxes:
    ([lease EXCEPT ![b] = v][x] = m)
    <=> ((x # b /\ lease[x] = m) \/ (x = b /\ v = m))
    BY SMT, LeaAfterLease
  <1>2. QED BY SMT, <1>1

\* Turn cardinality facts into explicit location sets before moving a message.
LEMMA L_Locations ==
  ASSUME Inv, IsFiniteSet(Boxes), NEW m \in Messages
  PROVE /\ (mstatus[m] \in {"absent", "acked"} => Occ(m) = {} /\ Lea(m) = {})
        /\ (mstatus[m] = "queued" => Lea(m) = {})
        /\ (mstatus[m] = "fetched" => Occ(m) = {})
  <1>1. Occ(m) \subseteq Boxes /\ Lea(m) \subseteq Boxes BY SMT DEF Occ, Lea
  <1>2. QED BY SMT, <1>1, L_Card0Empty DEF Inv, MessageStatus

LEMMA L_UniqueLocation ==
  ASSUME IsFiniteSet(Boxes), NEW S \in SUBSET Boxes,
         Cardinality(S) = 1, NEW b \in S
  PROVE S = {b}
  <1>1. IsFiniteSet(S) BY SMT, FS_Subset
  <1>2. \E x: S = {x} BY SMT, <1>1, FS_Singleton
  <1>3. QED BY SMT, <1>2

LEMMA OccAfterPrependOther ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW m2 \in Messages, m2 # m
  PROVE \A x \in Boxes:
    (m2 \in Members([mailbox EXCEPT ![b] = <<m>> \o mailbox[b]][x]))
    <=> (m2 \in Members(mailbox[x]))
  <1>1. SUFFICES ASSUME NEW x \in Boxes PROVE
    (m2 \in Members([mailbox EXCEPT ![b] = <<m>> \o mailbox[b]][x]))
    <=> (m2 \in Members(mailbox[x]))
    BY SMT
  <1>2. [mailbox EXCEPT ![b] = <<m>> \o mailbox[b]][x]
        = IF x = b THEN <<m>> \o mailbox[b] ELSE mailbox[x]
    BY SMTT(30) DEF Inv, TypeOK
  <1>3. Members(<<m>> \o mailbox[b]) = Members(mailbox[b]) \cup {m}
    BY SMT, L_MembersPrepend DEF Inv, TypeOK
  <1>4. QED BY SMT, <1>2, <1>3

LEMMA OccAfterTailOther ==
  ASSUME Inv, NEW b \in Boxes, NEW m \in Messages, NEW m2 \in Messages, m2 # m,
         Head(mailbox[b]) = m, IsInjective(mailbox[b]), mailbox[b] # <<>>
  PROVE \A x \in Boxes:
    (m2 \in Members([mailbox EXCEPT ![b] = Tail(mailbox[b])][x]))
    <=> (m2 \in Members(mailbox[x]))
  <1>1. Members(Tail(mailbox[b])) = Members(mailbox[b]) \ {m}
    BY SMT, L_MembersTail DEF Inv, TypeOK
  <1>2. QED BY SMTT(30), <1>1 DEF Inv, TypeOK

MessageClause(m) ==
         /\ (mstatus[m] = "absent"  => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 0)
         /\ (mstatus[m] = "queued"  => Cardinality(Occ(m)) = 1 /\ Cardinality(Lea(m)) = 0)
         /\ (mstatus[m] = "fetched" => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 1)
         /\ (mstatus[m] = "acked"   => Cardinality(Occ(m)) = 0 /\ Cardinality(Lea(m)) = 0)
         /\ Cardinality(Occ(m)) + Cardinality(Lea(m)) <= 1
         /\ (mstatus[m] # "absent" => sender[m] = origin[m])

LEMMA L_ReturnStatus ==
  ASSUME Inv, IsFiniteSet(Boxes), None \notin Messages,
         NEW b \in Boxes, NEW m \in Messages, lease[b] = m,
         mstatus' = [mstatus EXCEPT ![m] = "queued"],
         mailbox' = [mailbox EXCEPT ![b] = <<m>> \o mailbox[b]],
         lease' = [lease EXCEPT ![b] = None],
         UNCHANGED <<sender, origin>>
  PROVE MessageStatus'
  <1>1. mstatus[m] = "fetched" BY SMT DEF Inv, MailboxInv
  <1>2. Occ(m) = {} /\ Lea(m) = {b}
    BY SMTT(30), <1>1, L_UniqueLocation, L_Locations DEF Inv, MessageStatus, Lea
  <1>3a. \A x \in Boxes: (m \in Members(mailbox'[x])) <=> (m \in Members(mailbox[x]) \/ x = b)
    BY SMT, OccAfterPrepend DEF Inv, TypeOK
  <1>3. \A x \in Boxes: (m \in Members(mailbox'[x])) <=> x = b
    BY SMT, <1>2, <1>3a DEF Occ
  <1>4. Occ(m)' = {b} /\ Lea(m)' = {}
    BY SMTT(30), <1>2, <1>3, L_LeaseUpdateSet DEF Occ, Lea
  <1>5. MessageClause(m)'
    BY SMTT(30), <1>1, <1>4, FS_EmptySet, FS_Singleton DEF MessageClause, Inv, TypeOK, MessageStatus
  <1>6. \A n \in Messages \ {m}: MessageClause(n)'
    <2>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
      BY SMT
    <2>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
      BY SMTT(30), OccAfterPrependOther
    <2>3. Occ(n)' = Occ(n) /\ Lea(n)' = Lea(n)
      BY SMTT(30), <2>2, L_LeaseUpdateSet DEF Occ, Lea
    <2>4. QED BY SMTT(30), <2>3 DEF Inv, TypeOK, MessageStatus, MessageClause
  <1>7. QED BY SMT, <1>5, <1>6 DEF MessageStatus, MessageClause

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

LEMMA L_SortedPrepend ==
  ASSUME NEW q \in Seq(Messages), NEW m \in Messages, NEW t,
         Sorted(q, t), \A i \in DOMAIN q: t[m] < t[q[i]]
  PROVE Sorted(<<m>> \o q, t)
  <1>1. <<m>> \in Seq(Messages) /\ Len(<<m>>) = 1 BY SMT
  <1>2. DOMAIN q = 1..Len(q) /\ Len(q) \in Nat BY SMT, LenProperties
  <1>3. <<m>> \o q \in Seq(Messages) /\ Len(<<m>> \o q) = Len(q)+1
    /\ (\A i \in 1..(Len(q)+1): (<<m>> \o q)[i] = IF i = 1 THEN m ELSE q[i-1])
    BY SMTT(30), <1>1, <1>2, ConcatProperties
  <1>4. DOMAIN (<<m>> \o q) = 1..(Len(q)+1)
    BY SMT, <1>3, LenProperties
  <1>5. SUFFICES ASSUME NEW i \in DOMAIN (<<m>> \o q), NEW j \in DOMAIN (<<m>> \o q), i < j
    PROVE t[(<<m>> \o q)[i]] < t[(<<m>> \o q)[j]]
    BY SMT DEF Sorted
  <1>6. CASE i = 1
    BY <1>6, SMTT(30), <1>2, <1>3, <1>4, <1>5
  <1>7. CASE i # 1
    <2>1. i-1 \in DOMAIN q /\ j-1 \in DOMAIN q /\ i-1 < j-1
      BY SMTT(30), <1>7, <1>2, <1>4, <1>5
    <2>2. t[q[i-1]] < t[q[j-1]] BY SMT, <2>1 DEF Sorted
    <2>3. (<<m>> \o q)[i] = q[i-1] /\ (<<m>> \o q)[j] = q[j-1]
      BY SMTT(30), <1>7, <1>3, <1>4, <1>5
    <2>4. QED BY SMT, <2>2, <2>3
  <1>8. QED BY SMT, <1>6, <1>7

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
  <1>4. mstatus[mailbox[b][i]] = "queued"
    BY SMT, <1>2, <1>3, L_QueueMailboxNotAcked
  <1>5. QED BY SMT, <1>2, <1>4 DEF Inv, SentAtLeClock

BoxClause(b) ==
         /\ Len(mailbox[b]) + LeasedSlots(lease[b]) <= Cap
         /\ (lease[b] = None \/ (lease[b] \in Messages /\ mstatus[lease[b]] = "fetched" /\ recipient[lease[b]] = b))
         \* Needed by Recv: moving the head to a lease preserves its recipient.
         /\ \A i \in DOMAIN mailbox[b]: recipient[mailbox[b][i]] = b
         /\ \A i, j \in DOMAIN mailbox[b]: i < j => sentAt[mailbox[b][i]] < sentAt[mailbox[b][j]]

LEMMA L_RecipientMembers ==
  ASSUME Inv
  PROVE \A b \in Boxes: \A n \in Members(mailbox[b]): recipient[n] = b
  BY SMTT(30) DEF Inv, MailboxInv, Members

LEMMA L_ReturnMailbox ==
  ASSUME Inv, None \notin Messages, NEW b \in Boxes, NEW m \in Messages, lease[b] = m,
         mstatus' = [mstatus EXCEPT ![m] = "queued"],
         mailbox' = [mailbox EXCEPT ![b] = <<m>> \o mailbox[b]],
         lease' = [lease EXCEPT ![b] = None],
         UNCHANGED <<recipient, sentAt>>
  PROVE MailboxInv'
  <1>1. <<m>> \in Seq(Messages) /\ Len(<<m>>) = 1 BY SMT
  <1>2. Len(<<m>> \o mailbox[b]) = 1 + Len(mailbox[b])
    BY SMT, <1>1, ConcatProperties DEF Inv, TypeOK
  <1>3a. Sorted(mailbox[b], sentAt) BY SMT DEF Sorted, Inv, MailboxInv
  <1>3b. \A i \in DOMAIN mailbox[b]: sentAt[m] < sentAt[mailbox[b][i]]
    BY SMT DEF Inv, LeasePrecedes
  <1>3. Sorted(<<m>> \o mailbox[b], sentAt)
    BY SMT, <1>3a, <1>3b, L_SortedPrepend DEF Inv, TypeOK
  <1>4. \A x \in Boxes \ {b}: lease[x] # m
    BY SMTT(30) DEF Inv, MailboxInv
  <1>5. \A n \in Members(<<m>> \o mailbox[b]): recipient[n] = b
    BY SMTT(30), L_MembersPrepend, L_RecipientMembers DEF Inv, TypeOK, MailboxInv
  <1>6. BoxClause(b)'
    BY SMTT(30), <1>2, <1>3, <1>5 DEF BoxClause, Sorted, Inv, TypeOK, MailboxInv, LeasedSlots, Members
  <1>7. \A x \in Boxes \ {b}: BoxClause(x)'
    <2>1. SUFFICES ASSUME NEW x \in Boxes \ {b} PROVE BoxClause(x)'
      BY SMT
    <2>2. mailbox'[x] = mailbox[x] /\ lease'[x] = lease[x]
      /\ (lease[x] # None => mstatus'[lease[x]] = mstatus[lease[x]])
      BY SMTT(30), <2>1, <1>4 DEF Inv, TypeOK, MailboxInv
    <2>3. QED BY SMTT(30), <2>1, <2>2 DEF BoxClause, Inv, MailboxInv
  <1>8. QED BY SMT, <1>6, <1>7 DEF BoxClause, MailboxInv

LEMMA L_PrecedesAppend ==
  ASSUME NEW q \in Seq(Messages), NEW m \in Messages, NEW t, NEW l,
         \A i \in DOMAIN q: t[l] < t[q[i]], t[l] < t[m]
  PROVE \A i \in DOMAIN Append(q, m): t[l] < t[Append(q, m)[i]]
  <1>1. DOMAIN q = 1..Len(q) /\ Len(q) \in Nat BY SMT, LenProperties
  <1>2. Append(q, m) \in Seq(Messages) /\ Len(Append(q, m)) = Len(q)+1
      /\ (\A i \in DOMAIN q: Append(q, m)[i] = q[i])
      /\ Append(q, m)[Len(q)+1] = m
    BY SMT, <1>1, AppendProperties
  <1>3. DOMAIN Append(q, m) = 1..(Len(q)+1) BY SMT, <1>2, LenProperties
  <1>4. QED BY SMTT(30), <1>1, <1>2, <1>3

THEOREM Safety ==
  ASSUME Cap \in Nat, MaxClock \in Nat, IsFiniteSet(Boxes),
         \* `None` is the "no value" sentinel of an option type; it must be fresh,
         \* or `lease[b] = None` would also count as a message named "none".
         None \notin (Agents \cup Boxes \cup Messages \cup Posts \cup Topics)
  PROVE Spec => []Inv

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
      <3>3. \A m \in Messages: Lea(m) = {}
        BY <3>1, SMTT(30) DEF Init, Lea
      <3>4. QED BY SMT, <3>1, <3>2, <3>3, FS_EmptySet DEF Init, MessageStatus
    <2>5. Init => MailboxInv
      BY SMT DEF MStatus, PStatus, Init, MailboxInv, LeasedSlots
    <2>6. Init => PostsInv
      BY SMT DEF MStatus, PStatus, Init, PostsInv
    <2>7. Init => PostedDistinct
      BY SMT DEF MStatus, PStatus, Init, PostedDistinct
    <2>8. Init => PostedMembership
      BY SMT, L_EmptyMembers, L_Card0Empty DEF MStatus, PStatus, Init, PostedMembership
    <2>9. Init => LeaseNotInMailbox
      BY SMT DEF MStatus, PStatus, Init, LeaseNotInMailbox
    <2>10. Init => LeasePrecedes
      BY SMT DEF MStatus, PStatus, Init, LeasePrecedes
    <2>11. Init => SentAtLeClock
      BY SMT DEF MStatus, PStatus, Init, SentAtLeClock
    <2>12. QED
      BY SMT, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11 DEF Inv

  <1>2. Inv /\ [Next]_vars => Inv'
    <2>1. \A a \in Agents: Inv /\ Register(a) => Inv'
      <3>1. \A a \in Agents: Inv /\ Register(a) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Register, GuardRegister, vars
      <3>2. \A a \in Agents: Inv /\ Register(a) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>3. \A a \in Agents: Inv /\ Register(a) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>4. \A a \in Agents: Inv /\ Register(a) => MessageStatus'
        BY Isa DEF Inv, Register, MessageStatus, Occ, Lea, Members
      <3>5. \A a \in Agents: Inv /\ Register(a) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>6. \A a \in Agents: Inv /\ Register(a) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>7. \A a \in Agents: Inv /\ Register(a) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>8. \A a \in Agents: Inv /\ Register(a) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>9. \A a \in Agents: Inv /\ Register(a) => LeaseNotInMailbox'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>10. \A a \in Agents: Inv /\ Register(a) => LeasePrecedes'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>11. \A a \in Agents: Inv /\ Register(a) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Register, GuardRegister, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>2. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => Inv'
      <3>1. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Bind, GuardBind, vars
      <3>2. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => BoundConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Bind, GuardBind
      <3>3. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => OwnerConsistent'
        BY SMTT(30) DEF Inv, TypeOK, BoundConsistent, OwnerConsistent, Bind, GuardBind
      <3>4. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => MessageStatus'
        BY Isa DEF Inv, Bind, MessageStatus, Occ, Lea, Members
      <3>5. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>6. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>7. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>8. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>9. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => LeaseNotInMailbox'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>10. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => LeasePrecedes'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>11. \A a \in Agents, b \in Boxes: Inv /\ Bind(a, b) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Bind, GuardBind, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>3. \A a \in Agents: Inv /\ Unbind(a) => Inv'
      <3>1. \A a \in Agents: Inv /\ Unbind(a) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Unbind, GuardUnbind, vars
      <3>2. \A a \in Agents: Inv /\ Unbind(a) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>3. \A a \in Agents: Inv /\ Unbind(a) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>4. \A a \in Agents: Inv /\ Unbind(a) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW a \in Agents, Inv, Unbind(a) PROVE MessageStatus'
          BY SMT
        <4>2. CASE lease[bound[a]] # None
          <5>1. bound[a] \in Boxes /\ lease[bound[a]] \in Messages
            BY SMTT(30), <4>1, <4>2 DEF Inv, TypeOK, Unbind, GuardUnbind
          <5>2. QED BY SMTT(30), <4>1, <4>2, <5>1, L_ReturnStatus DEF Unbind
        <4>3. CASE lease[bound[a]] = None
          <5>1. UNCHANGED <<mstatus, mailbox, lease, sender, origin>>
            BY <4>1, <4>3, SMTT(30) DEF Inv, TypeOK, Unbind, GuardUnbind
          <5>2. QED BY <4>1, <4>3, Isa, <5>1 DEF Inv, MessageStatus, Occ, Lea, Members
        <4>4. QED BY SMT, <4>1, <4>2, <4>3
      <3>5. \A a \in Agents: Inv /\ Unbind(a) => MailboxInv'
        <4>1. SUFFICES ASSUME NEW a \in Agents, Inv, Unbind(a) PROVE MailboxInv'
          BY SMT
        <4>2. CASE lease[bound[a]] # None
          <5>1. bound[a] \in Boxes /\ lease[bound[a]] \in Messages
            BY SMTT(30), <4>1, <4>2 DEF Inv, TypeOK, Unbind, GuardUnbind
          <5>2. QED BY SMTT(30), <4>1, <4>2, <5>1, L_ReturnMailbox DEF Unbind
        <4>3. CASE lease[bound[a]] = None
          <5>1. UNCHANGED <<mstatus, mailbox, lease, recipient, sentAt>>
            BY <4>1, <4>3, SMTT(30) DEF Inv, TypeOK, Unbind, GuardUnbind
          <5>2. QED BY <4>1, <4>3, SMTT(30), <5>1 DEF Inv, MailboxInv
        <4>4. QED BY SMT, <4>1, <4>2, <4>3
      <3>6. \A a \in Agents: Inv /\ Unbind(a) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>7. \A a \in Agents: Inv /\ Unbind(a) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>8. \A a \in Agents: Inv /\ Unbind(a) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>9. \A a \in Agents: Inv /\ Unbind(a) => LeaseNotInMailbox'
        BY SMT, L_HeadNotInTail, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_Card0NotMember DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>10. \A a \in Agents: Inv /\ Unbind(a) => LeasePrecedes'
        BY SMT, L_SortedInjective, L_MembersPrepend, L_MembersAppend, L_MembersTail, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>11. \A a \in Agents: Inv /\ Unbind(a) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Unbind, GuardUnbind, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>4. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => Inv'
      <3>1. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Send, GuardSend, vars
      <3>2. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>3. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>4. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW s \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Send(s, b, m) PROVE MessageStatus'
          BY SMT
        <4>2. Occ(m) = {} /\ Lea(m) = {}
          BY SMT, <4>1, L_Locations DEF Send, GuardSend
        <4>3a. \A x \in Boxes: (m \in Members(mailbox'[x])) <=> (m \in Members(mailbox[x]) \/ x = b)
          BY SMT, <4>1, OccAfterAppend DEF Send, Inv, TypeOK
        <4>3. \A x \in Boxes: (m \in Members(mailbox'[x])) <=> x = b
          BY SMT, <4>1, <4>2, <4>3a DEF Occ
        <4>4. Occ(m)' = {b} /\ Lea(m)' = {}
          BY SMT, <4>1, <4>2, <4>3 DEF Send, Occ, Lea
        <4>5. MessageClause(m)'
          BY <4>1, SMTT(30), <4>4, FS_EmptySet, FS_Singleton DEF MessageClause, Send, Inv, TypeOK
        <4>6. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
            BY <4>1, <5>1, SMTT(30), OccAfterAppendOther DEF Send, Inv, TypeOK
          <5>3. Occ(n)' = Occ(n) /\ Lea(n)' = Lea(n)
            BY SMT, <4>1, <5>1, <5>2 DEF Occ, Lea, Send
          <5>4. QED BY <4>1, <5>1, SMTT(30), <5>3 DEF Inv, TypeOK, MessageStatus, MessageClause, Send
        <4>7. QED BY SMT, <4>1, <4>5, <4>6 DEF MessageStatus, MessageClause
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
        <4>6. \A x \in Boxes: lease[x] # None => lease[x] # m
          BY <4>1, SMTT(30) DEF Inv, MailboxInv, Send, GuardSend
        <4>7. \A n \in Members(Append(mailbox[b], m)): recipient'[n] = b
          <5>1. SUFFICES ASSUME NEW n \in Members(Append(mailbox[b], m)) PROVE recipient'[n] = b
            BY SMT
          <5>2. n \in Members(mailbox[b]) \/ n = m
            BY SMT, <4>1, <5>1, L_MembersAppend DEF Inv, TypeOK
          <5>3. n \in Messages /\ (n = m \/ recipient[n] = b)
            BY SMT, <4>1, <5>2, L_RecipientMembers DEF Inv, TypeOK, Members
          <5>4. QED BY SMT, <4>1, <5>1, <5>3 DEF Inv, TypeOK, Send
        <4>8. BoxClause(b)'
          BY <4>1, SMTT(30), <4>4, <4>5, <4>6, <4>7
            DEF BoxClause, Sorted, Inv, TypeOK, MailboxInv, Send, GuardSend, LeasedSlots, Members
        <4>9. \A x \in Boxes \ {b}: BoxClause(x)'
          BY <4>1, SMTT(30), <4>2, <4>3, <4>6
            DEF BoxClause, Sorted, Inv, TypeOK, MailboxInv, Send
        <4>10. QED BY SMT, <4>8, <4>9 DEF BoxClause, MailboxInv
      <3>6. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>7. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>8. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>9. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => LeaseNotInMailbox'
        <4>1. SUFFICES ASSUME NEW s \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Send(s, b, m) PROVE LeaseNotInMailbox'
          BY SMT
        <4>2. \A x \in Boxes: lease[x] # None => lease[x] # m
          BY <4>1, SMTT(30) DEF Inv, MailboxInv, Send, GuardSend
        <4>3. Members(Append(mailbox[b], m)) = Members(mailbox[b]) \cup {m}
          BY SMT, <4>1, L_MembersAppend DEF Inv, TypeOK
        <4>4. QED BY <4>1, SMTT(30), <4>2, <4>3 DEF Inv, TypeOK, LeaseNotInMailbox, Send
      <3>10. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => LeasePrecedes'
        <4>1. SUFFICES ASSUME NEW s \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Send(s, b, m) PROVE LeasePrecedes'
          BY SMT
        <4>2. \A x \in Boxes: lease[x] # None =>
          /\ lease[x] # m /\ sentAt'[lease[x]] = sentAt[lease[x]] /\ sentAt[lease[x]] <= clock
          BY <4>1, SMTT(30) DEF Inv, TypeOK, MailboxInv, SentAtLeClock, Send, GuardSend
        <4>3. \A x \in Boxes: \A i \in DOMAIN mailbox[x]:
          /\ mailbox[x][i] # m /\ sentAt'[mailbox[x][i]] = sentAt[mailbox[x][i]]
          BY <4>1, SMTT(30), L_QueueFacts DEF Inv, TypeOK, Send, GuardSend
        <4>4. lease[b] # None =>
          \A i \in DOMAIN Append(mailbox[b], m): sentAt'[lease[b]] < sentAt'[Append(mailbox[b], m)[i]]
          <5>1. SUFFICES ASSUME lease[b] # None PROVE
            \A i \in DOMAIN Append(mailbox[b], m): sentAt'[lease[b]] < sentAt'[Append(mailbox[b], m)[i]]
            BY SMT
          <5>2. \A i \in DOMAIN mailbox[b]: sentAt'[lease[b]] < sentAt'[mailbox[b][i]]
            BY SMT, <4>1, <4>2, <4>3, <5>1 DEF Inv, LeasePrecedes
          <5>3. sentAt'[lease[b]] < sentAt'[m]
            BY SMT, <4>1, <4>2, <5>1 DEF Inv, TypeOK, Send
          <5>4. QED BY SMT, <4>1, <5>1, <5>2, <5>3, L_PrecedesAppend DEF Inv, TypeOK
        <4>5. QED BY <4>1, SMTT(30), <4>2, <4>3, <4>4
          DEF Inv, TypeOK, LeasePrecedes, Send
      <3>11. \A s \in Agents, b \in Boxes, m \in Messages: Inv /\ Send(s, b, m) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Send, GuardSend, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>5. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => Inv'
      <3>1. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Recv, GuardRecv, vars
      <3>2. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>3. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>4. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Recv(a, b, m) PROVE MessageStatus'
          BY SMT
        <4>2. mailbox[b] # <<>> /\ IsInjective(mailbox[b]) /\ m \in Members(mailbox[b])
          BY <4>1, SMTT(30), L_SortedInjective, HeadTailProperties DEF Inv, TypeOK, MailboxInv, Recv, GuardRecv, Members, Range
        <4>3. Occ(m) = {b} /\ Lea(m) = {}
          BY <4>1, SMTT(30), <4>2, L_UniqueLocation, L_Locations DEF Inv, MessageStatus, Recv, GuardRecv, Occ
        <4>4. \A x \in Boxes: m \notin Members(mailbox'[x])
          BY <4>1, SMTT(30), <4>2, <4>3, OccAfterTail DEF Recv, GuardRecv, Occ, Inv, TypeOK
        <4>5. Occ(m)' = {} /\ Lea(m)' = {b}
          BY <4>1, SMTT(30), <4>3, <4>4, L_LeaseUpdateSet DEF Recv, Occ, Lea
        <4>6. MessageClause(m)'
          BY <4>1, SMTT(30), <4>5, FS_EmptySet, FS_Singleton DEF MessageClause, Inv, TypeOK, MessageStatus, Recv, GuardRecv
        <4>7. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2. \A x \in Boxes: (n \in Members(mailbox'[x])) <=> (n \in Members(mailbox[x]))
            BY <4>1, <5>1, SMTT(30), <4>2, OccAfterTailOther DEF Recv, GuardRecv
          <5>3. Occ(n)' = Occ(n) /\ Lea(n)' = Lea(n)
            BY <4>1, <5>1, SMTT(30), <5>2, L_LeaseUpdateSet DEF Occ, Lea, Recv, GuardRecv
          <5>4. QED BY <4>1, <5>1, SMTT(30), <5>3 DEF Inv, TypeOK, MessageStatus, MessageClause, Recv
        <4>8. QED BY SMT, <4>1, <4>6, <4>7 DEF MessageStatus, MessageClause
      <3>5. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => MailboxInv'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Recv(a, b, m) PROVE MailboxInv'
          BY SMT
        <4>2. mailbox[b] # <<>> BY SMT, <4>1 DEF Recv, GuardRecv
        <4>3. Sorted(Tail(mailbox[b]), sentAt)
          BY SMT, <4>1, <4>2, L_SortedTail DEF Sorted, Inv, TypeOK, MailboxInv
        <4>4. Len(Tail(mailbox[b])) = Len(mailbox[b])-1
          BY SMT, <4>1, <4>2, HeadTailProperties DEF Inv, TypeOK
        <4>5. \A x \in Boxes: lease[x] # None => lease[x] # m
          BY <4>1, SMTT(30) DEF Inv, MailboxInv, Recv, GuardRecv
        <4>6. recipient[m] = b
          BY <4>1, SMTT(30), HeadTailProperties, LenProperties DEF Inv, TypeOK, MailboxInv, Recv, GuardRecv
        <4>7. QED BY <4>1, SMTT(30), <4>3, <4>4, <4>5, <4>6
          DEF Sorted, Inv, TypeOK, MailboxInv, Recv, GuardRecv, LeasedSlots
      <3>6. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>7. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>8. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>9. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => LeaseNotInMailbox'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Recv(a, b, m) PROVE LeaseNotInMailbox'
          BY SMT
        <4>2. mailbox[b] # <<>> /\ IsInjective(mailbox[b])
          BY SMT, <4>1, L_SortedInjective DEF Inv, TypeOK, MailboxInv, Recv, GuardRecv
        <4>3. m \notin Members(Tail(mailbox[b]))
          BY SMT, <4>1, <4>2, L_HeadNotInTail DEF Inv, TypeOK, Recv, GuardRecv
        <4>4. QED BY <4>1, SMTT(30), <4>3 DEF Inv, TypeOK, LeaseNotInMailbox, Recv
      <3>10. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => LeasePrecedes'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Recv(a, b, m) PROVE LeasePrecedes'
          BY SMT
        <4>2. mailbox[b] # <<>> BY SMT, <4>1 DEF Recv, GuardRecv
        <4>3. \A i \in DOMAIN Tail(mailbox[b]): sentAt[m] < sentAt[Tail(mailbox[b])[i]]
          BY SMT, <4>1, <4>2, L_SortedTail DEF Sorted, Inv, TypeOK, MailboxInv, Recv, GuardRecv
        <4>4. QED BY <4>1, SMTT(30), <4>3 DEF Inv, TypeOK, LeasePrecedes, Recv
      <3>11. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Recv(a, b, m) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Recv, GuardRecv, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>6. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => Inv'
      <3>1. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Ack, GuardAck, vars
      <3>2. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>3. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>4. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => MessageStatus'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Ack(a, b, m) PROVE MessageStatus'
          BY SMT
        <4>2. Occ(m) = {} /\ Lea(m) = {b}
          BY <4>1, SMTT(30), L_UniqueLocation, L_Locations DEF Inv, MessageStatus, Ack, GuardAck, Lea
        <4>3. Occ(m)' = {} /\ Lea(m)' = {}
          BY <4>1, SMTT(30), <4>2, L_LeaseUpdateSet DEF Ack, Occ, Lea
        <4>4. MessageClause(m)'
          BY <4>1, SMTT(30), <4>3, FS_EmptySet DEF MessageClause, Inv, TypeOK, MessageStatus, Ack, GuardAck
        <4>5. \A n \in Messages \ {m}: MessageClause(n)'
          <5>1. SUFFICES ASSUME NEW n \in Messages \ {m} PROVE MessageClause(n)'
            BY SMT
          <5>2a. \A x \in Boxes: (lease'[x] = n) <=> (lease[x] = n)
            BY <4>1, <5>1, SMTT(30) DEF Inv, TypeOK, Ack, GuardAck
          <5>2. Occ(n)' = Occ(n) /\ Lea(n)' = Lea(n)
            BY SMT, <4>1, <5>1, <5>2a DEF Occ, Lea, Ack
          <5>3. QED BY <4>1, <5>1, SMTT(30), <5>2 DEF Inv, TypeOK, MessageStatus, MessageClause, Ack
        <4>6. QED BY SMT, <4>1, <4>4, <4>5 DEF MessageStatus, MessageClause
      <3>5. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => MailboxInv'
        <4>1. SUFFICES ASSUME NEW a \in Agents, NEW b \in Boxes, NEW m \in Messages,
                    Inv, Ack(a, b, m) PROVE MailboxInv'
          BY SMT
        <4>2. \A x \in Boxes \ {b}: lease[x] # m
          BY <4>1, SMTT(30) DEF Inv, MailboxInv, Ack, GuardAck
        <4>3. QED BY <4>1, <4>2, SMTT(30)
          DEF Inv, TypeOK, MailboxInv, Ack, GuardAck, LeasedSlots
      <3>6. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>7. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>8. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>9. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => LeaseNotInMailbox'
        BY SMT, L_HeadNotInTail, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_Card0NotMember DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>10. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => LeasePrecedes'
        BY SMT, L_SortedInjective, L_MembersPrepend, L_MembersAppend, L_MembersTail, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>11. \A a \in Agents, b \in Boxes, m \in Messages: Inv /\ Ack(a, b, m) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Ack, GuardAck, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>7. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => Inv'
      <3>1. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Rollback, GuardRollback, vars
      <3>2. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>3. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>4. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => MessageStatus'
        BY SMTT(30), L_ReturnStatus DEF Inv, TypeOK, Rollback, GuardRollback
      <3>5. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => MailboxInv'
        BY SMTT(30), L_ReturnMailbox DEF Inv, TypeOK, Rollback, GuardRollback
      <3>6. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>7. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>8. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>9. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => LeaseNotInMailbox'
        BY SMT, L_HeadNotInTail, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_Card0NotMember DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>10. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => LeasePrecedes'
        BY SMT, L_SortedInjective, L_MembersPrepend, L_MembersAppend, L_MembersTail, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>11. \A a \in Agents, b \in Boxes: Inv /\ Rollback(a, b) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Rollback, GuardRollback, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>8. \A b \in Boxes: Inv /\ Reclaim(b) => Inv'
      <3>1. \A b \in Boxes: Inv /\ Reclaim(b) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Reclaim, GuardReclaim, vars
      <3>2. \A b \in Boxes: Inv /\ Reclaim(b) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>3. \A b \in Boxes: Inv /\ Reclaim(b) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>4. \A b \in Boxes: Inv /\ Reclaim(b) => MessageStatus'
        BY SMTT(30), L_ReturnStatus DEF Inv, TypeOK, Reclaim, GuardReclaim
      <3>5. \A b \in Boxes: Inv /\ Reclaim(b) => MailboxInv'
        BY SMTT(30), L_ReturnMailbox DEF Inv, TypeOK, Reclaim, GuardReclaim
      <3>6. \A b \in Boxes: Inv /\ Reclaim(b) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>7. \A b \in Boxes: Inv /\ Reclaim(b) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>8. \A b \in Boxes: Inv /\ Reclaim(b) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>9. \A b \in Boxes: Inv /\ Reclaim(b) => LeaseNotInMailbox'
        BY SMT, L_HeadNotInTail, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_Card0NotMember DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>10. \A b \in Boxes: Inv /\ Reclaim(b) => LeasePrecedes'
        BY SMT, L_SortedInjective, L_MembersPrepend, L_MembersAppend, L_MembersTail, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>11. \A b \in Boxes: Inv /\ Reclaim(b) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Reclaim, GuardReclaim, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>9. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => Inv'
      <3>1. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, Post, GuardPost, vars
      <3>2. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>3. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>4. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => MessageStatus'
        BY Isa DEF Inv, Post, MessageStatus, Occ, Lea, Members
      <3>5. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => MailboxInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>6. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>7. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>8. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>9. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => LeaseNotInMailbox'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>10. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => LeasePrecedes'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>11. \A a \in Agents, p \in Posts, t \in Topics, par \in Posts \cup {None}: Inv /\ Post(a, p, t, par) => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          Post, GuardPost, vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>10. Inv /\ UNCHANGED vars => Inv'
      <3>1. Inv /\ UNCHANGED vars => TypeOK'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Inv, TypeOK, vars
      <3>2. Inv /\ UNCHANGED vars => BoundConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>3. Inv /\ UNCHANGED vars => OwnerConsistent'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>4. Inv /\ UNCHANGED vars => MessageStatus'
        BY Isa DEF Inv, vars, MessageStatus, Occ, Lea, Members
      <3>5. Inv /\ UNCHANGED vars => MailboxInv'
        BY SMT, L_SortedInjective, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_MembersRange, L_Card0NotMember, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>6. Inv /\ UNCHANGED vars => PostsInv'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>7. Inv /\ UNCHANGED vars => PostedDistinct'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>8. Inv /\ UNCHANGED vars => PostedMembership'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>9. Inv /\ UNCHANGED vars => LeaseNotInMailbox'
        BY SMT, L_HeadNotInTail, L_MembersAppend, L_MembersPrepend, L_MembersTail, L_Card0NotMember DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>10. Inv /\ UNCHANGED vars => LeasePrecedes'
        BY SMT, L_SortedInjective, L_MembersPrepend, L_MembersAppend, L_MembersTail, L_QueueMailboxNotAcked DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>11. Inv /\ UNCHANGED vars => SentAtLeClock'
        BY SMT DEF
          MStatus, PStatus, None, LeasedSlots,
          Members, Occ, Lea, Inv, TypeOK, BoundConsistent, OwnerConsistent,
          MessageStatus, MailboxInv, PostsInv, PostedDistinct,
          PostedMembership, LeaseNotInMailbox, LeasePrecedes, SentAtLeClock,
          vars
      <3>12. QED
        BY SMT, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11 DEF Inv
    <2>11. QED
      BY SMT, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
         DEF Next, vars

  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

=======================================================================
