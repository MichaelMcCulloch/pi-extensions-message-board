------------------------- MODULE IdempotentPostProof -------------------------
EXTENDS MessageBoardProof
\* Payload equality (subject/body) is checked by the store; these opaque strings
\* are erased by the board projection. The identity and parent are not erased.
PostOnce(a,p,t,par) ==
  \/ Post(a,p,t,par)
  \/ /\ p \in Posts /\ pstatus[p] = "posted" /\ author[p] = a /\ topic[p] = t /\ parent[p] = par
     /\ UNCHANGED vars
THEOREM IdempotentPostRefinesBoard ==
  \A a \in Agents,p \in Posts,t \in Topics,par \in Posts \cup {None}: PostOnce(a,p,t,par) => [Next]_vars
  BY SMT DEF PostOnce, Next
THEOREM ExistingKeyDoesNotAppend ==
  \A a \in Agents,p \in Posts,t \in Topics,par \in Posts \cup {None}:
    pstatus[p] = "posted" /\ PostOnce(a,p,t,par) => UNCHANGED vars
  BY SMT DEF PostOnce, Post, GuardPost
=============================================================================
