----------------------- MODULE TendermintVotingProofs -----------------------
(***************************************************************************)
(* TLAPS proof of the safety properties of the abstract TendermintVoting   *)
(* spec: TypeOK, Validity, and Agreement.                                  *)
(*                                                                         *)
(* - Agreement reduces to PrecommitQuorumAgreement (two precommit quorums  *)
(*   decide the same value), the lock-chain core, which in turn reduces to *)
(*   PolkaDescent: a value-polka at round s >= r above a precommit quorum  *)
(*   for v at r is itself for v.                                           *)
(* - PolkaDescent is proved by course-of-values induction on s, using the  *)
(*   value-prevote justification invariant                                 *)
(*   (PrevoteAfterPrecommitJustification). The latter is STRICT (the       *)
(*   witness polka sits strictly below the prevote round) because the spec *)
(*   enforces prevote-before-precommit within a round.                     *)
(***************************************************************************)
EXTENDS TendermintVoting, NaturalsInduction

(***************************************************************************)
(* Auxiliary lemmas                                                        *)
(***************************************************************************)

\* nil is not an application value: the Russell set RR = {x \in Values : x \notin x}
\* cannot be in Values (RR \in RR <=> RR \notin RR), so it witnesses
\* \E v : v \notin Values, and the CHOOSE in nil lands outside Values.
LEMMA NilNotInValues == nil \notin Values
<1> DEFINE RR == { x \in Values : x \notin x }
<1>1. RR \notin Values
  BY DEF RR
<1>2. QED
  BY <1>1 DEF nil

\* A non-empty set of naturals bounded above has a greatest element (via the
\* least-number principle SmallestNatural). Used for the descent's max witness.
LEMMA NatSetMax ==
  ASSUME NEW S, S \subseteq Nat, S # {}, NEW bnd \in Nat, \A x \in S : x <= bnd
  PROVE  \E mx \in S : \A x \in S : x <= mx
<1> DEFINE UB(u) == \A x \in S : x <= u
<1>1. UB(bnd)
  OBVIOUS
<1>2. \E m \in Nat : UB(m) /\ (\A k \in 0..(m-1) : ~UB(k))
  <2> HIDE DEF UB
  <2> QED BY ONLY <1>1, SmallestNatural, IsaM("blast")
<1>3. PICK m \in Nat : UB(m) /\ (\A k \in 0..(m-1) : ~UB(k))
  BY <1>2
<1>4. m \in S
  <2>1. SUFFICES ASSUME m \notin S PROVE FALSE
    OBVIOUS
  <2>2. \A x \in S : x \in Nat /\ x <= m /\ x # m
    BY <1>3, <2>1 DEF UB
  <2>3. UB(m - 1)
    BY <2>2 DEF UB
  <2>4. PICK x0 \in S : TRUE
    BY <1>3, <2>1
  <2>5. m >= 1
    BY <2>2, <2>4
  <2>6. m - 1 \in 0..(m-1)
    BY <2>5
  <2>7. QED
    BY <1>3, <2>3, <2>6
<1>5. QED
  <2> WITNESS m \in S
  <2> QED BY <1>3 DEF UB

\* Quorum-existence is monotone in the message set: once a polka / commit
\* forms, it persists as sent grows.
LEMMA PrevoteQuorumMono ==
  ASSUME NEW w, NEW r, sent \subseteq sent', ExistsPrevoteQuorum(w, r)
  PROVE  ExistsPrevoteQuorum(w, r)'
BY DEFS ExistsPrevoteQuorum, PrevotesAt, PrevoteSendersFor, SentPrevotes

\* Every action either leaves sent unchanged or adds one message to it.
LEMMA SentGrows ==
  ASSUME Next
  PROVE  sent \subseteq sent'
BY DEF Next, Propose, PrevoteNil, PrevoteValue, PrecommitNil, PrecommitValue, Decide

\* Propose adds only a Proposal message (type "Proposal"), so it leaves the
\* vote-sets and the non-message state untouched. This collapses the Propose
\* case of every vote/lock/decision invariant: nothing those invariants
\* depend on changes. Quorum-existence persists by the *Mono lemmas (sent
\* grows).
LEMMA ProposeKeepsState ==
  ASSUME NEW r, Propose(r)
  PROVE  /\ SentPrevotes' = SentPrevotes
         /\ SentPrecommits' = SentPrecommits
         /\ sent \subseteq sent'
         /\ UNCHANGED << locked, decision >>
BY DEF Propose, Proposal, SentPrevotes, SentPrecommits

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
THEOREM TypeOKInv == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, LockState, ValuesOrNil
<1>2. ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  <2> USE <1>2 DEF TypeOK, ValuesOrNil, Message, Rounds
  <2>1. CASE Next
    BY <2>1 DEFS Decide, LockState, Next, Precommit, PrecommitMsg, PrecommitNil, PrecommitValue, 
      Prevote, PrevoteMsg, PrevoteNil, PrevoteValue, Proposal, ProposalMsg, Propose
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF TypeOK, vars
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Invariant: Decision implies a precommit quorum.                         *)
(***************************************************************************)
DecisionImpliesPrecommitQuorum ==
  \A p \in Validators :
    decision[p] \in Values => \E r \in Rounds : ExistsPrecommitQuorum(decision[p], r)

THEOREM DecisionImpliesPrecommitQuorumInv ==
  Spec => []DecisionImpliesPrecommitQuorum
<1>1. Init => DecisionImpliesPrecommitQuorum
  BY NilNotInValues DEF Init, DecisionImpliesPrecommitQuorum
<1>2. ASSUME TypeOK, DecisionImpliesPrecommitQuorum, [Next]_vars PROVE DecisionImpliesPrecommitQuorum'
  <2> USE <1>2 DEFS DecisionImpliesPrecommitQuorum
  <2>1. CASE UNCHANGED vars
    BY <2>1 DEFS vars, ExistsPrecommitQuorum, PrecommitSendersFor, PrecommitsAt, SentPrecommits
  <2>2. CASE Next
    BY <2>2, SentGrows
    DEFS Decide, ExistsPrecommitQuorum, Next, PrecommitNil, PrecommitsAt, PrecommitSendersFor, PrecommitValue, PrevoteNil, PrevoteValue, Propose, SentPrecommits, TypeOK
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: A value-precommit implies a polka for that value at the same *)
(* round (the PrecommitValue guard). Monotone in sent.                     *)
(***************************************************************************)
PrecommitHasPrevoteQuorum ==
  \A m \in SentPrecommits :
    m.valueID \in Values => ExistsPrevoteQuorum(m.valueID, m.round)

THEOREM PrecommitHasPrevoteQuorumInv == Spec => []PrecommitHasPrevoteQuorum
<1>1. Init => PrecommitHasPrevoteQuorum
  BY DEF Init, PrecommitHasPrevoteQuorum, SentPrecommits
<1>2. ASSUME TypeOK, PrecommitHasPrevoteQuorum, [Next]_vars PROVE PrecommitHasPrevoteQuorum'
  <2> USE <1>2 DEFS PrecommitHasPrevoteQuorum, SentPrecommits
  <2>1. CASE UNCHANGED vars
    BY <2>1 DEF vars, ExistsPrevoteQuorum, PrevoteSendersFor, PrevotesAt, SentPrevotes
  <2>2. CASE Next
    BY <2>2, NilNotInValues, PrevoteQuorumMono, SentGrows, ProposeKeepsState
    DEFS Propose, PrecommitNil, PrecommitValue, PrevoteNil, PrevoteValue, Decide, Next, Precommit, Prevote
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: A nonempty lock implies a polka for the locked value at the  *)
(* lock round (locking is coupled to PrecommitValue). Monotone in sent.    *)
(***************************************************************************)
LockedHasPrevoteQuorum ==
  \A p \in Validators :
    locked[p].round >= 0 =>
      /\ locked[p].value \in Values
      /\ ExistsPrevoteQuorum(locked[p].value, locked[p].round)

THEOREM LockedHasPrevoteQuorumInv == Spec => []LockedHasPrevoteQuorum
<1>1. Init => LockedHasPrevoteQuorum
  BY DEF Init, LockedHasPrevoteQuorum
<1>2. ASSUME TypeOK, LockedHasPrevoteQuorum, [Next]_vars PROVE LockedHasPrevoteQuorum'
  <2> USE <1>2 DEFS LockedHasPrevoteQuorum
  <2>1. CASE UNCHANGED vars
    BY <2>1 DEFS vars, ExistsPrevoteQuorum, PrevoteSendersFor, PrevotesAt, SentPrevotes
  <2>2. CASE Next
    BY <2>2, PrevoteQuorumMono, SentGrows
    DEFS Propose, PrecommitNil, PrecommitValue, PrevoteNil, PrevoteValue, Decide, Next, TypeOK
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: Each validator casts at most one prevote and one precommit   *)
(* per round (the NotYet... guards).                                       *)
(***************************************************************************)
VoteUniqueness ==
  /\ \A m1 \in SentPrevotes, m2 \in SentPrevotes :
       (m1.sender = m2.sender /\ m1.round = m2.round) => m1 = m2
  /\ \A m1 \in SentPrecommits, m2 \in SentPrecommits :
       (m1.sender = m2.sender /\ m1.round = m2.round) => m1 = m2

THEOREM VoteUniquenessInv == Spec => []VoteUniqueness
<1>1. Init => VoteUniqueness
  BY DEF Init, VoteUniqueness, SentPrevotes, SentPrecommits
<1>2. ASSUME TypeOK, VoteUniqueness, [Next]_vars PROVE VoteUniqueness'
  <2> USE <1>2 DEFS VoteUniqueness, SentPrevotes, SentPrecommits
  <2>1. CASE Next
    BY <2>1, ProposeKeepsState DEFS Decide, Next, NoPrecommitAtOrAboveRound, 
      NoPrevoteAtOrAboveRound, Precommit, PrecommitNil, PrecommitValue, 
      Prevote, PrevoteNil, PrevoteValue, Rounds
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars
  <2>3. QED
    BY <2>2, <2>1
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: Every value-precommit by p sits at a round <= p's lock       *)
(* round: locking is coupled to precommit-for-value, and the precommit     *)
(* guard makes the round monotone. This links precommit-quorum membership  *)
(* to the lock.                                                            *)
(***************************************************************************)
PrecommitBelowLock ==
  \A m \in SentPrecommits :
    m.valueID \in Values => locked[m.sender].round >= m.round

THEOREM PrecommitBelowLockInv == Spec => []PrecommitBelowLock
<1>1. Init => PrecommitBelowLock
  BY DEF Init, PrecommitBelowLock, SentPrecommits
<1>2. ASSUME TypeOK, PrecommitBelowLock, [Next]_vars PROVE PrecommitBelowLock'
  <2> USE <1>2 DEFS PrecommitBelowLock, SentPrecommits
  <2>1. CASE Next
    BY <2>1, NilNotInValues, ProposeKeepsState
    DEFS Decide, Message, Next, NoPrecommitAtOrAboveRound, Precommit, PrecommitMsg, PrecommitNil, PrecommitValue, Prevote, PrevoteMsg, PrevoteNil, PrevoteValue, ProposalMsg, Propose, Rounds, TypeOK, ValuesOrNil
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEFS vars
  <2>3. QED
    BY <2>2, <2>1
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: A set lock round is witnessed by the validator's own         *)
(* value-precommit at that round. Used to relate the current lock back to  *)
(* sent history.                                                           *)
(***************************************************************************)
LockedRoundHasPrecommitWitness ==
  \A p \in Validators :
    locked[p].round >= 0 =>
      \E m \in PrecommitsAt(locked[p].value, locked[p].round) : m.sender = p

THEOREM LockedRoundHasPrecommitWitnessInv == Spec => []LockedRoundHasPrecommitWitness
<1>1. Init => LockedRoundHasPrecommitWitness
  BY DEF Init, LockedRoundHasPrecommitWitness
<1>2. ASSUME TypeOK, LockedRoundHasPrecommitWitness, [Next]_vars
      PROVE  LockedRoundHasPrecommitWitness'
  <2> USE <1>2 DEFS LockedRoundHasPrecommitWitness, SentPrecommits, PrecommitsAt
  <2>1. CASE Next
    BY <2>1, SentGrows
    DEFS Decide, LockedRoundHasPrecommitWitness, Next, Precommit, PrecommitNil, PrecommitValue, PrevoteNil, PrevoteValue, Propose, TypeOK
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF LockedRoundHasPrecommitWitness, vars
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: If a validator value-precommitted at a lower round and later *)
(* value-prevoted, then either it prevoted that precommit's value or the   *)
(* later value already has a polka at some round between the precommit and *)
(* the prevote. The upper bound is <= the prevote round, not strict,       *)
(* because the abstract spec permits precommit-before-prevote in the same  *)
(* round.                                                                  *)
(***************************************************************************)
PrevoteAfterPrecommitJustification ==
  \A pc \in SentPrecommits, pv \in SentPrevotes :
    pc.sender = pv.sender /\ pc.valueID \in Values /\ pv.valueID \in Values /\ pc.round < pv.round =>
      \/ pc.valueID = pv.valueID
      \/ \E vr \in Rounds :
           /\ pc.round <= vr
           /\ vr < pv.round
           /\ ExistsPrevoteQuorum(pv.valueID, vr)

THEOREM PrevoteAfterPrecommitJustificationInv ==
  Spec => []PrevoteAfterPrecommitJustification
<1>1. Init => PrevoteAfterPrecommitJustification
  BY DEF Init, PrevoteAfterPrecommitJustification, SentPrecommits
<1>2. ASSUME TypeOK, VoteUniqueness, LockedHasPrevoteQuorum, PrecommitBelowLock,
             LockedRoundHasPrecommitWitness, PrevoteAfterPrecommitJustification,
             [Next]_vars
      PROVE  PrevoteAfterPrecommitJustification'
  BY <1>2, NilNotInValues, PrevoteQuorumMono, ProposeKeepsState, SentGrows
  DEFS Decide, ExistsPrevoteQuorum, LockedHasPrevoteQuorum, LockedRoundHasPrecommitWitness, 
    LockState, Message, Next, NoHigherRoundPrevote, NoPrecommitAtOrAboveRound, Precommit, 
    PrecommitBelowLock, PrecommitMsg, PrecommitNil, PrecommitsAt, PrecommitValue, Prevote, 
    PrevoteAfterPrecommitJustification, PrevoteMsg, PrevoteNil, PrevotesAt, PrevoteSendersFor, 
    PrevoteValue, ProposalMsg, Rounds, SentPrecommits, SentPrevotes, TypeOK, vars
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, VoteUniquenessInv, LockedHasPrevoteQuorumInv,
     PrecommitBelowLockInv, LockedRoundHasPrecommitWitnessInv, PTL DEF Spec

-----------------------------------------------------------------------------

\* A precommit quorum for a value implies a polka for it (any one member of the
\* quorum value-precommitted it, hence saw a polka).
LEMMA CommitImpliesPolka ==
  ASSUME TypeOK, PrecommitHasPrevoteQuorum,
         NEW w \in Values, NEW rr \in Rounds, ExistsPrecommitQuorum(w, rr)
  PROVE  ExistsPrevoteQuorum(w, rr)
BY PrecommitHasPrevoteQuorum, QuorumIntersection, Zenon
DEFS ExistsPrecommitQuorum, PrecommitHasPrevoteQuorum, PrecommitsAt, PrecommitSendersFor

\* Two quorum-covered sender sets share a validator member. This is the single
\* place QuorumIntersection (and QuorumType) is applied behind the same-round
\* and descent agreement arguments below.
LEMMA QuorumsShareSender ==
  ASSUME NEW S1, NEW S2,
         \E Q \in Quorum : Q \subseteq S1,
         \E Q \in Quorum : Q \subseteq S2
  PROVE  \E e \in Validators : e \in S1 /\ e \in S2
BY QuorumIntersection, QuorumType DEF QuorumType

\* Two same-round polkas are for the same value.
LEMMA SameRoundPolkaAgreement ==
  ASSUME TypeOK, VoteUniqueness,
         NEW v \in Values, NEW u \in Values, NEW r \in Rounds,
         ExistsPrevoteQuorum(v, r), ExistsPrevoteQuorum(u, r)
  PROVE  v = u
BY QuorumsShareSender 
DEFS ExistsPrevoteQuorum, PrevotesAt, PrevoteSendersFor, SentPrevotes, VoteUniqueness

(***************************************************************************)
(* Invariant: The descent, the heart of the lock chain. If a precommit     *)
(* quorum forms for value v at round r, then a polka (prevote quorum) for  *)
(* value u at any round s >= r must be for the same value, i.e. u = v.     *)
(* In short: once a value is committed at a round, no polka for a          *)
(* different value can ever form at that round or above. This is what      *)
(* prevents two distinct values from each gathering a precommit            *)
(* quorum, and so underlies Agreement.                                     *)
(***************************************************************************)
PolkaDescent ==
  \A r, s \in Rounds, v, u \in Values :
    r <= s /\ ExistsPrecommitQuorum(v, r) /\ ExistsPrevoteQuorum(u, s) => v = u

\* Proof by course-of-values induction on the polka round s.
\* - The inductive step picks e in (precommit quorum for v at r) INTERSECT
\*   (u-polka at s).
\* - e value-precommitted v at r and value-prevoted u at s.
\* - The justification invariant (PrevoteAfterPrecommitJustification) gives
\*   either u = v or a u-polka STRICTLY below s, on which the induction
\*   hypothesis closes u = v.
\* - Strictness of the justification (hence no same-round circularity) comes
\*   from the spec's prevote-before-precommit guard.
THEOREM PolkaDescentInv == Spec => []PolkaDescent
<1>1. ASSUME TypeOK, VoteUniqueness, PrecommitHasPrevoteQuorum, PrevoteAfterPrecommitJustification
      PROVE  PolkaDescent
  <2> DEFINE P(s) == \A r \in Rounds, v, u \in Values :
                       r <= s /\ ExistsPrecommitQuorum(v, r) /\ ExistsPrevoteQuorum(u, s) => v = u
  <2>1. \A s \in Nat : (\A s2 \in 0..(s-1) : P(s2)) => P(s)
    <3> TAKE s \in Nat
    <3> SUFFICES ASSUME \A s2 \in 0..(s-1) : P(s2),
                        NEW r \in Rounds, NEW v \in Values, NEW u \in Values,
                        r <= s, ExistsPrecommitQuorum(v, r), ExistsPrevoteQuorum(u, s)
                 PROVE  v = u
      BY DEF P
    <3>1. CASE r = s
      BY <1>1, <3>1, CommitImpliesPolka, SameRoundPolkaAgreement
    <3>2. CASE r < s
      <4>1. PICK e \in Validators : e \in PrecommitSendersFor(v, r) /\ e \in PrevoteSendersFor(u, s)
        BY QuorumsShareSender DEF ExistsPrecommitQuorum, ExistsPrevoteQuorum
      <4>2. PICK pc \in PrecommitsAt(v, r) : pc.sender = e
        BY <4>1 DEF PrecommitSendersFor
      <4>3. PICK pv \in PrevotesAt(u, s) : pv.sender = e
        BY <4>1 DEF PrevoteSendersFor
      <4>4. QED
        BY <1>1, <3>2, <4>2, <4>3
        DEFS P, PrecommitsAt, PrevoteAfterPrecommitJustification, PrevotesAt, Rounds
    <3>3. QED
      BY <3>1, <3>2 DEF Rounds
  <2>2. \A s \in Nat : P(s)
    <3> HIDE DEF P
    <3> QED BY ONLY <2>1, GeneralNatInduction, IsaM("blast")
  <2>3. QED
    BY <2>2 DEF PolkaDescent, P, Rounds
<1>2. QED
  BY <1>1, TypeOKInv, VoteUniquenessInv, PrecommitHasPrevoteQuorumInv,
     PrevoteAfterPrecommitJustificationInv, PTL DEF Spec

(***************************************************************************)
(* Invariant: The lock-chain core: any two precommit quorums (across any   *)
(* rounds) are for the same value. The abstract analogue of the            *)
(* operational proof's precommit agreement and lock-chain invariants.      *)
(* Reduced (below) to PolkaDescent via CommitImpliesPolka and a Nat round  *)
(* ordering; fully discharged.                                             *)
(***************************************************************************)
PrecommitQuorumAgreement ==
  \A v, w \in Values, r, r2 \in Rounds :
    ExistsPrecommitQuorum(v, r) /\ ExistsPrecommitQuorum(w, r2) => v = w

THEOREM PrecommitQuorumAgreementInv == Spec => []PrecommitQuorumAgreement
<1>1. TypeOK /\ PrecommitHasPrevoteQuorum /\ PolkaDescent => PrecommitQuorumAgreement
  <2> SUFFICES ASSUME TypeOK, PrecommitHasPrevoteQuorum, PolkaDescent,
                      NEW v \in Values, NEW w \in Values,
                      NEW r \in Rounds, NEW r2 \in Rounds,
                      ExistsPrecommitQuorum(v, r), ExistsPrecommitQuorum(w, r2)
               PROVE  v = w
    BY DEF PrecommitQuorumAgreement
  <2>0. r <= r2 \/ r2 <= r
    BY DEF Rounds
  <2>3. QED
    BY <2>0, CommitImpliesPolka DEF PolkaDescent
<1>2. QED
  BY <1>1, TypeOKInv, PrecommitHasPrevoteQuorumInv, PolkaDescentInv, PTL DEF Spec

(***************************************************************************)
(* Agreement: any two decided validators agree. Follows from               *)
(* DecisionImpliesPrecommitQuorum (each decision rests on a precommit      *)
(* quorum) and PrecommitQuorumAgreement (precommit quorums are unique).    *)
(***************************************************************************)
THEOREM AgreementInv == Spec => []Agreement
<1>1. TypeOK /\ DecisionImpliesPrecommitQuorum /\ PrecommitQuorumAgreement => Agreement
  BY DEFS TypeOK, DecisionImpliesPrecommitQuorum, PrecommitQuorumAgreement, Agreement, ValuesOrNil
<1>2. QED
  BY <1>1, TypeOKInv, DecisionImpliesPrecommitQuorumInv, PrecommitQuorumAgreementInv, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Validity: any decided value is application-valid (the Decide guard).    *)
(***************************************************************************)
THEOREM ValidityInv == Spec => []Validity
<1>1. Init => Validity
  BY DEF Init, Validity
<1>2. ASSUME TypeOK, Validity, [Next]_vars PROVE Validity'
  <2> USE <1>2
  <2>1. CASE Next
    BY <2>1 DEFS Next, TypeOK, Propose, PrecommitNil, PrecommitValue, PrevoteNil, PrevoteValue, Decide, Validity
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF Validity, vars
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Integrity: a decision, once set, never changes (Decide's                *)
(* decision[p]=nil guard). Stated as a step property under [][..]_vars.    *)
(***************************************************************************)
THEOREM IntegrityStepInv == Spec => []IntegrityStep
<1>1. ASSUME TypeOK, [Next]_vars PROVE IntegrityStep
  <2> USE <1>1
  <2> SUFFICES ASSUME NEW p \in Validators, decision[p] # nil PROVE decision'[p] = decision[p]
    BY DEF IntegrityStep
  <2>1. CASE Next
    BY <2>1 DEFS Next, TypeOK, Propose, PrecommitNil, PrecommitValue, PrevoteNil, PrevoteValue, Decide
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars
  <2>3. QED
    BY <2>1, <2>2
<1>2. QED
  BY <1>1, TypeOKInv, PTL DEF Spec

=============================================================================
\* Modification History
\* Created Jun 7 2026 by hvanz (Hernán Vanzetto)