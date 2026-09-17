--------------- MODULE TendermintPartialSyncTerminationCascadeRegion -----------
(***************************************************************************)
(* The propose ceiling, the first temporal stage, and the two region       *)
(* conjuncts with their latches.                                           *)
(*                                                                         *)
(* Owns CascadeCeiling, ProposalDated, ValidRecordValid,                   *)
(* ValidProposalValue, CascadeEntry, LockDatedAfterEntry,                  *)
(* LocksDominateOrDated, CascadeLockFloor, NilPrevoteBlocks,               *)
(* CascadeLockBelowRound and NilPrevoteRefusedOrTimedOut. The temporal     *)
(* exports are ClockUnbounded, ProposalReached, LocksDominateLatch,        *)
(* WRDurableLatch and NilPrevoteBlocksLatch.                               *)
(*                                                                         *)
(* The cut keeps items 11, 11b and 11c with BOTH latch wrappers in one     *)
(* link. A latch and the item it latches must not be separated, because    *)
(* a latch gives [](H => []X) and the region conjunct consumes it.         *)
(*                                                                         *)
(* THE CHAIN. Link 2 of 4. Above: ...CascadeInvariants. Below:             *)
(* ...CascadeCore.                                                         *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationCascadeInvariants

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 9: the propose ceiling.                                            *)
(*                                                                         *)
(* CascadeCeiling(p, r) is the instant by which the honest proposer of a   *)
(* good round r has to have proposed. Once the clock is above it, the      *)
(* round-r proposal is in the pool, dated at or below the ceiling.         *)
(*                                                                         *)
(*  Every conjunct of the antecedent is stable, and both disjuncts of the  *)
(*  conclusion are monotone. Only ONE step of the induction therefore does *)
(*  work. That step is the Tick which lifts the clock off the ceiling. The *)
(*  maximal-progress guard of Tick forces the proposal to be there         *)
(*  already. Absence of a round-r proposal makes ProposeEnabledFromAbsence *)
(*  fire, and an exit above r makes the backing chain fire and hit the     *)
(*  propose-timeout margin. Each outcome contradicts the guard.            *)
(***************************************************************************)
CascadeCeiling(p, r) == enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)

\* The margin, read at a round. TimeoutPropose(rr) clears the ceiling offset
\* Delta + TimeoutPrecommit(rr - 1) by a whole Delta.
LEMMA ProposeClearsCeiling ==
  ASSUME NEW rr \in Nat, rr > 0
  PROVE  TimeoutPropose(rr) > Delta + TimeoutPrecommit(rr - 1)
<1>1. rr * TDelta = (rr - 1) * TDelta + TDelta
  BY TDeltaType, SMT
<1> QED
  BY <1>1, DeltaType, ProposeTimeoutMargin, T0PrecommitType, T0ProposeType,
     TDeltaType, SMT
  DEFS TimeoutPrecommit, TimeoutPropose

\* The precommit timeout of any round is a positive natural. NO SMT here:
\* T0Precommit + rr * TDelta is NONLINEAR, and the default backends close it
\* from the Naturals closure facts while z3 searches.
LEMMA TimeoutPrecommitPos ==
  ASSUME NEW rr \in Nat
  PROVE  TimeoutPrecommit(rr) > 0 /\ TimeoutPrecommit(rr) \in Nat
BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit

\*  Two more minimal-context arithmetic facts. Every SMT call in this section
\*  is a TOP-LEVEL lemma with assumptions on constants only, and that is
\*  deliberate. Take an SMT leaf inside a proof whose ASSUME carries
\*  quantified invariants. That leaf gives z3 those invariants as axioms, and
\*  z3 then searches for hours.
LEMMA PredOfPositive ==
  ASSUME NEW n \in Nat, n > 0
  PROVE  n - 1 \in Nat
BY SMT

LEMMA SuccDistinct ==
  ASSUME NEW n \in Nat
  PROVE  n + 1 # n
BY SMT

LEMMA MinusNatBelow ==
  ASSUME NEW a \in Int, NEW k \in Int, k >= 0
  PROVE  a - k \in Int /\ a - k <= a
BY SMT

LEMMA GeFromEq ==
  ASSUME NEW a \in Int, NEW b \in Int, a = b
  PROVE  a >= b
BY SMT

LEMMA GeFromAbovePred ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a > b - 1
  PROVE  a >= b
BY SMT

LEMMA RegionIntLeTransitive ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int,
         a <= b, b <= c
  PROVE  a <= c
BY SMT

LEMMA RegionIntLtLeTransitive ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int,
         a < b, b <= c
  PROVE a < c
BY SMT

\* Every typing fact about a round and its predecessor, in ONE minimal-context
\* lemma. The proofs below carry eleven quantified invariants in their ASSUME,
\* and a backend asked to rediscover these facts there searches instead of
\* closing. Cite this and never inline the typing.
LEMMA RoundTypes ==
  ASSUME NEW rr \in Rounds, rr > 0
  PROVE  /\ rr \in Nat
         /\ rr - 1 \in Nat
         /\ rr - 1 \in Rounds
         /\ rr - 1 < rr
         /\ TimeoutPrecommit(rr - 1) \in Nat
         /\ TimeoutPrecommit(rr - 1) > 0
         /\ TimeoutPropose(rr) \in Nat
<1>1. rr \in Nat /\ rr - 1 \in Nat /\ rr - 1 < rr
  BY PredOfPositive DEF Rounds
<1> QED
  BY <1>1, T0PrecommitType, T0ProposeType, TDeltaType
  DEFS Rounds, TimeoutPrecommit, TimeoutPropose

\* Arithmetic in a minimal context. An entry at or after t0 whose propose
\* deadline clears the ceiling cannot have a prevote at or below the ceiling.
LEMMA CeilingBelowProposeDeadline ==
  ASSUME NEW t0 \in Int, NEW tc \in Int, NEW tp \in Int, NEW d \in Int,
         NEW x \in Int, NEW y \in Int,
         tp > d + tc, y >= t0, x >= y + tp, x <= t0 + d + tc
  PROVE  FALSE
BY SMT

\* A clock that has just recorded an entry cannot already be past that entry's
\* ceiling, not even after one tick.
LEMMA ClockBelowFreshEntry ==
  ASSUME NEW n \in Nat, NEW np \in Int, NEW d \in Int, NEW k \in Int,
         d > 1, k > 0, np = n \/ np = n + 1, np > n + d + k
  PROVE  FALSE
BY SMT

\* Only Tick moves the clock. This is the sibling of TickFromClockAdvance in
\* ...CrossRound, which sits on the other branch of the lattice.
LEMMA TickFromClockStep ==
  ASSUME TypeOK, [Next]_vars, now' = now + 1
  PROVE  Tick
<1>1. now + 1 # now
  BY SuccDistinct DEF TypeOK
<1> QED
  BY <1>1, NowStaysUnlessTick, Zenon

\* A decision is permanent. OnPrecommitQuorumValue is the only writer of
\* decision, and it is guarded on the slot being nil.
LEMMA DecidedLatchStep ==
  ASSUME TypeOK, [Next]_vars, SomeCorrectDecided
  PROVE  SomeCorrectDecided'
<1>1. PICK c \in Honest : decision[c] # nil
  BY DEFS HasDecided, SomeCorrectDecided
<1>2. decision'[c] # nil
  BY <1>1
  DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next,
    OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
    OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
    OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
    ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK,
    vars
<1> QED
  BY <1>1, <1>2 DEFS HasDecided, SomeCorrectDecided

\* The certificate of the previous round, read off CrossingBacked and weakened
\* to the entry instant. Top-level, because DatedCertWeaken's unification runs
\* under TWO quantifiers and cannot be done with the eleven invariants of
\* ProposalAtCeiling in scope.
LEMMA EntryCertificateDated ==
  ASSUME TypeOK, CrossingBacked, NEW p \in Honest, NEW r \in Rounds, r > 0,
         enteredAt[p][r] # OFF
  PROVE  AnyPrecommitDated(r - 1, enteredAt[p][r])
<1>ty. /\ r \in Nat /\ r - 1 \in Rounds /\ r - 1 < r
       /\ TimeoutPrecommit(r - 1) \in Nat /\ TimeoutPrecommit(r - 1) >= 0
  BY RoundTypes
<1>e. enteredAt[p][r] \in Nat
  BY DEFS OFF, TypeOK
<1>1. \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, r - 1, v) \in sent
        /\ sentTime[Precommit(s, r - 1, v)]
             <= enteredAt[p][r] - TimeoutPrecommit(r - 1)
  BY <1>ty DEF CrossingBacked
<1>2. /\ enteredAt[p][r] - TimeoutPrecommit(r - 1) \in Int
      /\ enteredAt[p][r] - TimeoutPrecommit(r - 1) <= enteredAt[p][r]
  BY <1>e, <1>ty, MinusNatBelow
<1>3. \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, r - 1, v) \in sent
        /\ sentTime[Precommit(s, r - 1, v)] <= enteredAt[p][r]
  BY <1>1, <1>2, <1>e, DatedCertWeaken
<1> QED
  BY <1>3 DEF AnyPrecommitDated

\* Every undecided correct validator is at or above r once the clock sits on
\* the ceiling. Top-level for the same reason as above.
LEMMA AllAboveEntryRound ==
  ASSUME TypeOK, EntryWindowCore, NEW p \in Honest, NEW r \in Rounds, r > 0,
         enteredAt[p][r] # OFF, enteredAt[p][r] >= GST,
         AnyPrecommitDated(r - 1, enteredAt[p][r]),
         now = enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1),
         ~ \E q \in Honest : CanCompute(q),
         \A cc \in Honest : step[cc] # "decided",
         NEW c \in Honest
  PROVE  round[c] >= r
<1>ty. /\ r \in Nat /\ r - 1 \in Rounds /\ TimeoutPrecommit(r - 1) \in Nat
  BY RoundTypes
<1>e. enteredAt[p][r] \in Nat
  BY DEFS OFF, TypeOK
<1>i. enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1) \in Int
  BY <1>e, <1>ty, DeltaType
<1>ge. now >= enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)
  BY <1>i, GeFromEq DEF TypeOK
<1>1. round[c] > r - 1
  BY <1>e, <1>ge, <1>ty, EntryReachedAtCeiling
<1>t2. round[c] \in Nat /\ r \in Nat
  BY <1>ty DEFS Rounds, TypeOK
<1> QED
  BY <1>1, <1>t2, GeFromAbovePred

\*  The state content of the ceiling. Take a state where the clock sits ON the
\*  ceiling, and where no correct validator has a computation step. The
\*  round-r proposal is already in the pool there.
LEMMA ProposalAtCeiling ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, EnteredAtLeNow,
         EnteredCurrentRound, CrossingBacked, PrecommitBacked,
         EntryWindowCore, StepPastProposeHasPrevote,
         PrevoteNeedsProposalOrTimeout, DecidedStepOp,
         NEW p \in Honest, NEW r \in Rounds, NEW q \in Honest,
         RoundOrigin(p, r), Proposer[r] = q,
         now = CascadeCeiling(p, r),
         ~ \E x \in Honest : CanCompute(x),
         ~ SomeCorrectDecided
  PROVE  \E v \in Values, vr \in Rounds \cup {-1} :
           /\ Proposal(q, r, v, vr) \in sent
           /\ sentTime[Proposal(q, r, v, vr)] <= CascadeCeiling(p, r)
<1>lr. /\ r \in Nat /\ r > 0 /\ r - 1 \in Rounds /\ r - 1 < r
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] >= GST
       /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta >= 0
       /\ TimeoutPrecommit(r - 1) \in Int
  <2>1. r > 0 /\ enteredAt[p][r] # OFF /\ enteredAt[p][r] > GST
    BY DEF RoundOrigin
  <2>2. /\ r \in Nat /\ r - 1 \in Rounds /\ r - 1 < r
        /\ TimeoutPrecommit(r - 1) \in Nat
    BY <2>1, RoundTypes
  <2>3. enteredAt[p][r] \in Nat /\ now \in Nat
    BY <2>1 DEFS OFF, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType, GSTType
<1>off. enteredAt[p][r] # OFF
  BY DEF RoundOrigin
<1>ap. AnyPrecommitDated(r - 1, enteredAt[p][r])
  BY <1>lr, <1>off, EntryCertificateDated
<1>nd. \A c \in Honest : step[c] # "decided"
  BY DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
\* Nobody correct is below r any more.
<1>ceil. now = enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)
  BY DEF CascadeCeiling
<1>up. \A c \in Honest : round[c] >= r
  <2> SUFFICES ASSUME NEW c \in Honest PROVE round[c] >= r
    OBVIOUS
  <2> QED
    BY <1>ap, <1>ceil, <1>lr, <1>nd, <1>off, AllAboveEntryRound
\* A pool record with the proposal fields IS an application of the constructor.
<1>rb. ASSUME NEW mm \in sent, mm.type = "Proposal", mm.round = r,
              mm.sender = q, sentTime[mm] <= CascadeCeiling(p, r)
       PROVE  \E v \in Values, vr \in Rounds \cup {-1} :
                /\ Proposal(q, r, v, vr) \in sent
                /\ sentTime[Proposal(q, r, v, vr)] <= CascadeCeiling(p, r)
  <2>1. /\ mm.value \in Values
        /\ mm.validRound \in Rounds \cup {-1}
        /\ mm = Proposal(mm.sender, mm.round, mm.value, mm.validRound)
    BY <1>rb, ProposalRecordRebuild DEF sent
  <2> QED
    BY <1>rb, <2>1
\* The last arrow, packaged. A correct prevote at r gives the proposal, or a
\* propose deadline that the margin puts above the ceiling.
<1>pv. ASSUME NEW c \in Honest, NEW w \in ValuesOrNil,
              Prevote(c, r, w) \in sent
       PROVE  \E v \in Values, vr \in Rounds \cup {-1} :
                /\ Proposal(q, r, v, vr) \in sent
                /\ sentTime[Proposal(q, r, v, vr)] <= CascadeCeiling(p, r)
  <2>1. /\ enteredAt[c][r] # OFF
        /\ \/ \E mm \in sent : /\ mm.type = "Proposal"
                               /\ mm.round = r
                               /\ mm.sender = Proposer[r]
                               /\ sentTime[mm] <= sentTime[Prevote(c, r, w)]
           \/ sentTime[Prevote(c, r, w)]
                >= enteredAt[c][r] + TimeoutPropose(r)
    BY <1>pv DEF PrevoteNeedsProposalOrTimeout
  <2>tp. TimeoutPropose(r) \in Nat
    BY <1>lr, RoundTypes
  <2>tm. Prevote(c, r, w) \in Message
    BY HonestSubValidators, MsgPrevote
  <2>ty. /\ sentTime[Prevote(c, r, w)] \in Int
         /\ enteredAt[c][r] \in Int
         /\ TimeoutPropose(r) \in Int
    BY <2>tm, <2>tp DEFS OFF, TypeOK
  <2>d. sentTime[Prevote(c, r, w)] <= now
    BY <1>pv, HonestSubValidators, MsgPrevote DEFS OFF, sent, SentTimeLeNow
  <2>a. CASE \E mm \in sent : /\ mm.type = "Proposal"
                              /\ mm.round = r
                              /\ mm.sender = Proposer[r]
                              /\ sentTime[mm] <= sentTime[Prevote(c, r, w)]
    <3>1. PICK mm \in sent : /\ mm.type = "Proposal"
                             /\ mm.round = r
                             /\ mm.sender = Proposer[r]
                             /\ sentTime[mm] <= sentTime[Prevote(c, r, w)]
      BY <2>a
    <3>2. sentTime[mm] \in Int
      BY <3>1 DEFS OFF, sent, TypeOK
    <3>3. sentTime[mm] <= CascadeCeiling(p, r)
      BY <1>lr, <2>d, <2>ty, <3>1, <3>2
    <3>4. mm.sender = q
      BY <3>1
    <3> QED
      BY <1>rb, <3>1, <3>3, <3>4
  <2>b. CASE sentTime[Prevote(c, r, w)]
               >= enteredAt[c][r] + TimeoutPropose(r)
    <3>1. enteredAt[c][r] >= enteredAt[p][r]
      BY <2>1 DEFS EntriesAtOrAfter, RoundOrigin
    <3>2. TimeoutPropose(r) > Delta + TimeoutPrecommit(r - 1)
      BY <1>lr, ProposeClearsCeiling
    <3>3. sentTime[Prevote(c, r, w)]
            <= enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)
      BY <2>d DEF CascadeCeiling
    <3>4. FALSE
      BY <1>lr, <2>b, <2>ty, <3>1, <3>2, <3>3, CeilingBelowProposeDeadline
    <3> QED
      BY <3>4
  <2> QED
    BY <2>1, <2>a, <2>b
\* The proposal is there: SentTimeLeNow dates it at the ceiling.
<1>pp. CASE \E v \in Values, vr \in Rounds \cup {-1} : Proposal(q, r, v, vr) \in sent
  <2>1. PICK v \in Values, vr \in Rounds \cup {-1} : Proposal(q, r, v, vr) \in sent
    BY <1>pp
  <2>2. sentTime[Proposal(q, r, v, vr)] <= now
    BY <2>1 DEFS OFF, sent, SentTimeLeNow
  <2> QED
    BY <2>1, <2>2
\* The proposal is missing. Both positions of p give a contradiction.
<1>np. CASE ~ \E v \in Values, vr \in Rounds \cup {-1} : Proposal(q, r, v, vr) \in sent
  <2>abs. \A v \in Values, vr \in Rounds \cup {-1} : Proposal(q, r, v, vr) \notin sent
    BY <1>np
  <2>a. CASE round[q] = r
    <3>1. step[q] # "propose"
      <4> SUFFICES ASSUME step[q] = "propose" PROVE FALSE
        OBVIOUS
      <4>1. CanCompute(q)
        BY <2>a, <2>abs, ProposeEnabledFromAbsence
      <4> QED
        BY <4>1
    <3>2. step[q] \in {"prevote", "precommit"}
      BY <1>nd, <3>1 DEFS Step, TypeOK
    <3>3. PICK w \in ValuesOrNil : Prevote(q, round[q], w) \in sent
      BY <3>2 DEF StepPastProposeHasPrevote
    <3> QED
      BY <1>pv, <2>a, <3>3
  <2>b. CASE round[q] > r
    <3>1. PICK h \in Honest, w \in ValuesOrNil :
            /\ Precommit(h, r, w) \in sent
            /\ sentTime[Precommit(h, r, w)] <= now - TimeoutPrecommit(r)
      BY <2>b, AboveNeedsCorrectPrecommit
    <3>m. Precommit(h, r, w) \in Message
      BY HonestSubValidators, MsgPrecommit
    <3>tp. TimeoutPrecommit(r) \in Nat
      BY <1>lr, TimeoutPrecommitPos
    <3>ty. /\ sentTime[Precommit(h, r, w)] \in Int
           /\ TimeoutPrecommit(r) \in Nat
      BY <3>m, <3>tp DEFS OFF, TypeOK
    <3>2. sentTime[Precommit(h, r, w)] <= now
      BY <1>lr, <3>1, <3>ty, LeMinusNat
    <3>3. \E h2 \in Honest, w2 \in ValuesOrNil :
            /\ Prevote(h2, r, w2) \in sent
            /\ sentTime[Prevote(h2, r, w2)] <= now
      BY <1>lr, <3>1, <3>2, PrecommitNeedsCorrectPrevote
    <3>4. PICK h2 \in Honest : \E w2 \in ValuesOrNil :
            /\ Prevote(h2, r, w2) \in sent
            /\ sentTime[Prevote(h2, r, w2)] <= now
      BY <3>3
    <3>5. PICK w2 \in ValuesOrNil : Prevote(h2, r, w2) \in sent
      BY <3>4
    <3> QED
      BY <1>pv, <3>5
  <2> QED
    BY <1>lr, <1>up, <2>a, <2>b DEF TypeOK
<1> QED
  BY <1>np, <1>pp

\*  The proposer of r need NOT be p. p is the first correct process into r.
\*  RoundOrigin(Proposer[r], r) does not follow from RoundOrigin(p, r),
\*  because EntriesAtOrAfter is anchored at the entry instant of its own
\*  process. The ceiling therefore stays p's, while the proposal is the
\*  proposer's.
ProposalDated ==
  \A p \in Honest, r \in Rounds :
    ( /\ RoundOrigin(p, r)
      /\ Proposer[r] \in Honest
      /\ now > CascadeCeiling(p, r) )
    => \/ SomeCorrectDecided
       \/ \E v \in Values, vr \in Rounds \cup {-1} :
            /\ Proposal(Proposer[r], r, v, vr) \in sent
            /\ sentTime[Proposal(Proposer[r], r, v, vr)]
                 <= CascadeCeiling(p, r)

LEMMA ProposalDatedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, RoundEntryHistory,
         EnteredAtLeNow, EnteredCurrentRound, CrossingBacked, PrecommitBacked,
         EntryWindowCore, StepPastProposeHasPrevote,
         PrevoteNeedsProposalOrTimeout, DecidedStepOp, [Next]_vars,
         ProposalDated
  PROVE  ProposalDated'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds,
                    RoundOrigin(p, r)', Proposer[r] \in Honest,
                    now' > CascadeCeiling(p, r)'
             PROVE  \/ SomeCorrectDecided'
                    \/ \E v \in Values, vr \in Rounds \cup {-1} :
                         /\ Proposal(Proposer[r], r, v, vr) \in sent'
                         /\ sentTime'[Proposal(Proposer[r], r, v, vr)]
                              <= CascadeCeiling(p, r)'
  BY DEF ProposalDated
<1>r0. /\ r \in Nat /\ r > 0 /\ r - 1 \in Nat
       /\ Delta \in Nat /\ Delta > 1
       /\ TimeoutPrecommit(r - 1) > 0 /\ TimeoutPrecommit(r - 1) \in Int
       /\ now \in Nat /\ now' \in Nat
  <2>1. r \in Nat /\ r > 0
    BY DEFS RoundOrigin, Rounds
  <2>2. r - 1 \in Nat
    BY <2>1, PredOfPositive
  <2>3. TimeoutPrecommit(r - 1) > 0 /\ TimeoutPrecommit(r - 1) \in Nat
    BY <2>2, TimeoutPrecommitPos
  <2>4. now \in Nat /\ now' \in Nat
    BY NowShape DEF TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, DeltaType
\*  The entry is missing before the step, so it can be recorded only AT the
\*  clock. A clock cannot be above its own instant plus a positive offset.
<1>a. CASE enteredAt[p][r] = OFF
  <2>1. enteredAt'[p][r] = now
    BY <1>a, EntryUpdateDisciplineStep
    DEFS EntryUpdateDiscipline, RoundOrigin
  <2>2. now' = now \/ now' = now + 1
    BY NowShape
  <2> QED
    BY <1>r0, <2>1, <2>2, ClockBelowFreshEntry DEF CascadeCeiling
<1>b. CASE enteredAt[p][r] # OFF
  <2>e. enteredAt'[p][r] = enteredAt[p][r]
    BY <1>b, EnteredAtFrozenStep
  <2>c. CascadeCeiling(p, r)' = CascadeCeiling(p, r)
    BY <2>e DEF CascadeCeiling
  <2>ro. RoundOrigin(p, r)
    <3>1. EntriesAtOrAfter(r, enteredAt[p][r])
      <4> SUFFICES ASSUME NEW c \in Honest, enteredAt[c][r] # OFF
                   PROVE  enteredAt[c][r] >= enteredAt[p][r]
        BY DEF EntriesAtOrAfter
      <4>1. enteredAt'[c][r] = enteredAt[c][r]
        BY EnteredAtFrozenStep
      <4> QED
        BY <2>e, <4>1 DEFS EntriesAtOrAfter, OFF, RoundOrigin
    <3> QED
      BY <1>b, <2>e, <3>1 DEF RoundOrigin
  <2>1. CASE now > CascadeCeiling(p, r)
    <3>1. \/ SomeCorrectDecided
          \/ \E v \in Values, vr \in Rounds \cup {-1} :
               /\ Proposal(Proposer[r], r, v, vr) \in sent
               /\ sentTime[Proposal(Proposer[r], r, v, vr)]
                    <= CascadeCeiling(p, r)
      BY <2>1, <2>ro DEF ProposalDated
    <3>2. CASE SomeCorrectDecided
      BY <3>2, DecidedLatchStep
    <3>3. CASE \E v \in Values, vr \in Rounds \cup {-1} :
                 /\ Proposal(Proposer[r], r, v, vr) \in sent
                 /\ sentTime[Proposal(Proposer[r], r, v, vr)]
                      <= CascadeCeiling(p, r)
      <4>1. PICK v \in Values, vr \in Rounds \cup {-1} :
              /\ Proposal(Proposer[r], r, v, vr) \in sent
              /\ sentTime[Proposal(Proposer[r], r, v, vr)]
                   <= CascadeCeiling(p, r)
        BY <3>3
      <4>2. Proposal(Proposer[r], r, v, vr) \in Message
        BY <4>1 DEF sent
      <4>3. sentTime'[Proposal(Proposer[r], r, v, vr)]
              = sentTime[Proposal(Proposer[r], r, v, vr)]
        BY <1>fz, <4>1, <4>2 DEF sent
      <4> QED
        BY <1>sub, <2>c, <4>1, <4>3
    <3> QED
      BY <3>1, <3>2, <3>3
\*  The clock crossed the ceiling at this step. The step is therefore a Tick
\*  from a state that sits exactly ON the ceiling, with no computation step
\*  available.
  <2>2. CASE ~ (now > CascadeCeiling(p, r))
    <3>ty. now \in Int /\ CascadeCeiling(p, r) \in Int
      BY <1>r0, <2>e DEFS CascadeCeiling, RoundOrigin, TypeOK
    <3>1. now' = now + 1
      BY <1>r0, <2>2, <2>c, <3>ty, NowShape
    <3>2. Tick
      BY <3>1, TickFromClockStep
    <3>3. now = CascadeCeiling(p, r)
      BY <1>r0, <2>2, <2>c, <3>1, <3>ty
    <3>4. ~ \E q \in Honest : CanCompute(q)
      BY <3>2 DEF Tick
    <3>5. CASE SomeCorrectDecided
      BY <3>5, DecidedLatchStep
    <3>6. CASE ~ SomeCorrectDecided
      <4>1. PICK v \in Values, vr \in Rounds \cup {-1} :
              /\ Proposal(Proposer[r], r, v, vr) \in sent
              /\ sentTime[Proposal(Proposer[r], r, v, vr)]
                   <= CascadeCeiling(p, r)
        BY <2>ro, <3>3, <3>4, <3>6, ProposalAtCeiling
      <4>2. Proposal(Proposer[r], r, v, vr) \in Message
        BY <4>1 DEF sent
      <4>3. sentTime'[Proposal(Proposer[r], r, v, vr)]
              = sentTime[Proposal(Proposer[r], r, v, vr)]
        BY <1>fz, <4>1, <4>2 DEF sent
      <4> QED
        BY <1>sub, <2>c, <4>1, <4>3
    <3> QED
      BY <3>5, <3>6
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>a, <1>b

THEOREM ProposalDatedInv == ASSUME Spec PROVE []ProposalDated
<1>1. ProposalDated
  BY DEFS Init, OFF, ProposalDated, RoundOrigin, Spec
<1>ds. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
             /\ RoundEntryHistory /\ EnteredAtLeNow /\ EnteredCurrentRound
             /\ CrossingBacked /\ PrecommitBacked /\ EntryWindowCore
             /\ StepPastProposeHasPrevote /\ PrevoteNeedsProposalOrTimeout
             /\ DecidedStepOp /\ [Next]_vars  )
  BY <1>ds, CrossingBackedInv, EnteredAtLeNowInv, EnteredCurrentRoundInv,
     EntryWindowCoreInv, InvProof, PrecommitBackedInv,
     PrevoteNeedsProposalOrTimeoutInv, PTL, RoundEntryHistoryInv, SentInvInv,
     SentTimeLeNowInv, StepPastProposeHasPrevoteInv
  DEFS Inv, Spec
<1>3. [](ProposalDated => ProposalDated')
  BY <1>2, ProposalDatedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The clock outruns any fixed bound. Moved up from ...LockRetry, which    *)
(* EXTENDS this module: the cascade stages below need the same fact, and   *)
(* a sibling module cannot be cited.                                       *)
(***************************************************************************)
\* ---- Item 3 of the count: the clock outruns any fixed bound ---------------
\* Both legs are Spec-FREE boxed lemmas with constant-only assumptions.
\* Necessitation (BY P, PTL for []P) fails with Spec in scope, so a boxed
\* identity can never be derived inside the theorem that consumes it.
LEMMA BoxRoundAboveClock ==
  ASSUME NEW b \in Nat
  PROVE  [](TypeOK /\ RoundBelowNow /\ RoundAbove(b) => now > b)
<1>1. TypeOK /\ RoundBelowNow /\ RoundAbove(b) => now > b
  BY DEFS RoundAbove, RoundBelowNow, Rounds, TypeOK
<1> QED
  BY <1>1, PTL

LEMMA BoxClockLatch ==
  ASSUME NEW b \in Nat
  PROVE  [](TypeOK /\ [Next]_vars /\ now > b => (now > b)')
\* NowShape and not NowMonotoneStep: the conclusion is at the PRIMED state, so
\* the leaf needs now' typed, and only the shape now' = now \/ now' = now + 1
\* delivers that from the unprimed TypeOK.
<1>1. TypeOK /\ [Next]_vars /\ now > b => (now > b)'
  BY NowShape DEF TypeOK
<1> QED
  BY <1>1, PTL

\*  The bound is named b, to match the binder of ProgressBeyond itself. To
\*  instantiate a quantifier over a TEMPORAL body works at a TAKEn constant,
\*  or at a NEW constant, of the IDENTICAL name. It works at nothing else.
THEOREM ClockUnbounded ==
  ASSUME Spec, []~SomeCorrectDecided, NEW b \in Nat
  PROVE  <>[](now > b)
<1>pb. <>SomeCorrectDecided \/ <>(now > GST /\ RoundAbove(b))
  BY PostGSTRoundProgress DEFS ProgressBeyond, Rounds
<1>inv. [](TypeOK /\ RoundBelowNow /\ [Next]_vars)
  BY InvProof, RoundBelowNowInv, PTL DEFS Inv, Spec
<1>ab. [](TypeOK /\ RoundBelowNow /\ RoundAbove(b) => now > b)
  BY BoxRoundAboveClock
<1>lt. [](TypeOK /\ [Next]_vars /\ now > b => (now > b)')
  BY BoxClockLatch
<1> QED
  BY <1>pb, <1>inv, <1>ab, <1>lt, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* An honest proposal carries a valid value.                               *)
(*                                                                         *)
(* ProposalStage asks for Valid(v) beside the justification, and nothing   *)
(* in the tree said this yet. Propose draws its value either from          *)
(* getValue, whose members are valid by definition, or from the proposer's *)
(* own valid record. The record is therefore typed first.                  *)
(***************************************************************************)

\* Both writers of the valid record, OnPrevoteQuorumValueFirstTime and
\* OnPrevoteQuorumValueLateUpdate, are guarded on Valid(prop.value).
ValidRecordValid ==
  \A c \in Honest : valid[c].value # nil => Valid(valid[c].value)

LEMMA ValidRecordValidStepL ==
  ASSUME TypeOK, [Next]_vars, ValidRecordValid
  PROVE  ValidRecordValid'
<1> SUFFICES ASSUME NEW c \in Honest, valid'[c].value # nil
             PROVE  Valid(valid'[c].value)
  BY DEF ValidRecordValid
\* Group 1: the record is untouched.
<1>1. CASE \/ (\E p \in Honest : Propose(p) \/ Deliver(p)
                 \/ OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                 \/ OnProposalWithPOL(p) \/ OnPrevoteQuorumNil(p)
                 \/ OnTimeoutPrevote(p) \/ ScheduleTimeoutPrevote(p)
                 \/ ScheduleTimeoutPrecommit(p) \/ OnPrecommitQuorumValue(p)
                 \/ OnTimeoutPrecommit(p)
                 \/ (\E rr \in Rounds : SkipRound(p, rr)))
           \/ (\E p \in Faulty : FaultyStep(p))
           \/ Tick
           \/ vars' = vars
  <2>1. valid' = valid
    BY <1>1
    DEFS Deliver, FaultyStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
      OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
      OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit,
      ScheduleTimeoutPrevote, SkipRound, Tick, vars
  <2> QED
    BY <2>1 DEF ValidRecordValid
\* Group 2: a write. Each writer's own guard carries the validity.
<1>2. CASE \E p \in Honest : OnPrevoteQuorumValueFirstTime(p)
                               \/ OnPrevoteQuorumValueLateUpdate(p)
  <2> PICK p \in Honest : OnPrevoteQuorumValueFirstTime(p)
                            \/ OnPrevoteQuorumValueLateUpdate(p)
    BY <1>2
  <2>1. CASE p # c
    <3>1. valid'[c] = valid[c]
      BY <2>1
      DEFS OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
        TypeOK
    <3> QED
      BY <3>1 DEF ValidRecordValid
  <2>a. CASE OnPrevoteQuorumValueFirstTime(c)
    <3>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
            /\ RExistsPrevoteQuorum(c, prop.value, round[c])
            /\ Valid(prop.value)
            /\ LET v == prop.value
                   newRecord == [value |-> v, round |-> round[c]]
               IN /\ locked' = [locked EXCEPT ![c] = newRecord]
                  /\ Broadcast(c, Precommit(c, round[c], v))
                  /\ step'   = [step EXCEPT ![c] = "precommit"]
                  /\ valid'  = [valid EXCEPT ![c] = newRecord]
      BY <2>a DEF OnPrevoteQuorumValueFirstTime
    <3> QED
      BY <3>1 DEF TypeOK
  <2>b. CASE OnPrevoteQuorumValueLateUpdate(c)
    <3>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
            /\ RExistsPrevoteQuorum(c, prop.value, round[c])
            /\ Valid(prop.value)
            /\ valid' = [valid EXCEPT ![c] =
                           [value |-> prop.value, round |-> round[c]]]
      BY <2>b DEF OnPrevoteQuorumValueLateUpdate
    <3> QED
      BY <3>1 DEF TypeOK
  <2> QED
    BY <2>1, <2>a, <2>b
<1> QED
  BY <1>1, <1>2
  DEFS HonestNext, HonestStep, Next, vars

THEOREM ValidRecordValidInv == ASSUME Spec PROVE []ValidRecordValid
<1>1. ValidRecordValid
  BY DEFS Init, ValidRecordValid, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ValidRecordValid => ValidRecordValid')
  BY <1>2, ValidRecordValidStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* Which action can activate a Proposal authored by a CORRECT validator: only
\* Propose. The sibling of FreshPrevoteAction.
LEMMA FreshProposalAction ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Proposal", mm.sender \in Honest
  PROVE  Propose(mm.sender)
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
                  => (mm = m0 /\ sentTime'[mm] = now)
  BY <1>0 DEF TypeOK
<1>1. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>1, <1>pin DEFS FaultyStep, Honest
<1>2. CASE \E p \in Honest : Propose(p)
  BY <1>2, <1>pin DEFS Broadcast, Proposal, Propose
<1>3. CASE \E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                                \/ OnProposalWithPOL(p))
  BY <1>3, <1>pin
  DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, Prevote
<1>4. CASE \E p \in Honest : (OnPrevoteQuorumValueFirstTime(p)
                                \/ OnPrevoteQuorumNil(p) \/ OnTimeoutPrevote(p))
  BY <1>4, <1>pin
  DEFS Broadcast, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
    OnTimeoutPrevote, Precommit
<1>5. CASE /\ ~(\E p \in Faulty : FaultyStep(p))
           /\ ~(\E p \in Honest : Propose(p))
           /\ ~(\E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                                     \/ OnProposalWithPOL(p)))
           /\ ~(\E p \in Honest : (OnPrevoteQuorumValueFirstTime(p)
                                     \/ OnPrevoteQuorumNil(p)
                                     \/ OnTimeoutPrevote(p)))
  BY <1>0, <1>5
  DEFS Deliver, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
    OnPrevoteQuorumValueLateUpdate, OnTimeoutPrecommit,
    ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

\* The value a fresh honest proposal carries is valid.
LEMMA FreshHonestProposalValid ==
  ASSUME TypeOK, ValidRecordValid, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Proposal", mm.sender \in Honest
  PROVE  Valid(mm.value)
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
<1>a. Propose(mm.sender)
  BY FreshProposalAction
<1>1. PICK v \in IF valid[mm.sender].value # nil
                 THEN {valid[mm.sender].value}
                 ELSE getValue :
        Broadcast(mm.sender,
          Proposal(mm.sender, round[mm.sender], v, valid[mm.sender].round))
  BY <1>a DEF Propose
<1>2. mm = Proposal(mm.sender, round[mm.sender], v, valid[mm.sender].round)
  BY <1>0, <1>1 DEFS Broadcast, TypeOK
<1>3. mm.value = v
  BY <1>2 DEF Proposal
<1>4. CASE valid[mm.sender].value # nil
  BY <1>1, <1>3, <1>4 DEF ValidRecordValid
<1>5. CASE valid[mm.sender].value = nil
  BY <1>1, <1>3, <1>5 DEF getValue
<1> QED
  BY <1>4, <1>5

ValidProposalValue ==
  \A q \in Honest, rr \in Rounds, v \in Values, vr \in Rounds \cup {-1} :
    Proposal(q, rr, v, vr) \in sent => Valid(v)

LEMMA ValidProposalValueStepL ==
  ASSUME TypeOK, ValidRecordValid, [Next]_vars, ValidProposalValue
  PROVE  ValidProposalValue'
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW q \in Honest, NEW rr \in Rounds, NEW v \in Values,
                    NEW vr \in Rounds \cup {-1}, Proposal(q, rr, v, vr) \in sent'
             PROVE  Valid(v)
  BY DEF ValidProposalValue
<1>m. Proposal(q, rr, v, vr) \in Message
  BY DEF sent
<1>f. /\ Proposal(q, rr, v, vr).type = "Proposal"
      /\ Proposal(q, rr, v, vr).sender = q
      /\ Proposal(q, rr, v, vr).value = v
  BY DEF Proposal
<1>1. CASE Proposal(q, rr, v, vr) \in sent
  BY <1>1 DEF ValidProposalValue
<1>2. CASE Proposal(q, rr, v, vr) \notin sent
  BY <1>2, <1>f, <1>m, FreshHonestProposalValid
<1> QED
  BY <1>1, <1>2

THEOREM ValidProposalValueInv == ASSUME Spec PROVE []ValidProposalValue
<1>1. ValidProposalValue
  BY DEFS Init, OFF, sent, Spec, ValidProposalValue
<1>2. [](TypeOK /\ ValidRecordValid /\ [Next]_vars)
  BY InvProof, PTL, ValidRecordValidInv DEF Spec, Inv
<1>3. [](ValidProposalValue => ValidProposalValue')
  BY <1>2, ValidProposalValueStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL




-----------------------------------------------------------------------------
(***************************************************************************)
(* S1. The hypothesis state leads to the proposal milestone.               *)
(*                                                                         *)
(* This stage is a CEILING plus an unbounded clock. It is not a WF1, and   *)
(* the ceiling shape is cheaper wherever one exists. ProposalDated already *)
(* puts the round-r proposal in the pool, dated at or below the ceiling,   *)
(* once the clock passes that ceiling. ClockUnbounded says the clock       *)
(* passes any fixed bound while no correct process decides. The two facts  *)
(* meet in one PTL step.                                                   *)
(*                                                                         *)
(*  THE CEILING CANNOT STAY A STATE FUNCTION. ClockUnbounded has a         *)
(*  TEMPORAL conclusion, so it matches only at a NEW constant of the       *)
(*  identical binder name b. The region below therefore PINS the ceiling   *)
(*  below such a b. The stage for each b is then proved, and the           *)
(*  existential over b is lifted afterwards. This is the shape that        *)
(*  ClockRegionBreaks uses for its own deadline.                           *)
(***************************************************************************)

\* The durable residue of a Lemma5Hyp state, with the ceiling pinned below a
\* constant. CascadeDurable already carries Proposer[r] \in Honest, inside
\* WRDurable(r).
CascadeEntry(p, r, b) == CascadeDurable(p, r) /\ CascadeCeiling(p, r) <= b

\* Two minimal-context arithmetic facts. The deadline is the ceiling plus one
\* gossip delay, which is what JustifiedWeaken has to cover.
LEMMA CeilingBelowDeadline ==
  ASSUME NEW e \in Nat, NEW d \in Nat, NEW k \in Nat
  PROVE  /\ e + d + k \in Nat
         /\ e + 2 * d + k \in Nat
         /\ e + d + k <= e + 2 * d + k
BY SMT

LEMMA GtFromPinned ==
  ASSUME NEW x \in Nat, NEW b \in Nat, NEW c \in Nat, x > b, c <= b
  PROVE  x > c
BY SMT

\* The clock conjunct of WRDurable across one step. np is left untyped on
\* purpose: the disjunction types it, so the call site needs no typing fact
\* beyond now \in Nat.
LEMMA GeAcrossTick ==
  ASSUME NEW n \in Nat, NEW g \in Nat, NEW np \in Int, n >= g,
         np = n \/ np = n + 1
  PROVE  np >= g
BY SMT

\*  The region latches. RoundOrigin is stable, by RoundOriginStep, and the
\*  clock only grows. The three timeout inequalities are constant, and the
\*  ceiling is frozen, because an entry slot is write once.
LEMMA BoxCascadeEntryLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ RoundEntryHistory /\ [Next]_vars
              /\ CascadeEntry(p, r, b) => CascadeEntry(p, r, b)'  )
<1>1. TypeOK /\ RoundEntryHistory /\ [Next]_vars /\ CascadeEntry(p, r, b)
        => CascadeEntry(p, r, b)'
  <2> SUFFICES ASSUME TypeOK, RoundEntryHistory, [Next]_vars,
                      CascadeEntry(p, r, b)
               PROVE  CascadeEntry(p, r, b)'
    OBVIOUS
  <2>ro. RoundOrigin(p, r) /\ WRDurable(r) /\ CascadeCeiling(p, r) <= b
    BY DEFS CascadeDurable, CascadeEntry
  <2>1. RoundOrigin(p, r)'
    BY <2>ro, RoundOriginStep
\* Only the clock conjunct of WRDurable can move. The other four read
\* Proposer, Delta and the three timeout constants, so priming is identity.
  <2>2. WRDurable(r)'
    <3>1. now >= GST /\ (now' = now \/ now' = now + 1)
      BY <2>ro, NowShape DEF WRDurable
    <3>2. now' >= GST
      BY <3>1, GSTType, GeAcrossTick DEF TypeOK
    <3> QED
      BY <2>ro, <3>2 DEF WRDurable
  <2>3. enteredAt'[p][r] = enteredAt[p][r]
    BY <2>ro, EnteredAtFrozenStep DEF RoundOrigin
  <2> QED
    BY <2>1, <2>2, <2>3, <2>ro
    DEFS CascadeCeiling, CascadeDurable, CascadeEntry
<1> QED
  BY <1>1, PTL

\* The entry into the region. The ceiling of the hypothesis state is itself a
\* natural, so it is its own witness for b.
LEMMA BoxCascadeEntryFromHyp ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ Lemma5Hyp(p, r)
              => (\E b \in Nat : CascadeEntry(p, r, b))  )
<1>1. TypeOK /\ Lemma5Hyp(p, r) => (\E b \in Nat : CascadeEntry(p, r, b))
  <2> SUFFICES ASSUME TypeOK, Lemma5Hyp(p, r)
               PROVE  \E b \in Nat : CascadeEntry(p, r, b)
    OBVIOUS
  <2>d. CascadeDurable(p, r)
    BY Lemma5HypDurable
  <2>ty. /\ enteredAt[p][r] \in Nat /\ Delta \in Nat
         /\ TimeoutPrecommit(r - 1) \in Nat
    <3>1. r > 0 /\ enteredAt[p][r] # OFF
      BY <2>d DEFS CascadeDurable, RoundOrigin
    <3>2. TimeoutPrecommit(r - 1) \in Nat
      BY <3>1, RoundTypes
    <3> QED
      BY <3>1, <3>2, DeltaType DEFS OFF, TypeOK
  <2>1. CascadeCeiling(p, r) \in Nat
    BY <2>ty DEF CascadeCeiling
  <2> QED
    BY <2>1, <2>d DEF CascadeEntry
<1> QED
  BY <1>1, PTL

\*  The state content of the stage. Above the pinned ceiling, ProposalDated
\*  puts the round-r proposal in the pool, with its date at or below the
\*  ceiling. ValidProposalValue types its value. ProposalJustified turns the
\*  dated proposal into a dated justification. JustifiedWeaken then lifts that
\*  date the one gossip delay up to the deadline.
LEMMA BoxProposalFromCeiling ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ ProposalDated /\ ProposalJustified /\ ValidProposalValue
              /\ ~SomeCorrectDecided /\ CascadeEntry(p, r, b) /\ now > b
              => ProposalMilestone(p, r)  )
<1>1. TypeOK /\ ProposalDated /\ ProposalJustified /\ ValidProposalValue
      /\ ~SomeCorrectDecided /\ CascadeEntry(p, r, b) /\ now > b
        => ProposalMilestone(p, r)
  <2> SUFFICES ASSUME TypeOK, ProposalDated, ProposalJustified,
                      ValidProposalValue, ~SomeCorrectDecided,
                      CascadeEntry(p, r, b), now > b
               PROVE  ProposalMilestone(p, r)
    OBVIOUS
  <2>d. /\ CascadeDurable(p, r)
        /\ RoundOrigin(p, r)
        /\ Proposer[r] \in Honest
        /\ CascadeCeiling(p, r) <= b
    BY DEFS CascadeDurable, CascadeEntry, WRDurable
  <2>ty. /\ enteredAt[p][r] \in Nat /\ Delta \in Nat
         /\ TimeoutPrecommit(r - 1) \in Nat
    <3>1. r > 0 /\ enteredAt[p][r] # OFF
      BY <2>d DEF RoundOrigin
    <3>2. TimeoutPrecommit(r - 1) \in Nat
      BY <3>1, RoundTypes
    <3> QED
      BY <3>1, <3>2, DeltaType DEFS OFF, TypeOK
  <2>ar. /\ CascadeCeiling(p, r) \in Nat
         /\ CascadeDeadline(p, r) \in Nat
         /\ CascadeCeiling(p, r) <= CascadeDeadline(p, r)
    BY <2>ty, CeilingBelowDeadline DEFS CascadeCeiling, CascadeDeadline
  <2>gt. now > CascadeCeiling(p, r)
    BY <2>ar, <2>d, GtFromPinned DEF TypeOK
  <2>1. PICK v \in Values, vr \in Rounds \cup {-1} :
          /\ Proposal(Proposer[r], r, v, vr) \in sent
          /\ sentTime[Proposal(Proposer[r], r, v, vr)] <= CascadeCeiling(p, r)
    BY <2>d, <2>gt DEF ProposalDated
  <2>2. Valid(v)
    BY <2>1, <2>d DEF ValidProposalValue
  <2>3. Justified(r, v, CascadeCeiling(p, r))
    BY <2>1, <2>ar, <2>d DEF ProposalJustified
  <2>4. Justified(r, v, CascadeDeadline(p, r))
    BY <2>3, <2>ar, JustifiedWeaken
  <2> QED
    BY <2>2, <2>4, <2>d DEFS ProposalMilestone, ProposalStage
<1> QED
  BY <1>1, PTL

\* The per-b stage. The ceiling is a constant here, so ClockUnbounded is cited
\* at b by identity, the only shape a temporal conclusion supports.
THEOREM ProposalReachedAt ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided,
         NEW b \in Nat
  PROVE  CascadeEntry(p, r, b) ~> ProposalMilestone(p, r)
<1>cu. <>[](now > b)
  BY ClockUnbounded
<1>nd. []~SomeCorrectDecided
  OBVIOUS
<1>inv. [](  TypeOK /\ RoundEntryHistory /\ ProposalDated /\ ProposalJustified
             /\ ValidProposalValue /\ [Next]_vars  )
  BY InvProof, ProposalDatedInv, ProposalJustifiedInv, PTL,
     RoundEntryHistoryInv, ValidProposalValueInv
  DEFS Inv, Spec
<1>la. [](  TypeOK /\ RoundEntryHistory /\ [Next]_vars
            /\ CascadeEntry(p, r, b) => CascadeEntry(p, r, b)'  )
  BY BoxCascadeEntryLatch
<1>go. [](  TypeOK /\ ProposalDated /\ ProposalJustified /\ ValidProposalValue
            /\ ~SomeCorrectDecided /\ CascadeEntry(p, r, b) /\ now > b
            => ProposalMilestone(p, r)  )
  BY BoxProposalFromCeiling
<1> QED
  BY <1>cu, <1>nd, <1>inv, <1>la, <1>go, PTL

\* ---- The existential lift over the pinned ceiling -------------------------
\* The temporal consequent is abstracted, so the first-order backend never
\* looks inside <>. This is the shape of ClockRegionCommute and
\* ClockRegionBoxFO in ...RoundProgress.
LEMMA CascadeEntryCommute ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW TEMPORAL D,
         \A b \in Nat : [](CascadeEntry(p, r, b) => D)
  PROVE  [](\A b \in Nat : (CascadeEntry(p, r, b) => D))
OBVIOUS

LEMMA CascadeEntryBoxFO ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  (\A b \in Nat :
                 (CascadeEntry(p, r, b) => <>ProposalMilestone(p, r)))
              => ((\E b \in Nat : CascadeEntry(p, r, b))
                    => <>ProposalMilestone(p, r))  )
<1>1. (\A b \in Nat : (CascadeEntry(p, r, b) => <>ProposalMilestone(p, r)))
      => ((\E b \in Nat : CascadeEntry(p, r, b))
            => <>ProposalMilestone(p, r))
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM ProposalReached ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided
  PROVE  Lemma5Hyp(p, r) ~> ProposalMilestone(p, r)
<1>1. \A b \in Nat : [](CascadeEntry(p, r, b) => <>ProposalMilestone(p, r))
  <2> SUFFICES ASSUME NEW b \in Nat
               PROVE  [](CascadeEntry(p, r, b) => <>ProposalMilestone(p, r))
    OBVIOUS
  <2>1. CascadeEntry(p, r, b) ~> ProposalMilestone(p, r)
    BY ProposalReachedAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A b \in Nat : (CascadeEntry(p, r, b) => <>ProposalMilestone(p, r)))
  BY <1>1, CascadeEntryCommute
<1>3. (\E b \in Nat : CascadeEntry(p, r, b)) ~> ProposalMilestone(p, r)
  BY <1>2, CascadeEntryBoxFO, PTL
<1>4. [](TypeOK /\ Lemma5Hyp(p, r) => (\E b \in Nat : CascadeEntry(p, r, b)))
  BY BoxCascadeEntryFromHyp
<1>ty. []TypeOK
  BY InvProof, PTL DEFS Inv, Spec
<1> QED
  BY <1>3, <1>4, <1>ty, PTL

-----------------------------------------------------------------------------
\* Kept in a clean Spec-free context, so PTL can necessitate it. Inside a
\* theorem that assumes Spec the temporal hypothesis is in scope and
\* necessitation is refused there. Item 11 and Lemma5OrPriorLock both cite it,
\* so it sits above both.
LEMMA Lemma5HypRoundOriginBox ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r))
<1>1. TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r)
  BY Lemma5HypImpliesRoundOrigin
<1> QED
  BY <1>1, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 11. LocksDominateOrDated, a REGION conjunct and not a global       *)
(* invariant.                                                              *)
(*                                                                         *)
(*  The refusal branch of the cascade reads the accept guard of            *)
(*  OnProposalWithPOL at a state LATER than the hypothesis state. Clause   *)
(*  (3) of Lemma5Hyp bounds every correct lock there and then, and a lock  *)
(*  written after the entry instant can break that bound. The region       *)
(*  conjunct says that the bound still holds, or that the offending lock   *)
(*  is DATED at or after the entry instant. That is precisely what         *)
(*  BlockingLockDuring asks for.                                           *)
(*                                                                         *)
(*  IT IS STATED AS A SEPARATE STABILITY THEOREM, not threaded through     *)
(*  ProposalMilestone. The hypothesis state establishes it, and every step *)
(*  preserves it. LocksDominateLatch therefore gives [] of it from the     *)
(*  hypothesis instant. One PTL step in the assembly then hands it to the  *)
(*  consumer, together with the milestone. Threading it through every Box  *)
(*  wrapper of S1 would cost the same information and re-open a closed     *)
(*  stage.                                                                 *)
(*                                                                         *)
(* TWO clauses, ONE induction. Clause (1) is anchored at                   *)
(* valid[Proposer[r]].round, which only grows, and it is what supplies     *)
(* clause (2) at the instant the round-r proposal first appears. Clause    *)
(* (2) is anchored at the validRound of that proposal, and it is what the  *)
(* consumer reads. Neither clause is inductive on its own.                 *)
(***************************************************************************)

\* The dated half. The guard of LockBackedByPrecommit is locked[c].round >= 0,
\* so this predicate is written against the same guard and composes with it.
LockDatedAfterEntry(p, r, c) ==
  /\ locked[c].round >= 0
  /\ Precommit(c, locked[c].round, locked[c].value) \in sent
  /\ sentTime[Precommit(c, locked[c].round, locked[c].value)]
       >= enteredAt[p][r]

\* Proposer[r] \in Honest is carried as a conjunct, not proved. Lemma5Hyp
\* supplies it at the entry, it is a CONSTANT predicate, so every step keeps it,
\* and it makes the faulty-proposer case of clause (1) vacuous.
LocksDominateOrDated(p, r) ==
  /\ Proposer[r] \in Honest
  /\ \A c \in Honest :
       \/ locked[c].round <= valid[Proposer[r]].round
       \/ LockDatedAfterEntry(p, r, c)
  /\ \A c \in Honest, v \in Values, vr \in Rounds \cup {-1} :
       Proposal(Proposer[r], r, v, vr) \in sent =>
         \/ locked[c].round <= vr
         \/ locked[c].value = v
         \/ LockDatedAfterEntry(p, r, c)

\* Only OnPrevoteQuorumValueFirstTime writes locked. Its sibling
\* OnPrevoteQuorumValueLateUpdate writes valid alone. The cases are split into
\* groups on purpose: one bundled leaf over fourteen actions exhausts the
\* backend.
LEMMA LockWriteIsFirstTime ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, locked'[c] # locked[c]
  PROVE  OnPrevoteQuorumValueFirstTime(c)
<1>1. CASE \/ (\E d \in Honest : Propose(d) \/ Deliver(d)
                 \/ OnTimeoutPropose(d) \/ OnProposalNoPOL(d)
                 \/ OnProposalWithPOL(d) \/ OnPrevoteQuorumNil(d)
                 \/ OnTimeoutPrevote(d) \/ ScheduleTimeoutPrevote(d)
                 \/ ScheduleTimeoutPrecommit(d) \/ OnPrecommitQuorumValue(d)
                 \/ OnTimeoutPrecommit(d)
                 \/ OnPrevoteQuorumValueLateUpdate(d)
                 \/ (\E rr \in Rounds : SkipRound(d, rr)))
           \/ (\E d \in Faulty : FaultyStep(d))
           \/ Tick
           \/ vars' = vars
  <2>1. locked' = locked
    BY <1>1
    DEFS Deliver, FaultyStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
      OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
      OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
      ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
  <2> QED
    BY <2>1
<1>2. CASE \E d \in Honest : OnPrevoteQuorumValueFirstTime(d)
  <2> PICK d \in Honest : OnPrevoteQuorumValueFirstTime(d)
    BY <1>2
  <2>1. CASE d # c
    <3>1. locked'[c] = locked[c]
      BY <2>1 DEFS OnPrevoteQuorumValueFirstTime, TypeOK
    <3> QED
      BY <3>1
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2
  DEFS HonestNext, HonestStep, Next, vars

\* The valid round of any correct validator only grows. Every write sets it to
\* round[c], which is itself monotone, and ValidBelowRound caps the old value by
\* the old round.
LEMMA ValidRoundMonotoneStep ==
  ASSUME TypeOK, TypeOK', ValidBelowRound, [Next]_vars, NEW c \in Honest
  PROVE  valid[c].round <= valid'[c].round
\*  One typing fact per step. TypeOK' and not TypeOK carries the PRIMED
\*  record: the unprimed typing says nothing about it. To bundle the five
\*  facts into one leaf makes the backend unfold TypeOK twice, and apply the
\*  monotonicity lemma at the same time. The backend then exhausts its
\*  resources.
<1>v. c \in Validators
  BY HonestSubValidators
<1>i. valid[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>ip. valid'[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>r. round[c] \in Nat /\ round'[c] \in Nat /\ round[c] <= round'[c]
  BY <1>v, CrossRoundMonotoneStep DEFS Rounds, TypeOK
<1>1. CASE valid'[c] = valid[c]
  BY <1>1, <1>i
<1>2. CASE valid'[c] # valid[c]
  <2>1. valid'[c].round = round[c]
    <3>1. CASE \/ (\E d \in Honest : Propose(d) \/ Deliver(d)
                     \/ OnTimeoutPropose(d) \/ OnProposalNoPOL(d)
                     \/ OnProposalWithPOL(d) \/ OnPrevoteQuorumNil(d)
                     \/ OnTimeoutPrevote(d) \/ ScheduleTimeoutPrevote(d)
                     \/ ScheduleTimeoutPrecommit(d)
                     \/ OnPrecommitQuorumValue(d) \/ OnTimeoutPrecommit(d)
                     \/ (\E rr \in Rounds : SkipRound(d, rr)))
               \/ (\E d \in Faulty : FaultyStep(d))
               \/ Tick
               \/ vars' = vars
      <4>1. valid' = valid
        BY <3>1
        DEFS Deliver, FaultyStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
          OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
          OnTimeoutPrevote, OnTimeoutPropose, Propose,
          ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick,
          vars
      <4> QED
        BY <1>2, <4>1
    <3>2. CASE \E d \in Honest : OnPrevoteQuorumValueFirstTime(d)
                                   \/ OnPrevoteQuorumValueLateUpdate(d)
      <4> PICK d \in Honest : OnPrevoteQuorumValueFirstTime(d)
                                \/ OnPrevoteQuorumValueLateUpdate(d)
        BY <3>2
      <4>1. CASE d # c
        BY <1>2, <4>1
        DEFS OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
          TypeOK
      <4>2. CASE d = c
        BY <4>2
        DEFS OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
          TypeOK
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>1, <3>2 DEFS HonestNext, HonestStep, Next, vars
  <2>2. valid[c].round <= round[c]
    BY DEF ValidBelowRound
  <2> QED
    BY <1>i, <1>ip, <1>r, <2>1, <2>2
<1> QED
  BY <1>1, <1>2

\*  A write to locked leaves the DATED half behind. The action broadcasts the
\*  matching precommit in the same step. PrecommitFresh shows that the slot
\*  was empty, so the new timestamp is now. The region puts now at or after
\*  the entry instant.
LEMMA FreshLockIsDated ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, EnteredAtLeNow, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         RoundOrigin(p, r), enteredAt'[p][r] = enteredAt[p][r],
         locked'[c] # locked[c]
  PROVE  LockDatedAfterEntry(p, r, c)'
<1>a. OnPrevoteQuorumValueFirstTime(c)
  BY LockWriteIsFirstTime
<1>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
        /\ Valid(prop.value)
        /\ locked' = [locked EXCEPT ![c] = [value |-> prop.value,
                                            round |-> round[c]]]
        /\ Broadcast(c, Precommit(c, round[c], prop.value))
  BY <1>a DEF OnPrevoteQuorumValueFirstTime
<1>2. /\ locked'[c].round = round[c]
      /\ locked'[c].value = prop.value
  BY <1>1 DEF TypeOK
\* The message is typed FIRST. sentTime' comes from an EXCEPT, and an EXCEPT
\* reports a value only inside the function's own domain.
<1>v. prop.value \in Values
  BY <1>1, RProposalValueType DEFS Rounds, TypeOK
<1>m. Precommit(c, round[c], prop.value) \in Message
  BY <1>v, HonestSubValidators, MsgPrecommit DEFS Rounds, TypeOK, ValuesOrNil
<1>3. sentTime'[Precommit(c, round[c], prop.value)] = now
  BY <1>1, <1>m DEFS Broadcast, TypeOK
<1>4. Precommit(c, round[c], prop.value) \in sent'
  <2>ty. now \in Nat
    BY DEF TypeOK
  <2> QED
    BY <1>3, <1>m, <2>ty DEFS OFF, sent
<1>5. now >= enteredAt[p][r]
  BY DEFS EnteredAtLeNow, RoundOrigin, TypeOK
<1>6. round[c] >= 0
  BY DEFS Rounds, TypeOK
<1> QED
  BY <1>2, <1>3, <1>4, <1>5, <1>6 DEF LockDatedAfterEntry

\* And an untouched lock keeps it: the pool only grows, an activated timestamp
\* never changes again, and the entry slot is write once.
LEMMA KeptLockStaysDated ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         enteredAt'[p][r] = enteredAt[p][r], locked'[c] = locked[c],
         LockDatedAfterEntry(p, r, c)
  PROVE  LockDatedAfterEntry(p, r, c)'
<1>1. /\ locked[c].round >= 0
      /\ Precommit(c, locked[c].round, locked[c].value) \in sent
      /\ sentTime[Precommit(c, locked[c].round, locked[c].value)]
           >= enteredAt[p][r]
  BY DEF LockDatedAfterEntry
<1>2. Precommit(c, locked[c].round, locked[c].value) \in Message
  BY <1>1 DEF sent
<1>3. /\ Precommit(c, locked[c].round, locked[c].value) \in sent'
      /\ sentTime'[Precommit(c, locked[c].round, locked[c].value)]
           = sentTime[Precommit(c, locked[c].round, locked[c].value)]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <1>1, <1>2, <2>1, SentMonotoneStep
    DEFS OFF, sent, SentTimeFrozenPred, vars
<1> QED
  BY <1>1, <1>3 DEF LockDatedAfterEntry

LEMMA LocksDominateOrDatedStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, RoundEntryHistory,
         ValidBelowRound, EnteredAtLeNow, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds,
         RoundOrigin(p, r), LocksDominateOrDated(p, r)
  PROVE  LocksDominateOrDated(p, r)'
<1>e. enteredAt'[p][r] = enteredAt[p][r]
  BY EnteredAtFrozenStep DEF RoundOrigin
\* The dated half travels either way, so the whole induction reduces to the two
\* bounds.
<1>d. ASSUME NEW c \in Honest, LockDatedAfterEntry(p, r, c)
      PROVE  LockDatedAfterEntry(p, r, c)'
  <2>1. CASE locked'[c] = locked[c]
    BY <1>d, <1>e, <2>1, KeptLockStaysDated
  <2>2. CASE locked'[c] # locked[c]
    BY <1>e, <2>2, FreshLockIsDated
  <2> QED
    BY <2>1, <2>2
<1>w. ASSUME NEW c \in Honest, locked'[c] # locked[c]
      PROVE  LockDatedAfterEntry(p, r, c)'
  BY <1>e, <1>w, FreshLockIsDated
\* Clause (1). The anchor valid[Proposer[r]].round only grows.
<1>1. \A c \in Honest :
        \/ locked'[c].round <= valid'[Proposer[r]].round
        \/ LockDatedAfterEntry(p, r, c)'
  <2> SUFFICES ASSUME NEW c \in Honest, ~ LockDatedAfterEntry(p, r, c)'
               PROVE  locked'[c].round <= valid'[Proposer[r]].round
    OBVIOUS
  <2>q. Proposer[r] \in Honest
    BY DEF LocksDominateOrDated
  <2>k. locked'[c] = locked[c]
    BY <1>w
  <2>o. locked[c].round <= valid[Proposer[r]].round
    BY <1>d DEF LocksDominateOrDated
  <2>1. valid[Proposer[r]].round <= valid'[Proposer[r]].round
    BY <2>q, ValidRoundMonotoneStep
  <2>ty. /\ locked[c].round \in Int /\ valid[Proposer[r]].round \in Int
         /\ valid'[Proposer[r]].round \in Int
    BY <2>q, HonestSubValidators DEFS LockState, Rounds, TypeOK
  <2> QED
    BY <2>k, <2>o, <2>1, <2>ty
\* Clause (2). A fresh round-r proposal can only come from Propose, and Propose
\* reads vr off valid[Proposer[r]].round, which is exactly the anchor of
\* clause (1).
<1>2. \A c \in Honest, v \in Values, vr \in Rounds \cup {-1} :
        Proposal(Proposer[r], r, v, vr) \in sent' =>
          \/ locked'[c].round <= vr
          \/ locked'[c].value = v
          \/ LockDatedAfterEntry(p, r, c)'
  <2> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW vr \in Rounds \cup {-1},
                      Proposal(Proposer[r], r, v, vr) \in sent',
                      ~ LockDatedAfterEntry(p, r, c)'
               PROVE  locked'[c].round <= vr \/ locked'[c].value = v
    OBVIOUS
  <2>k. locked'[c] = locked[c]
    BY <1>w
  <2>1. CASE Proposal(Proposer[r], r, v, vr) \in sent
    BY <1>d, <2>1, <2>k DEF LocksDominateOrDated
  <2>2. CASE Proposal(Proposer[r], r, v, vr) \notin sent
    <3>m. Proposal(Proposer[r], r, v, vr) \in Message
      BY DEF sent
    <3>f. /\ Proposal(Proposer[r], r, v, vr).type = "Proposal"
          /\ Proposal(Proposer[r], r, v, vr).sender = Proposer[r]
          /\ Proposal(Proposer[r], r, v, vr).validRound = vr
      BY DEF Proposal
    <3>q. Proposer[r] \in Honest
      BY DEF LocksDominateOrDated
    <3>a. Propose(Proposer[r])
      BY <2>2, <3>f, <3>m, <3>q, FreshProposalAction
    <3>1. PICK w \in IF valid[Proposer[r]].value # nil
                     THEN {valid[Proposer[r]].value}
                     ELSE getValue :
            Broadcast(Proposer[r],
              Proposal(Proposer[r], round[Proposer[r]], w,
                       valid[Proposer[r]].round))
      BY <3>a DEF Propose
    <3>2. vr = valid[Proposer[r]].round
      <4>1. Proposal(Proposer[r], r, v, vr)
              = Proposal(Proposer[r], round[Proposer[r]], w,
                         valid[Proposer[r]].round)
        BY <2>2, <3>1, <3>m DEFS Broadcast, sent, TypeOK
      <4> QED
        BY <4>1 DEF Proposal
    <3>3. locked[c].round <= valid[Proposer[r]].round
      BY <1>d, <3>q DEF LocksDominateOrDated
    <3> QED
      BY <2>k, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1>q. Proposer[r] \in Honest
  BY DEF LocksDominateOrDated
<1> QED
  BY <1>1, <1>2, <1>q DEF LocksDominateOrDated

\* The entry. Clause (3) of Lemma5Hyp is clause (1) verbatim, and CaseA turns
\* it into clause (2).
LEMMA Lemma5HypGivesLocksDominate ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds,
         Lemma5Hyp(p, r), CaseA(p, r)
  PROVE  LocksDominateOrDated(p, r)
<1>1. \A c \in Honest : locked[c].round <= valid[Proposer[r]].round
  BY DEF Lemma5Hyp
<1>2. \A c \in Honest, v \in Values, vr \in Rounds \cup {-1} :
        Proposal(Proposer[r], r, v, vr) \in sent =>
          locked[c].round <= vr
  <2> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW vr \in Rounds \cup {-1},
                      Proposal(Proposer[r], r, v, vr) \in sent
               PROVE  locked[c].round <= vr
    OBVIOUS
  <2>q. Proposer[r] \in Honest
    BY DEF Lemma5Hyp
  <2>1. valid[Proposer[r]].round <= vr
    BY DEF CaseA
  <2>ty. /\ locked[c].round \in Int
          /\ valid[Proposer[r]].round \in Int
          /\ vr \in Int
    BY <2>q DEFS LockState, Rounds, TypeOK
  <2> QED
    BY <1>1, <2>1, <2>ty, RegionIntLeTransitive
<1>q. Proposer[r] \in Honest
  BY DEF Lemma5Hyp
<1> QED
  BY <1>1, <1>2, <1>q DEF LocksDominateOrDated

\* ---- The stability statement the assembly consumes ------------------------
LEMMA BoxLocksDominateEntry ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ Lemma5Hyp(p, r) /\ CaseA(p, r)
              => LocksDominateOrDated(p, r)  )
BY Lemma5HypGivesLocksDominate, PTL

LEMMA BoxLocksDominateStep ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv
              /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
              /\ [Next]_vars /\ RoundOrigin(p, r)
              /\ LocksDominateOrDated(p, r) => LocksDominateOrDated(p, r)'  )
BY LocksDominateOrDatedStepL, PTL

THEOREM LocksDominateLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec
  PROVE  [](  Lemma5Hyp(p, r) /\ CaseA(p, r)
              => []LocksDominateOrDated(p, r)  )
<1>inv. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv
             /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
             /\ [Next]_vars  )
  BY EnteredAtLeNowInv, InvProof, PTL, RoundEntryHistoryInv, SentInvInv,
     TypeOKBothStates, ValidBelowRoundInv
  DEFS Inv, Spec
<1>en. [](TypeOK /\ Lemma5Hyp(p, r) /\ CaseA(p, r)
            => LocksDominateOrDated(p, r))
  BY BoxLocksDominateEntry
<1>ro. [](TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r))
  BY Lemma5HypRoundOriginBox
<1>st. [](RoundOrigin(p, r) => []RoundOrigin(p, r))
  BY RoundOriginStable
<1>sp. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv
            /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
            /\ [Next]_vars /\ RoundOrigin(p, r)
            /\ LocksDominateOrDated(p, r) => LocksDominateOrDated(p, r)'  )
  BY BoxLocksDominateStep
<1> QED
  BY <1>inv, <1>en, <1>ro, <1>st, <1>sp, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 11b. NilPrevoteBlocks, the refusal leaf as a REGION conjunct.      *)
(*                                                                         *)
(*  This is the inductive core of stage S2. A correct nil prevote at r,    *)
(*  dated inside the cascade window, can only come from a refusal, and a   *)
(*  refusal gives BlockingLockDuring(p, r). The other producer of a nil    *)
(*  prevote is OnTimeoutPropose, and it is dated ABOVE the window.         *)
(*  WRDurable(r) carries TimeoutPropose(r) > 2*Delta +                     *)
(*  TimeoutPrecommit(r-1). The entry of any correct process into r is also *)
(*  at or after the entry of p.                                            *)
(*                                                                         *)
(* The accept guard of both proposal actions reads                          *)
(*   Valid(v) /\ (locked[c].round <= vr \/ locked[c].value = v),            *)
(* so a refusal has THREE possible causes and not two. ValidProposalValue   *)
(* excludes ~Valid(v), and that is the whole reason item 10a exists. The    *)
(* other two are the negated lock bound, which LocksDominateOrDated turns   *)
(* into a dated lock.                                                      *)
(***************************************************************************)

\*  Locks start at -1 and every write sets the round to the writer's own
\*  round, which is a natural. This lemma is proved here, and not imported.
\*  The copy in ...Dominator is on a sibling branch, and its proof needs
\*  LockMonotone, IntLeTransitive and LockedBelowRound. The
\*  LockWriteIsFirstTime of item 11 instead closes it in three lines.
LEMMA LockWriteRound ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, locked'[c] # locked[c]
  PROVE  locked'[c].round = round[c]
<1>a. OnPrevoteQuorumValueFirstTime(c)
  BY LockWriteIsFirstTime
<1> QED
  BY <1>a DEFS OnPrevoteQuorumValueFirstTime, TypeOK

CascadeLockFloor == \A c \in Honest : locked[c].round >= -1

LEMMA CascadeLockFloorStepL ==
  ASSUME TypeOK, [Next]_vars, CascadeLockFloor
  PROVE  CascadeLockFloor'
<1> SUFFICES ASSUME NEW c \in Honest PROVE locked'[c].round >= -1
  BY DEF CascadeLockFloor
<1>1. CASE locked'[c] = locked[c]
  BY <1>1 DEF CascadeLockFloor
<1>2. CASE locked'[c] # locked[c]
  <2>1. locked'[c].round = round[c]
    BY <1>2, LockWriteRound
  <2> QED
    BY <2>1, HonestSubValidators DEFS Rounds, TypeOK
<1> QED
  BY <1>1, <1>2

THEOREM CascadeLockFloorInv == ASSUME Spec PROVE []CascadeLockFloor
<1>1. CascadeLockFloor
  BY DEFS CascadeLockFloor, Init, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEFS Inv, Spec
<1>3. [](CascadeLockFloor => CascadeLockFloor')
  BY <1>2, CascadeLockFloorStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* Only ONE message is activated per step, and the action fixes its type. A step
\* that activates a prevote therefore leaves every proposal slot as it was.
LEMMA PrevoteStepKeepsProposals ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest,
         OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c),
         NEW mm \in Message, mm.type = "Proposal", mm \in sent'
  PROVE  mm \in sent
\* The witness is UNBOUNDED. Typing the prevote's value at ValuesOrNil would
\* need prop.value \in Values, hence RcvdSubsetSent, and none of that is
\* required: only the type field distinguishes the two constructors.
<1>1. \E m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
              /\ m0.type = "Prevote"
  BY DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose,
    Prevote
<1>2. PICK m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
                /\ m0.type = "Prevote"
  BY <1>1
<1>3. mm # m0
  BY <1>2
<1>4. sentTime'[mm] = sentTime[mm]
  BY <1>2, <1>3 DEF TypeOK
<1> QED
  BY <1>4 DEF sent

\* Arithmetic in a minimal context. An entry at or after the origin, whose
\* propose deadline clears the window offset by a whole Delta, lands above the
\* window.
LEMMA GtFromEntryMargin ==
  ASSUME NEW e \in Int, NEW e0 \in Int, NEW tp \in Int, NEW d \in Int,
         NEW k \in Int, e >= e0, tp > 2 * d + k
  PROVE  e + tp > e0 + 2 * d + k
BY SMT

NilPrevoteBlocks(p, r) ==
  \A c \in Honest, v \in Values, vr \in Rounds \cup {-1} :
    ( /\ Proposal(Proposer[r], r, v, vr) \in sent
      /\ Prevote(c, r, nil) \in sent
      /\ sentTime[Prevote(c, r, nil)] <= CascadeDeadline(p, r) )
    => BlockingLockDuring(p, r)

\*  Every witness of BlockingLockDuring is a message in the pool, or a frozen
\*  timestamp. The entry slot is write once, so the predicate is monotone.
LEMMA BlockingLockMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds,
         enteredAt'[p][r] = enteredAt[p][r], BlockingLockDuring(p, r)
  PROVE  BlockingLockDuring(p, r)'
<1>1. PICK v \in Values, w \in Values, vr \in Rounds \cup {-1}, c \in Honest, lr \in Rounds :
        /\ Proposal(Proposer[r], r, v, vr) \in sent
        /\ vr < lr
        /\ lr < r
        /\ w # v
        /\ Precommit(c, lr, w) \in sent
        /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]
  BY DEFS BlockingLockDuring, VotedPrecommit
<1>mc. Precommit(c, lr, w) \in Message
  BY <1>1 DEF sent
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>2. /\ Proposal(Proposer[r], r, v, vr) \in sent'
      /\ Precommit(c, lr, w) \in sent'
  BY <1>1, SentMonotoneStep
<1>3. sentTime'[Precommit(c, lr, w)] = sentTime[Precommit(c, lr, w)]
  BY <1>1, <1>fz, <1>mc DEF sent
<1> QED
  BY <1>1, <1>2, <1>3 DEFS BlockingLockDuring, VotedPrecommit

\*  The refusal leaf of section 1 of the plan, as a state lemma. The negated
\*  accept guard IS the pair vr < lr and w # v, and LocksDominateOrDated
\*  supplies the date. The bound lr < r comes from LockedLeValid composed with
\*  ValidStrictAtPropose. A process in step "propose" has its lock STRICTLY
\*  below its own round. No separate LockedBelowRound is needed.
LEMMA RefusalIsBlocking ==
  ASSUME TypeOK, LockedLeValid, ValidStrictAtPropose, LockBackedByPrecommit,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         NEW v \in Values, NEW vr \in Rounds \cup {-1},
         Proposal(Proposer[r], r, v, vr) \in sent,
         round[c] = r, step[c] = "propose",
         ~(locked[c].round <= vr), locked[c].value # v,
         LocksDominateOrDated(p, r)
  PROVE  BlockingLockDuring(p, r)
<1>d. LockDatedAfterEntry(p, r, c)
  BY DEF LocksDominateOrDated
<1>1. /\ locked[c].round >= 0
      /\ Precommit(c, locked[c].round, locked[c].value) \in sent
      /\ sentTime[Precommit(c, locked[c].round, locked[c].value)]
           >= enteredAt[p][r]
  BY <1>d DEF LockDatedAfterEntry
<1>lt. locked[c].round < r
  <2>1. locked[c].round <= valid[c].round
    BY DEF LockedLeValid
  <2>2. valid[c].round < round[c]
    BY DEF ValidStrictAtPropose
  <2>ty. /\ locked[c].round \in Int /\ valid[c].round \in Int
         /\ round[c] \in Nat
    BY HonestSubValidators DEFS LockState, Rounds, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>ty
<1>n. locked[c].round \in Rounds
  BY <1>1, HonestSubValidators DEFS LockState, Rounds, TypeOK
\* NOT off the message record. PrecommitMsg types valueID at ValuesOrNil,
\* because a correct process may precommit nil. LockBackedByPrecommit is what
\* rules that out for a lock.
<1>w. locked[c].value \in Values
  BY <1>1 DEF LockBackedByPrecommit
<1>ty. /\ locked[c].round \in Int /\ vr \in Int /\ vr < locked[c].round
  BY HonestSubValidators DEFS LockState, Rounds, TypeOK
<1> QED
  BY <1>1, <1>lt, <1>n, <1>ty, <1>w DEFS BlockingLockDuring, VotedPrecommit

\* A fresh correct nil prevote at r inside the window comes from a refusal.
LEMMA FreshNilPrevoteBlocks ==
  ASSUME TypeOK, RcvdSubsetSent, EnteredCurrentRound, HonestProposalUnique,
         ValidProposalValue, LockedLeValid, ValidStrictAtPropose,
         LockBackedByPrecommit, ProposeTimerValue, CascadeLockFloor,
         [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         NEW v \in Values, NEW vr \in Rounds \cup {-1},
         RoundOrigin(p, r), WRDurable(r), LocksDominateOrDated(p, r),
         Proposal(Proposer[r], r, v, vr) \in sent,
         Prevote(c, r, nil) \in sent', Prevote(c, r, nil) \notin sent,
         sentTime'[Prevote(c, r, nil)] <= CascadeDeadline(p, r)
  PROVE  BlockingLockDuring(p, r)
<1>m. Prevote(c, r, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>a. /\ r = round[c]
      /\ sentTime'[Prevote(c, r, nil)] = now
      /\ \/ OnTimeoutPropose(c)
         \/ OnProposalNoPOL(c)
         \/ OnProposalWithPOL(c)
  BY <1>m, FreshPrevoteAction DEF Prevote
<1>ty. /\ r \in Nat /\ r > 0 /\ enteredAt[p][r] \in Nat
       /\ enteredAt[c][r] \in Nat /\ Delta \in Nat
       /\ TimeoutPrecommit(r - 1) \in Nat /\ TimeoutPropose(r) \in Nat
       /\ now \in Nat
  <2>1. r > 0 /\ enteredAt[p][r] # OFF
    BY DEF RoundOrigin
  <2>2. enteredAt[c][r] # OFF
    BY <1>a DEF EnteredCurrentRound
  <2>3. /\ r \in Nat /\ TimeoutPrecommit(r - 1) \in Nat
        /\ TimeoutPropose(r) \in Nat
    BY <2>1, RoundTypes
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType DEFS OFF, TypeOK
\*  The propose deadline of c is above the window. c entered r at or after p,
\*  and the margin of WRDurable clears the window by a whole Delta.
<1>late. enteredAt[c][r] + TimeoutPropose(r) > CascadeDeadline(p, r)
  <2>1. enteredAt[c][r] >= enteredAt[p][r]
    BY <1>ty DEFS EntriesAtOrAfter, OFF, RoundOrigin
  <2>2. TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
    BY DEF WRDurable
  <2> QED
    BY <1>ty, <2>1, <2>2, GtFromEntryMargin DEF CascadeDeadline
\* Both proposal actions read the SAME round-r proposal, by uniqueness, and
\* their nil branch is the negated accept guard.
<1>ref. ASSUME NEW prop \in RProposalsFromProposerAt(c, round[c]),
               step[c] = "propose",
               ~(Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                         \/ locked[c].value = prop.value))
        PROVE  BlockingLockDuring(p, r)
  <2>1. /\ prop \in sent
        /\ prop.type = "Proposal"
        /\ prop.round = r
        /\ prop.sender = Proposer[r]
\* NOT `DEFS ... rcvd`. rcvd is a VARIABLE, and naming a variable in a DEFS
\* list crashes tlapm inside Proof.Gen.set_defn instead of reporting an error.
    BY <1>a, <1>ref
    DEFS RcvdSubsetSent, RProposals, RProposalsFromProposerAt, sent
  <2>2. /\ prop.value \in Values
        /\ prop.validRound \in Rounds \cup {-1}
        /\ prop = Proposal(prop.sender, prop.round, prop.value, prop.validRound)
    BY <2>1, ProposalRecordRebuild DEF sent
  <2>3. Proposal(Proposer[r], r, prop.value, prop.validRound) \in sent
    BY <2>1, <2>2
  <2>q. Proposer[r] \in Honest
    BY DEF WRDurable
  <2>4. prop.value = v /\ prop.validRound = vr
    BY <2>2, <2>3, <2>q DEF HonestProposalUnique
  <2>5. Valid(v)
    BY <2>3, <2>4, <2>q DEF ValidProposalValue
  <2>6. ~(locked[c].round <= vr) /\ locked[c].value # v
    BY <1>ref, <2>4, <2>5
  <2> QED
    BY <1>a, <1>ref, <2>6, RefusalIsBlocking
<1>1. CASE OnTimeoutPropose(c)
  <2>1. timer[c]["propose"] # OFF /\ now >= timer[c]["propose"]
    BY <1>1 DEF OnTimeoutPropose
  <2>2. timer[c]["propose"] = enteredAt[c][r] + TimeoutPropose(r)
    BY <1>a, <2>1 DEF ProposeTimerValue
  <2>ty. CascadeDeadline(p, r) \in Nat
    BY <1>ty DEF CascadeDeadline
  <2> QED
    BY <1>a, <1>late, <1>ty, <2>1, <2>2, <2>ty
<1>2. CASE OnProposalNoPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          /\ prop.validRound = -1
          /\ Broadcast(c, Prevote(c, round[c],
               IF Valid(prop.value) /\ (locked[c].round = -1
                                          \/ locked[c].value = prop.value)
               THEN prop.value ELSE nil))
    BY <1>2 DEF OnProposalNoPOL
  <2>st. step[c] = "propose"
    BY <1>2 DEF OnProposalNoPOL
  <2>2. ~(Valid(prop.value) /\ (locked[c].round = -1
                                  \/ locked[c].value = prop.value))
    <3>1. Prevote(c, r, nil)
            = Prevote(c, round[c],
                IF Valid(prop.value) /\ (locked[c].round = -1
                                           \/ locked[c].value = prop.value)
                THEN prop.value ELSE nil)
      BY <1>m, <2>1 DEFS Broadcast, sent, TypeOK
    <3>2. prop.value \in Values
      BY <2>1, RProposalValueType DEFS Rounds, TypeOK
    <3> QED
      BY <3>1, <3>2, NilNotInValues DEF Prevote
\* The floor bridges the two guard spellings: at validRound -1 the test
\* locked[c].round <= -1 IS locked[c].round = -1.
  <2>3. (locked[c].round <= prop.validRound) <=> (locked[c].round = -1)
    <3>1. locked[c].round >= -1
      BY DEF CascadeLockFloor
    <3>ty. locked[c].round \in Int
      BY HonestSubValidators DEFS LockState, Rounds, TypeOK
    <3> QED
      BY <2>1, <3>1, <3>ty
  <2> QED
    BY <1>ref, <2>1, <2>2, <2>3, <2>st
<1>3. CASE OnProposalWithPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          Broadcast(c, Prevote(c, round[c],
            IF Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                       \/ locked[c].value = prop.value)
            THEN prop.value ELSE nil))
    BY <1>3 DEF OnProposalWithPOL
  <2>st. step[c] = "propose"
    BY <1>3 DEF OnProposalWithPOL
  <2>2. ~(Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                  \/ locked[c].value = prop.value))
    <3>1. Prevote(c, r, nil)
            = Prevote(c, round[c],
                IF Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                           \/ locked[c].value = prop.value)
                THEN prop.value ELSE nil)
      BY <1>m, <2>1 DEFS Broadcast, sent, TypeOK
    <3>2. prop.value \in Values
      BY <2>1, RProposalValueType DEFS Rounds, TypeOK
    <3> QED
      BY <3>1, <3>2, NilNotInValues DEF Prevote
  <2> QED
    BY <1>ref, <2>1, <2>2, <2>st
<1> QED
  BY <1>1, <1>2, <1>3, <1>a

LEMMA NilPrevoteBlocksStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory,
         EnteredCurrentRound, HonestProposalUnique, ValidProposalValue,
         LockedLeValid, ValidStrictAtPropose, ProposeTimerValue,
         CascadeLockFloor, PrevoteNeedsProposalOrTimeout,
         HonestProposalUnique', LockBackedByPrecommit, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds,
         RoundOrigin(p, r), WRDurable(r), LocksDominateOrDated(p, r),
         NilPrevoteBlocks(p, r)
  PROVE  NilPrevoteBlocks(p, r)'
<1>e. enteredAt'[p][r] = enteredAt[p][r]
  BY EnteredAtFrozenStep DEF RoundOrigin
<1>c. CascadeDeadline(p, r)' = CascadeDeadline(p, r)
  BY <1>e DEF CascadeDeadline
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW vr \in Rounds \cup {-1},
                    Proposal(Proposer[r], r, v, vr) \in sent',
                    Prevote(c, r, nil) \in sent',
                    sentTime'[Prevote(c, r, nil)] <= CascadeDeadline(p, r)
             PROVE  BlockingLockDuring(p, r)'
  BY <1>c DEF NilPrevoteBlocks
<1>mv. Prevote(c, r, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>mp. Proposal(Proposer[r], r, v, vr) \in Message
  BY DEF sent
<1>ty. /\ r \in Nat /\ r > 0 /\ enteredAt[p][r] \in Nat
       /\ Delta \in Nat /\ TimeoutPrecommit(r - 1) \in Nat
       /\ TimeoutPropose(r) \in Nat /\ CascadeDeadline(p, r) \in Nat
  <2>1. r > 0 /\ enteredAt[p][r] # OFF
    BY DEF RoundOrigin
  <2>2. /\ r \in Nat /\ TimeoutPrecommit(r - 1) \in Nat
        /\ TimeoutPropose(r) \in Nat
    BY <2>1, RoundTypes
  <2>3. enteredAt[p][r] \in Nat
    BY <2>1 DEFS OFF, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, CascadeDeadlineType, DeltaType
\* The prevote is fresh: the refusal leaf closes it. A prevote step activates
\* one prevote, so the proposal has to pre-exist.
<1>1. CASE Prevote(c, r, nil) \notin sent
  <2>a. \/ OnTimeoutPropose(c)
        \/ OnProposalNoPOL(c)
        \/ OnProposalWithPOL(c)
    BY <1>1, <1>mv, FreshPrevoteAction DEF Prevote
  <2>p. Proposal(Proposer[r], r, v, vr) \in sent
    BY <1>mp, <2>a, PrevoteStepKeepsProposals DEF Proposal
  <2>1. BlockingLockDuring(p, r)
    BY <1>1, <2>p, FreshNilPrevoteBlocks
  <2> QED
    BY <1>e, <2>1, BlockingLockMove
\*  The prevote is old. Either the proposal is old too, and the hypothesis
\*  applies, or the proposal is fresh. In the second case the prevote had no
\*  proposal to read, so the propose timeout dated it above the window.
<1>2. CASE Prevote(c, r, nil) \in sent
  <2>d. sentTime[Prevote(c, r, nil)] <= CascadeDeadline(p, r)
    BY <1>2, <1>fz, <1>mv DEF sent
  <2>1. CASE Proposal(Proposer[r], r, v, vr) \in sent
    BY <1>2, <1>e, <2>1, <2>d, BlockingLockMove DEF NilPrevoteBlocks
  <2>2. CASE Proposal(Proposer[r], r, v, vr) \notin sent
\* Uniqueness is read at the PRIMED state. The round-r proposal is FRESH here,
\* so the unprimed pool holds nothing to compare it with, and only sent' holds
\* both proposals at once.
    <3>sub. sent \subseteq sent'
      BY SentMonotoneStep
    <3>no. \A v2 \in Values, vr2 \in Rounds \cup {-1} :
             Proposal(Proposer[r], r, v2, vr2) \notin sent
      <4> SUFFICES ASSUME NEW v2 \in Values, NEW vr2 \in Rounds \cup {-1},
                          Proposal(Proposer[r], r, v2, vr2) \in sent
                   PROVE  FALSE
        OBVIOUS
      <4>q. Proposer[r] \in Honest
        BY DEF WRDurable
      <4>2. Proposal(Proposer[r], r, v2, vr2) \in sent'
        BY <3>sub
      <4>1. v2 = v /\ vr2 = vr
        BY <4>2, <4>q DEF HonestProposalUnique
      <4> QED
        BY <2>2, <4>1
    <3>1. ~ \E mm \in sent : /\ mm.type = "Proposal"
                             /\ mm.round = r
                             /\ mm.sender = Proposer[r]
      BY <3>no, HonestSubValidators, NoProposalRebuild DEF WRDurable
    <3>2. /\ enteredAt[c][r] # OFF
          /\ sentTime[Prevote(c, r, nil)]
               >= enteredAt[c][r] + TimeoutPropose(r)
      BY <1>2, <3>1 DEFS PrevoteNeedsProposalOrTimeout, ValuesOrNil
    <3>3. enteredAt[c][r] >= enteredAt[p][r] /\ enteredAt[c][r] \in Nat
      BY <1>ty, <3>2 DEFS EntriesAtOrAfter, OFF, RoundOrigin, TypeOK
    <3>4. TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
      BY DEF WRDurable
    <3>5. enteredAt[c][r] + TimeoutPropose(r) > CascadeDeadline(p, r)
      BY <1>ty, <3>3, <3>4, GtFromEntryMargin DEF CascadeDeadline
    <3>t. sentTime[Prevote(c, r, nil)] \in Int
      BY <1>2, <1>mv DEFS OFF, sent, TypeOK
    <3> QED
      BY <1>ty, <2>d, <3>2, <3>3, <3>5, <3>t
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 11c. Carrying a refusal forward in time.                           *)
(*                                                                         *)
(*  The region of item 11b cannot be entered vacuously by inspection.      *)
(*  FirstToEnter(p, r) reads \A c \in Honest : enteredAt[c][r] = OFF \/    *)
(*  enteredAt[c][r] >= now, and EnteredAtLeNow pins any entered process to *)
(*  enteredAt[c][r] = now, so another correct process may enter r at the   *)
(*  SAME clock instant as p. The clock advances only on Tick. That process *)
(*  can therefore enter r, read the proposal and refuse, all at one clock  *)
(*  value. Its nil prevote is then already in the pool when the hypothesis *)
(*  holds.                                                                 *)
(*                                                                         *)
(*  The state is still unreachable, by LOCK MONOTONICITY. At the refusal   *)
(*  instant the lock round was above vr, and a lock round never decreases. *)
(*  It is therefore still above vr at the hypothesis state. There clause   *)
(*  (3) of Lemma5Hyp, with CaseA, forces it at or below vr.                *)
(*                                                                         *)
(*   That argument LOOKS BACK IN TIME, and an invariant cannot. So carry   *)
(*   the past forward. The naive form is "a nil prevote below a dated      *)
(*   proposal means a high lock", and it is FALSE. OnTimeoutPropose sends  *)
(*   a nil prevote for no reason about a lock. The proposal can also sit   *)
(*   in `sent` and never reach that process. The timeout is therefore an   *)
(*   explicit ESCAPE disjunct, and the consumer excludes it by arithmetic. *)
(*   At the hypothesis state every correct entry into r is at `now`, so no *)
(*   propose deadline has passed yet.                                      *)
(***************************************************************************)

\* Proved here and not moved. The copy in ...Selection is on a sibling branch,
\* and only CrossRoundMonotoneStep from ...Base is needed.
CascadeLockBelowRound == \A c \in Honest : locked[c].round <= round[c]

LEMMA CascadeLockBelowRoundStepL ==
  ASSUME TypeOK, [Next]_vars, CascadeLockBelowRound
  PROVE  CascadeLockBelowRound'
<1> SUFFICES ASSUME NEW c \in Honest PROVE locked'[c].round <= round'[c]
  BY DEF CascadeLockBelowRound
<1>v. c \in Validators
  BY HonestSubValidators
<1>r. round'[c] \in Nat /\ round[c] <= round'[c] /\ round[c] \in Nat
  BY <1>v, CrossRoundMonotoneStep DEFS Rounds, TypeOK
<1>i. locked[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>1. CASE locked'[c] = locked[c]
  <2>1. locked[c].round <= round[c]
    BY DEF CascadeLockBelowRound
  <2> QED
    BY <1>1, <1>i, <1>r, <2>1
<1>2. CASE locked'[c] # locked[c]
  <2>1. locked'[c].round = round[c]
    BY <1>2, LockWriteRound
  <2> QED
    BY <1>r, <2>1
<1> QED
  BY <1>1, <1>2

THEOREM CascadeLockBelowRoundInv ==
  ASSUME Spec PROVE []CascadeLockBelowRound
<1>1. CascadeLockBelowRound
  BY DEFS CascadeLockBelowRound, Init, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEFS Inv, Spec
<1>3. [](CascadeLockBelowRound => CascadeLockBelowRound')
  BY <1>2, CascadeLockBelowRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* A lock round never decreases. Every write sets it to the writer's own round,
\* which is monotone, and CascadeLockBelowRound caps the old value by the old
\* round.
LEMMA LockRoundMonotoneStep ==
  ASSUME TypeOK, CascadeLockBelowRound, [Next]_vars, NEW c \in Honest
  PROVE  locked[c].round <= locked'[c].round
<1>v. c \in Validators
  BY HonestSubValidators
<1>i. locked[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>r. round[c] \in Nat /\ round'[c] \in Nat /\ round[c] <= round'[c]
  BY <1>v, CrossRoundMonotoneStep DEFS Rounds, TypeOK
<1>1. CASE locked'[c] = locked[c]
  BY <1>1, <1>i
<1>2. CASE locked'[c] # locked[c]
  <2>1. locked'[c].round = round[c]
    BY <1>2, LockWriteRound
  <2>2. locked[c].round <= round[c]
    BY DEF CascadeLockBelowRound
  <2> QED
    BY <1>i, <1>r, <2>1, <2>2
<1> QED
  BY <1>1, <1>2

\*  Proposer[rr] \in Honest is an antecedent conjunct. A faulty proposer can
\*  author two different round-rr proposals. The refusal that produced the nil
\*  prevote need not then concern the proposal that the clause names.
NilPrevoteRefusedOrTimedOut ==
  \A c \in Honest, rr \in Rounds, v \in Values, vr \in Rounds \cup {-1} :
    ( /\ Proposer[rr] \in Honest
      /\ Proposal(Proposer[rr], rr, v, vr) \in sent
      /\ Prevote(c, rr, nil) \in sent )
    => \/ locked[c].round > vr
       \/ sentTime[Prevote(c, rr, nil)]
            >= enteredAt[c][rr] + TimeoutPropose(rr)

\* The refusal branches. Both proposal actions leave `locked` UNCHANGED, so the
\* lock that refused is the lock of the post-state, and the negated guard reports
\* its round directly.
LEMMA FreshNilPrevoteRefusedOrTimedOut ==
  ASSUME TypeOK, RcvdSubsetSent, HonestProposalUnique, ValidProposalValue,
         CascadeLockFloor, ProposeTimerValue, [Next]_vars,
         NEW c \in Honest, NEW rr \in Rounds, NEW v \in Values, NEW vr \in Rounds \cup {-1},
         Proposer[rr] \in Honest,
         Proposal(Proposer[rr], rr, v, vr) \in sent,
         Prevote(c, rr, nil) \in sent', Prevote(c, rr, nil) \notin sent
  PROVE  \/ locked'[c].round > vr
         \/ sentTime'[Prevote(c, rr, nil)]
              >= enteredAt'[c][rr] + TimeoutPropose(rr)
<1>mv. Prevote(c, rr, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>a. /\ rr = round[c]
      /\ sentTime'[Prevote(c, rr, nil)] = now
      /\ \/ OnTimeoutPropose(c)
         \/ OnProposalNoPOL(c)
         \/ OnProposalWithPOL(c)
  BY <1>mv, FreshPrevoteAction DEF Prevote
<1>e. enteredAt'[c][rr] = enteredAt[c][rr]
  BY <1>a
  DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose
<1>lk. locked'[c] = locked[c]
  BY <1>a
  DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose
<1>ref. ASSUME NEW prop \in RProposalsFromProposerAt(c, round[c]),
               ~(Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                         \/ locked[c].value = prop.value))
        PROVE  locked'[c].round > vr
  <2>1. /\ prop \in sent
        /\ prop.type = "Proposal"
        /\ prop.round = rr
        /\ prop.sender = Proposer[rr]
    BY <1>a, <1>ref
    DEFS RcvdSubsetSent, RProposals, RProposalsFromProposerAt, sent
  <2>2. /\ prop.value \in Values
        /\ prop.validRound \in Rounds \cup {-1}
        /\ prop = Proposal(prop.sender, prop.round, prop.value, prop.validRound)
    BY <2>1, ProposalRecordRebuild DEF sent
  <2>3. Proposal(Proposer[rr], rr, prop.value, prop.validRound) \in sent
    BY <2>1, <2>2
  <2>4. prop.value = v /\ prop.validRound = vr
    BY <2>2, <2>3 DEF HonestProposalUnique
  <2>5. Valid(v)
    BY <2>3, <2>4 DEF ValidProposalValue
  <2>ty. locked[c].round \in Int /\ vr \in Int
    BY HonestSubValidators DEFS LockState, Rounds, TypeOK
  <2> QED
    BY <1>lk, <1>ref, <2>2, <2>4, <2>5, <2>ty
\* The timeout branch. The escape disjunct is exactly the guard of the action,
\* read through ProposeTimerValue.
<1>1. CASE OnTimeoutPropose(c)
  <2>1. timer[c]["propose"] # OFF /\ now >= timer[c]["propose"]
    BY <1>1 DEF OnTimeoutPropose
  <2>2. timer[c]["propose"] = enteredAt[c][rr] + TimeoutPropose(rr)
    BY <1>a, <2>1 DEF ProposeTimerValue
  <2> QED
    BY <1>a, <1>e, <2>1, <2>2
<1>2. CASE OnProposalNoPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          /\ prop.validRound = -1
          /\ Broadcast(c, Prevote(c, round[c],
               IF Valid(prop.value) /\ (locked[c].round = -1
                                          \/ locked[c].value = prop.value)
               THEN prop.value ELSE nil))
    BY <1>2 DEF OnProposalNoPOL
  <2>2. ~(Valid(prop.value) /\ (locked[c].round = -1
                                  \/ locked[c].value = prop.value))
    <3>1. Prevote(c, rr, nil)
            = Prevote(c, round[c],
                IF Valid(prop.value) /\ (locked[c].round = -1
                                           \/ locked[c].value = prop.value)
                THEN prop.value ELSE nil)
      BY <1>mv, <2>1 DEFS Broadcast, sent, TypeOK
    <3>2. prop.value \in Values
      BY <2>1, RProposalValueType DEFS Rounds, TypeOK
    <3> QED
      BY <3>1, <3>2, NilNotInValues DEF Prevote
\* The floor bridges the two guard spellings: at validRound -1 the test
\* locked[c].round <= -1 IS locked[c].round = -1.
  <2>3. (locked[c].round <= prop.validRound) <=> (locked[c].round = -1)
    <3>1. locked[c].round >= -1
      BY DEF CascadeLockFloor
    <3>ty. locked[c].round \in Int
      BY HonestSubValidators DEFS LockState, Rounds, TypeOK
    <3> QED
      BY <2>1, <3>1, <3>ty
  <2> QED
    BY <1>ref, <2>1, <2>2, <2>3
<1>3. CASE OnProposalWithPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          Broadcast(c, Prevote(c, round[c],
            IF Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                       \/ locked[c].value = prop.value)
            THEN prop.value ELSE nil))
    BY <1>3 DEF OnProposalWithPOL
  <2>2. ~(Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                  \/ locked[c].value = prop.value))
    <3>1. Prevote(c, rr, nil)
            = Prevote(c, round[c],
                IF Valid(prop.value) /\ (locked[c].round <= prop.validRound
                                           \/ locked[c].value = prop.value)
                THEN prop.value ELSE nil)
      BY <1>mv, <2>1 DEFS Broadcast, sent, TypeOK
    <3>2. prop.value \in Values
      BY <2>1, RProposalValueType DEFS Rounds, TypeOK
    <3> QED
      BY <3>1, <3>2, NilNotInValues DEF Prevote
  <2> QED
    BY <1>ref, <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3, <1>a

LEMMA NilPrevoteRefusedOrTimedOutStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, RoundEntryHistory,
         HonestProposalUnique, HonestProposalUnique', ValidProposalValue,
         CascadeLockFloor, CascadeLockBelowRound, ProposeTimerValue,
         PrevoteNeedsProposalOrTimeout, [Next]_vars,
         NilPrevoteRefusedOrTimedOut
  PROVE  NilPrevoteRefusedOrTimedOut'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW c \in Honest, NEW rr \in Rounds, NEW v \in Values,
                    NEW vr \in Rounds \cup {-1}, Proposer[rr] \in Honest,
                    Proposal(Proposer[rr], rr, v, vr) \in sent',
                    Prevote(c, rr, nil) \in sent'
             PROVE  \/ locked'[c].round > vr
                    \/ sentTime'[Prevote(c, rr, nil)]
                         >= enteredAt'[c][rr] + TimeoutPropose(rr)
  BY DEF NilPrevoteRefusedOrTimedOut
<1>mv. Prevote(c, rr, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>mp. Proposal(Proposer[rr], rr, v, vr) \in Message
  BY DEF sent
<1>v. c \in Validators
  BY HonestSubValidators
<1>i. locked[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>ip. locked'[c].round \in Int
  BY <1>v DEFS LockState, Rounds, TypeOK
<1>iv. vr \in Int
  BY DEF Rounds
<1>tp. TimeoutPropose(rr) \in Nat
  BY T0ProposeType, TDeltaType DEFS Rounds, TimeoutPropose
\*  The proposal has to pre-exist. If it is fresh, then no round-rr proposal
\*  was in the pool before. PrevoteNeedsProposalOrTimeout therefore gave the
\*  timeout branch for the prevote that already existed. A FRESH prevote also
\*  cannot share the step with a fresh proposal.
<1>p. CASE Proposal(Proposer[rr], rr, v, vr) \notin sent
  <2>no. \A v2 \in Values, vr2 \in Rounds \cup {-1} :
           Proposal(Proposer[rr], rr, v2, vr2) \notin sent
    <3> SUFFICES ASSUME NEW v2 \in Values, NEW vr2 \in Rounds \cup {-1},
                        Proposal(Proposer[rr], rr, v2, vr2) \in sent
                 PROVE  FALSE
      OBVIOUS
    <3>1. Proposal(Proposer[rr], rr, v2, vr2) \in sent'
      BY <1>sub
    <3>2. v2 = v /\ vr2 = vr
      BY <3>1 DEF HonestProposalUnique
    <3> QED
      BY <1>p, <3>2
  <2>1. ~ \E mm \in sent : /\ mm.type = "Proposal"
                           /\ mm.round = rr
                           /\ mm.sender = Proposer[rr]
    BY <2>no, HonestSubValidators, NoProposalRebuild
\* A prevote step activates a prevote, so the proposal cannot be fresh in the
\* same step, so the prevote is old.
  <2>old. Prevote(c, rr, nil) \in sent
    <3> SUFFICES ASSUME Prevote(c, rr, nil) \notin sent PROVE FALSE
      OBVIOUS
    <3>a. \/ OnTimeoutPropose(c)
          \/ OnProposalNoPOL(c)
          \/ OnProposalWithPOL(c)
      BY <1>mv, FreshPrevoteAction DEF Prevote
    <3>1. Proposal(Proposer[rr], rr, v, vr) \in sent
      BY <1>mp, <3>a, PrevoteStepKeepsProposals DEF Proposal
    <3> QED
      BY <1>p, <3>1
  <2>2. /\ enteredAt[c][rr] # OFF
        /\ sentTime[Prevote(c, rr, nil)]
             >= enteredAt[c][rr] + TimeoutPropose(rr)
    BY <2>1, <2>old DEFS PrevoteNeedsProposalOrTimeout, ValuesOrNil
  <2>3. /\ sentTime'[Prevote(c, rr, nil)] = sentTime[Prevote(c, rr, nil)]
        /\ enteredAt'[c][rr] = enteredAt[c][rr]
    BY <1>fz, <1>mv, <2>2, <2>old, EnteredAtFrozenStep DEF sent
  <2> QED
    BY <2>2, <2>3
<1>q. CASE Proposal(Proposer[rr], rr, v, vr) \in sent
  <2>1. CASE Prevote(c, rr, nil) \notin sent
    BY <1>q, <2>1, FreshNilPrevoteRefusedOrTimedOut
  <2>2. CASE Prevote(c, rr, nil) \in sent
    <3>1. \/ locked[c].round > vr
          \/ sentTime[Prevote(c, rr, nil)]
               >= enteredAt[c][rr] + TimeoutPropose(rr)
      BY <1>q, <2>2 DEF NilPrevoteRefusedOrTimedOut
    <3>2. CASE locked[c].round > vr
      <4>1. locked[c].round <= locked'[c].round
        BY LockRoundMonotoneStep
      <4> QED
        BY <1>i, <1>ip, <1>iv, <3>2, <4>1, RegionIntLtLeTransitive
    <3>3. CASE sentTime[Prevote(c, rr, nil)]
                 >= enteredAt[c][rr] + TimeoutPropose(rr)
      <4>e. enteredAt[c][rr] # OFF
        BY <2>2 DEFS PrevoteNeedsProposalOrTimeout, ValuesOrNil
      <4>1. /\ sentTime'[Prevote(c, rr, nil)] = sentTime[Prevote(c, rr, nil)]
            /\ enteredAt'[c][rr] = enteredAt[c][rr]
        BY <1>fz, <1>mv, <2>2, <4>e, EnteredAtFrozenStep DEF sent
      <4> QED
        BY <3>3, <4>1
    <3> QED
      BY <3>1, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>p, <1>q

THEOREM NilPrevoteRefusedOrTimedOutInv ==
  ASSUME Spec PROVE []NilPrevoteRefusedOrTimedOut
<1>1. NilPrevoteRefusedOrTimedOut
  BY DEFS Init, NilPrevoteRefusedOrTimedOut, OFF, sent, Spec
<1>2. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
           /\ HonestProposalUnique /\ HonestProposalUnique'
           /\ ValidProposalValue /\ CascadeLockFloor
           /\ CascadeLockBelowRound /\ ProposeTimerValue
           /\ PrevoteNeedsProposalOrTimeout /\ [Next]_vars  )
  BY CascadeLockBelowRoundInv, CascadeLockFloorInv, HonestProposalUniqueInv,
     InvProof, PrevoteNeedsProposalOrTimeoutInv, ProposeTimerValueInv, PTL,
     RoundEntryHistoryInv, SentInvInv, TypeOKBothStates, ValidProposalValueInv
  DEFS Inv, Spec
<1>3. [](NilPrevoteRefusedOrTimedOut => NilPrevoteRefusedOrTimedOut')
  BY <1>2, NilPrevoteRefusedOrTimedOutStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*   ---- The entry, at last
\*   --------------------------------------------------- At the hypothesis
\*   state the region is entered VACUOUSLY, and both disjuncts of item 11c are
\*   what make it so. Arithmetic excludes the timeout escape. Every correct
\*   entry into r is at `now`, so no propose deadline has passed. Clause (3)
\*   of Lemma5Hyp, composed with CaseA, excludes the lock disjunct.
LEMMA Lemma5HypGivesNilPrevoteBlocks ==
  ASSUME TypeOK, SentTimeLeNow, NilPrevoteRefusedOrTimedOut,
         PrevoteNeedsProposalOrTimeout,
         NEW p \in Honest, NEW r \in Rounds, Lemma5Hyp(p, r), CaseA(p, r)
  PROVE  NilPrevoteBlocks(p, r)
<1> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW vr \in Rounds \cup {-1},
                    Proposal(Proposer[r], r, v, vr) \in sent,
                    Prevote(c, r, nil) \in sent
             PROVE  FALSE
  BY DEF NilPrevoteBlocks
<1>q. Proposer[r] \in Honest
  BY DEF Lemma5Hyp
<1>mv. Prevote(c, r, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>ty. /\ now \in Nat /\ locked[c].round \in Int /\ vr \in Int
       /\ valid[Proposer[r]].round \in Int
       /\ sentTime[Prevote(c, r, nil)] \in Int
       /\ TimeoutPropose(r) \in Nat /\ TimeoutPropose(r) > 0
  <2>1. TimeoutPropose(r) \in Nat /\ TimeoutPropose(r) > 0
    BY T0ProposeType, TDeltaType DEFS Rounds, TimeoutPropose
  <2> QED
    BY <1>mv, <1>q, <2>1, HonestSubValidators
    DEFS LockState, OFF, Rounds, sent, TypeOK
<1>1. \/ locked[c].round > vr
      \/ sentTime[Prevote(c, r, nil)] >= enteredAt[c][r] + TimeoutPropose(r)
  BY <1>q DEF NilPrevoteRefusedOrTimedOut
\* The lock disjunct: clause (3) with CaseA bounds the lock at or below vr.
<1>2. locked[c].round <= vr
  <2>1. locked[c].round <= valid[Proposer[r]].round
    BY DEF Lemma5Hyp
  <2>2. valid[Proposer[r]].round <= vr
    BY DEF CaseA
  <2> QED
    BY <1>ty, <2>1, <2>2, RegionIntLeTransitive
\*  The timeout disjunct. The entry of c is at `now`, and the prevote is at or
\*  below `now`. A whole propose timeout can therefore not have elapsed.
<1>3. ~ (sentTime[Prevote(c, r, nil)] >= enteredAt[c][r] + TimeoutPropose(r))
  <2>1. sentTime[Prevote(c, r, nil)] <= now
    BY <1>mv DEFS OFF, sent, SentTimeLeNow, TypeOK
\* The entry slot is populated: it is the FIRST conjunct of
\* PrevoteNeedsProposalOrTimeout, so no separate lemma is needed.
  <2>2. enteredAt[c][r] # OFF
    BY DEFS PrevoteNeedsProposalOrTimeout, ValuesOrNil
  <2>3. enteredAt[c][r] >= now /\ enteredAt[c][r] \in Nat
    BY <2>2 DEFS FirstToEnter, Lemma5Hyp, OFF, TypeOK
  <2> QED
    BY <1>ty, <2>1, <2>3
<1> QED
  BY <1>1, <1>2, <1>3, <1>ty

-----------------------------------------------------------------------------
(***************************************************************************)
(* The two latch wrappers of items 11 and 11b.                             *)
(*                                                                         *)
(* WRDurable(r) is durable on its own: only its clock conjunct can move,    *)
(* and the other four read Proposer, Delta and the three timeout constants. *)
(* The NilPrevoteBlocks step lemma reads three region conjuncts beside the  *)
(* global invariants, so its latch carries one durability leg for each:     *)
(* RoundOriginStable, WRDurableLatch and LocksDominateLatch.                *)
(*                                                                         *)
(*  Every boxing lemma below sits in a context with no Spec. Necessitation *)
(*  is not available under an assumed Spec. A step `BY lemma, PTL` for a   *)
(*  goal under [] must therefore be moved out of the theorem that assumes  *)
(*  Spec.                                                                  *)
(***************************************************************************)

\* This is the <2>2 leg of BoxCascadeEntryLatch, standing on its own, because
\* the step lemma takes WRDurable(r) and not CascadeEntry(p, r, b).
LEMMA BoxWRDurableStep ==
  ASSUME NEW r \in Rounds
  PROVE  [](TypeOK /\ [Next]_vars /\ WRDurable(r) => WRDurable(r)')
<1>1. TypeOK /\ [Next]_vars /\ WRDurable(r) => WRDurable(r)'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars, WRDurable(r)
               PROVE  WRDurable(r)'
    OBVIOUS
  <2>1. now >= GST /\ (now' = now \/ now' = now + 1)
    BY NowShape DEF WRDurable
  <2>2. now' >= GST
    BY <2>1, GSTType, GeAcrossTick DEF TypeOK
  <2> QED
    BY <2>2 DEF WRDurable
<1> QED
  BY <1>1, PTL

THEOREM WRDurableLatch ==
  ASSUME NEW r \in Rounds, Spec
  PROVE  [](WRDurable(r) => []WRDurable(r))
<1>inv. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEFS Inv, Spec
<1>st. [](TypeOK /\ [Next]_vars /\ WRDurable(r) => WRDurable(r)')
  BY BoxWRDurableStep
<1> QED
  BY <1>inv, <1>st, PTL

\* Lemma5HypDurable gives CascadeDurable, which is RoundOrigin /\ WRDurable.
LEMMA BoxLemma5HypWRDurable ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](TypeOK /\ Lemma5Hyp(p, r) => WRDurable(r))
<1>1. TypeOK /\ Lemma5Hyp(p, r) => WRDurable(r)
  BY Lemma5HypDurable DEF CascadeDurable
<1> QED
  BY <1>1, PTL

LEMMA BoxNilPrevoteBlocksEntry ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ SentTimeLeNow /\ NilPrevoteRefusedOrTimedOut
              /\ PrevoteNeedsProposalOrTimeout
              /\ Lemma5Hyp(p, r) /\ CaseA(p, r)
              => NilPrevoteBlocks(p, r)  )
BY Lemma5HypGivesNilPrevoteBlocks, PTL

LEMMA BoxNilPrevoteBlocksStep ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
              /\ EnteredCurrentRound /\ HonestProposalUnique
              /\ ValidProposalValue /\ LockedLeValid /\ ValidStrictAtPropose
              /\ ProposeTimerValue /\ CascadeLockFloor
              /\ PrevoteNeedsProposalOrTimeout /\ HonestProposalUnique'
              /\ LockBackedByPrecommit /\ [Next]_vars
              /\ RoundOrigin(p, r) /\ WRDurable(r)
              /\ LocksDominateOrDated(p, r) /\ NilPrevoteBlocks(p, r)
              => NilPrevoteBlocks(p, r)'  )
BY NilPrevoteBlocksStepL, PTL

THEOREM NilPrevoteBlocksLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec
  PROVE  [](  Lemma5Hyp(p, r) /\ CaseA(p, r)
              => []NilPrevoteBlocks(p, r)  )
<1>inv. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
             /\ EnteredCurrentRound /\ HonestProposalUnique
             /\ ValidProposalValue /\ LockedLeValid /\ ValidStrictAtPropose
             /\ ProposeTimerValue /\ CascadeLockFloor
             /\ PrevoteNeedsProposalOrTimeout /\ HonestProposalUnique'
             /\ LockBackedByPrecommit /\ [Next]_vars
             /\ SentTimeLeNow /\ NilPrevoteRefusedOrTimedOut  )
  BY CascadeLockFloorInv, EnteredCurrentRoundInv, HonestProposalUniqueInv,
     InvProof, LockBackedByPrecommitInv, LockedLeValidInv,
     NilPrevoteRefusedOrTimedOutInv, PrevoteNeedsProposalOrTimeoutInv,
     ProposeTimerValueInv, PTL, RoundEntryHistoryInv, SentInvInv,
     SentTimeLeNowInv, ValidProposalValueInv, ValidStrictAtProposeInv
  DEFS Inv, Spec
<1>en. [](  TypeOK /\ SentTimeLeNow /\ NilPrevoteRefusedOrTimedOut
            /\ PrevoteNeedsProposalOrTimeout
            /\ Lemma5Hyp(p, r) /\ CaseA(p, r)
            => NilPrevoteBlocks(p, r)  )
  BY BoxNilPrevoteBlocksEntry
<1>ro. [](TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r))
  BY Lemma5HypRoundOriginBox
<1>rs. [](RoundOrigin(p, r) => []RoundOrigin(p, r))
  BY RoundOriginStable
<1>wd. [](TypeOK /\ Lemma5Hyp(p, r) => WRDurable(r))
  BY BoxLemma5HypWRDurable
<1>ws. [](WRDurable(r) => []WRDurable(r))
  BY WRDurableLatch
<1>ld. [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []LocksDominateOrDated(p, r))
  BY LocksDominateLatch
<1>sp. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
            /\ EnteredCurrentRound /\ HonestProposalUnique
            /\ ValidProposalValue /\ LockedLeValid /\ ValidStrictAtPropose
            /\ ProposeTimerValue /\ CascadeLockFloor
            /\ PrevoteNeedsProposalOrTimeout /\ HonestProposalUnique'
            /\ LockBackedByPrecommit /\ [Next]_vars
            /\ RoundOrigin(p, r) /\ WRDurable(r)
            /\ LocksDominateOrDated(p, r) /\ NilPrevoteBlocks(p, r)
            => NilPrevoteBlocks(p, r)'  )
  BY BoxNilPrevoteBlocksStep
<1> QED
  BY <1>inv, <1>en, <1>ro, <1>rs, <1>wd, <1>ws, <1>ld, <1>sp, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)