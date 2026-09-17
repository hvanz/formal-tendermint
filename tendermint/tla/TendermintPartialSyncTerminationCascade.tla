--------------- MODULE TendermintPartialSyncTerminationCascade -----------------
(***************************************************************************)
(* The quantitative cascade of the repaired paper Lemma 5, and the         *)
(* interface theorems that consume it. This link owns the two reaches      *)
(* to the precommit quorum: CascadeReach, EarlyPolkaNoNil,                 *)
(* EarlyPolkaAbove and EarlyReach. It ends with QuorumReached,             *)
(* EarlyQuorumReached, Lemma5OrBlockingLock, Lemma5OrPriorLock and         *)
(* Lemma5ResolutionExists.                                                 *)
(*                                                                         *)
(* THE CHAIN. The cascade is four links. They are cut so that one edit     *)
(* re-checks one link, and not the whole proof. ...CascadeInvariants holds *)
(* the vocabulary and the global invariants. ...CascadeRegion holds the    *)
(* propose ceiling and the region conjuncts. ...CascadeCore holds the vote *)
(* dates and the joint induction. This module holds the interface. It is   *)
(* link 4 of 4, and the link above is ...CascadeCore.                      *)
(*                                                                         *)
(* THIS LINK KEEPS THE NAME. ...LockRetry extends                          *)
(* TendermintPartialSyncTerminationCascade, so the composition module         *)
(* inherits the whole cascade through the retry layer. Neither module      *)
(* changes. Every definition stays where it was, because only theorems     *)
(* moved here. ...WithinRoundMC and the composition module therefore       *)
(* resolve BlockingLockDuring, PostGSTPriorRoundLock, Lemma5Outcome,       *)
(* Lemma5BlockingOutcome, GoodRoundResolution and Lemma5Reach in           *)
(* ...WithinRound, as before.                                              *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationCascadeCore

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 14. The last stage. The milestone and the ceiling reach            *)
(* DecideEvidence(r).                                                      *)
(*                                                                         *)
(* The shape is the shape of item 10: a pinned ceiling, an unbounded clock *)
(* and one PTL step. It is NOT a WF1, and it needs no fairness at all,     *)
(* because CascadeCore already holds the whole content. CascadeCore        *)
(* arrives as a BOXED hypothesis from its latch, so the region carries the *)
(* milestone and the pin only.                                             *)
(***************************************************************************)

\* The pin is two gossip delays above the deadline. CascadeCore spends one
\* delay from the justified proposal to the polka, and one more from the polka
\* to the precommit quorum.
\*
\* The region carries the three region conjuncts of items 11, 11b and 13c. A
\* latch gives [](hypothesis => []X). That is NOT the global []X that a stage
\* with a temporal hypothesis would need, and to discharge one with the other
\* is unsound. Each X is false before the hypothesis state. Every latched fact
\* therefore travels in the region, with the boxed step lemma of its own item
\* as its preservation leg. The assembly hands all three to the region at the
\* milestone state, in one PTL step.
CascadeReach(p, r, b) ==
  /\ CascadeDurable(p, r)
  /\ ProposalMilestone(p, r)
  /\ LocksDominateOrDated(p, r)
  /\ NilPrevoteBlocks(p, r)
  /\ CascadeCore(p, r)
  /\ CascadeDeadline(p, r) + 2 * Delta <= b

LEMMA DeadlinePinOrder ==
  ASSUME NEW e \in Nat, NEW d \in Nat, NEW k \in Nat, NEW g \in Nat,
         NEW bb \in Nat, NEW n \in Nat,
         e > g, (e + 2 * d + k) + 2 * d <= bb, n > bb
  PROVE  /\ e + 2 * d + k \in Nat
         /\ e + 2 * d + k >= g
         /\ e <= e + 2 * d + k
         /\ e + d + k <= (e + 2 * d + k) + d
         /\ n > (e + 2 * d + k) + 2 * d
<1>1. e + 2 * d + k \in Nat
  OBVIOUS
<1>2. e + 2 * d + k >= g
  BY SMT
<1>3. e <= e + 2 * d + k
  OBVIOUS
<1>4. e + d + k <= (e + 2 * d + k) + d
  BY SMT
<1>5. n > (e + 2 * d + k) + 2 * d
  BY SMT
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

\* The durable part of the region. The three region conjuncts arrive primed
\* from their own boxed step lemmas, so this leg carries the milestone and the
\* pin only.
LEMMA BoxCascadeReachLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
              /\ [Next]_vars /\ CascadeReach(p, r, b)
              /\ LocksDominateOrDated(p, r)' /\ NilPrevoteBlocks(p, r)'
              /\ CascadeCore(p, r)'
              => CascadeReach(p, r, b)'  )
<1>1. TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory /\ [Next]_vars
      /\ CascadeReach(p, r, b)
      /\ LocksDominateOrDated(p, r)' /\ NilPrevoteBlocks(p, r)'
      /\ CascadeCore(p, r)'
        => CascadeReach(p, r, b)'
  <2> SUFFICES ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory,
                      [Next]_vars, CascadeReach(p, r, b),
                      LocksDominateOrDated(p, r)', NilPrevoteBlocks(p, r)',
                      CascadeCore(p, r)'
               PROVE  CascadeReach(p, r, b)'
    OBVIOUS
  <2>d. /\ RoundOrigin(p, r)
        /\ WRDurable(r)
        /\ CascadeDeadline(p, r) + 2 * Delta <= b
    BY DEFS CascadeDurable, CascadeReach
  <2>1. RoundOrigin(p, r)'
    BY <2>d, RoundOriginStep
\* Only the clock conjunct of WRDurable can move.
  <2>2. WRDurable(r)'
    <3>1. now >= GST /\ (now' = now \/ now' = now + 1)
      BY <2>d, NowShape DEF WRDurable
    <3>2. now' >= GST
      BY <3>1, GSTType, GeAcrossTick DEF TypeOK
    <3> QED
      BY <2>d, <3>2 DEF WRDurable
  <2>3. enteredAt'[p][r] = enteredAt[p][r]
    BY <2>d, EnteredAtFrozenStep DEF RoundOrigin
  <2>4. PICK v \in Values : Valid(v) /\ Justified(r, v, CascadeDeadline(p, r))
    BY DEFS CascadeReach, ProposalMilestone, ProposalStage
  <2>5. Justified(r, v, CascadeDeadline(p, r))'
    BY <2>3, <2>4, JustifiedMove DEF CascadeDeadline
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5
    DEFS CascadeDeadline, CascadeDurable, CascadeReach, ProposalMilestone,
         ProposalStage
<1> QED
  BY <1>1, PTL

\* The whole region across one step. The three legs are the boxed step lemmas
\* of items 11, 11b and 13c, unchanged.
LEMMA BoxCascadeReachStep ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
              /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
              /\ EnteredCurrentRound /\ GossipDeadline /\ EntryWindowCore
              /\ CrossingBacked /\ PrecommitBacked /\ PrevoteJustified
              /\ PrevoteOncePerRound /\ HonestProposalUnique
              /\ HonestProposalUnique' /\ ValidProposalValue /\ LockedLeValid
              /\ ValidStrictAtPropose /\ ProposeTimerValue /\ CascadeLockFloor
              /\ PrevoteNeedsProposalOrTimeout /\ LockBackedByPrecommit
              /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
              /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
              /\ DecidedStepOp /\ ProposalDated /\ PrevoteArmedQuorumTimed
              /\ [Next]_vars /\ CascadeReach(p, r, b)
              => CascadeReach(p, r, b)'  )
<1>d. [](CascadeReach(p, r, b) => RoundOrigin(p, r) /\ WRDurable(r))
  <2>1. CascadeReach(p, r, b) => RoundOrigin(p, r) /\ WRDurable(r)
    BY DEFS CascadeDurable, CascadeReach
  <2> QED
    BY <2>1, PTL
<1>ld. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv
            /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
            /\ [Next]_vars /\ RoundOrigin(p, r)
            /\ LocksDominateOrDated(p, r) => LocksDominateOrDated(p, r)'  )
  BY BoxLocksDominateStep
<1>np. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
            /\ EnteredCurrentRound /\ HonestProposalUnique
            /\ ValidProposalValue /\ LockedLeValid /\ ValidStrictAtPropose
            /\ ProposeTimerValue /\ CascadeLockFloor
            /\ PrevoteNeedsProposalOrTimeout /\ HonestProposalUnique'
            /\ LockBackedByPrecommit /\ [Next]_vars
            /\ RoundOrigin(p, r) /\ WRDurable(r)
            /\ LocksDominateOrDated(p, r) /\ NilPrevoteBlocks(p, r)
            => NilPrevoteBlocks(p, r)'  )
  BY BoxNilPrevoteBlocksStep
<1>cc. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
            /\ GossipDeadline /\ EntryWindowCore /\ CrossingBacked
            /\ EnteredAtLeNow /\ EnteredCurrentRound /\ PrecommitBacked
            /\ PrevoteJustified /\ PrevoteOncePerRound
            /\ HonestProposalUnique /\ HonestProposalUnique'
            /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
            /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
            /\ DecidedStepOp /\ ProposalDated
            /\ PrevoteNeedsProposalOrTimeout /\ PrevoteArmedQuorumTimed
            /\ RoundEntryHistory /\ [Next]_vars
            /\ RoundOrigin(p, r) /\ WRDurable(r) /\ NilPrevoteBlocks(p, r)
            /\ CascadeCore(p, r)
            => CascadeCore(p, r)'  )
  BY BoxCascadeCoreStep
<1>re. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
            /\ [Next]_vars /\ CascadeReach(p, r, b)
            /\ LocksDominateOrDated(p, r)' /\ NilPrevoteBlocks(p, r)'
            /\ CascadeCore(p, r)'
            => CascadeReach(p, r, b)'  )
  BY BoxCascadeReachLatch
<1>rd. [](  CascadeReach(p, r, b)
            => LocksDominateOrDated(p, r) /\ NilPrevoteBlocks(p, r)
               /\ CascadeCore(p, r)  )
  <2>1. CascadeReach(p, r, b)
          => LocksDominateOrDated(p, r) /\ NilPrevoteBlocks(p, r)
             /\ CascadeCore(p, r)
    BY DEF CascadeReach
  <2> QED
    BY <2>1, PTL
<1> QED
  BY <1>d, <1>ld, <1>np, <1>cc, <1>re, <1>rd, PTL

\* The state content of the stage. Above the pin, CascadeCore turns the dated
\* justification into the precommit quorum. The escape then has only two other
\* disjuncts. They are the decision, which the stage excludes, and the
\* blocking lock, which is the other outcome of paper Lemma 5.
LEMMA BoxQuorumFromReach ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ ~SomeCorrectDecided /\ CascadeReach(p, r, b) /\ now > b
              => DecideEvidence(r) \/ BlockingLockDuring(p, r)  )
<1>1. TypeOK /\ ~SomeCorrectDecided /\ CascadeReach(p, r, b) /\ now > b
        => DecideEvidence(r) \/ BlockingLockDuring(p, r)
  <2> SUFFICES ASSUME TypeOK, ~SomeCorrectDecided, CascadeReach(p, r, b),
                      now > b
               PROVE  DecideEvidence(r) \/ BlockingLockDuring(p, r)
    OBVIOUS
  <2>d. /\ RoundOrigin(p, r)
        /\ CascadeCore(p, r)
        /\ CascadeDeadline(p, r) + 2 * Delta <= b
    BY DEFS CascadeDurable, CascadeReach
  <2>1. PICK v \in Values : Valid(v) /\ Justified(r, v, CascadeDeadline(p, r))
    BY DEFS CascadeReach, ProposalMilestone, ProposalStage
  <2>ty. /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
         /\ Delta \in Nat /\ TimeoutPrecommit(r - 1) \in Nat
         /\ now \in Nat /\ GST \in Nat
    <3>1. r > 0 /\ enteredAt[p][r] # OFF /\ enteredAt[p][r] > GST
      BY <2>d DEF RoundOrigin
    <3>2. TimeoutPrecommit(r - 1) \in Nat
      BY <3>1, RoundTypes
    <3> QED
      BY <3>1, <3>2, DeltaType, GSTType DEFS OFF, TypeOK
  <2>ar. /\ CascadeDeadline(p, r) \in Nat
         /\ CascadeDeadline(p, r) >= GST
         /\ enteredAt[p][r] <= CascadeDeadline(p, r)
         /\ CascadeCeiling(p, r) <= CascadeDeadline(p, r) + Delta
         /\ now > CascadeDeadline(p, r) + 2 * Delta
    BY <2>d, <2>ty, DeadlinePinOrder DEFS CascadeCeiling, CascadeDeadline
  <2>2. CascadeEscape(p, r, v)
    BY <2>1, <2>ar, <2>d, CoreJustifiedGivesEscape
  <2>3. PrecommitQuorumFor(r, v) \/ BlockingLockDuring(p, r)
    BY <2>2 DEF CascadeEscape
  <2>4. CASE PrecommitQuorumFor(r, v)
    <3>1. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
      BY <2>1, JustifiedGivesProposal
    <3> QED
      BY <2>1, <2>4, <3>1 DEFS DecideEvidence, PrecommitQuorumFor
  <2> QED
    BY <2>3, <2>4
<1> QED
  BY <1>1, PTL

\* The per-b stage. The pin is a constant here, so ClockUnbounded is cited at b
\* by identity, the only shape a temporal conclusion supports.
THEOREM QuorumReachedAt ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided,
         NEW b \in Nat
  PROVE  CascadeReach(p, r, b) ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
<1>cu. <>[](now > b)
  BY ClockUnbounded
<1>nd. []~SomeCorrectDecided
  OBVIOUS
<1>ds. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>inv. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
             /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
             /\ EnteredCurrentRound /\ GossipDeadline /\ EntryWindowCore
             /\ CrossingBacked /\ [Next]_vars  )
  BY CrossingBackedInv, EnteredAtLeNowInv, EnteredCurrentRoundInv,
     EntryWindowCoreInv, GossipDeadlineInv, InvProof, PTL, RoundEntryHistoryInv,
     SentInvInv, SentTimeLeNowInv, TypeOKBothStates, ValidBelowRoundInv
  DEFS Inv, Spec
<1>inv2. [](  PrecommitBacked /\ PrevoteJustified /\ PrevoteOncePerRound
              /\ HonestProposalUnique /\ HonestProposalUnique'
              /\ ValidProposalValue /\ LockedLeValid /\ ValidStrictAtPropose
              /\ ProposeTimerValue /\ CascadeLockFloor  )
  BY CascadeLockFloorInv, HonestProposalUniqueInv, LockedLeValidInv,
     PrecommitBackedInv, PrevoteJustifiedInv, PrevoteOncePerRoundInv,
     ProposeTimerValueInv, PTL, ValidProposalValueInv, ValidStrictAtProposeInv
<1>inv3. [](  PrevoteNeedsProposalOrTimeout /\ LockBackedByPrecommit
              /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
              /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
              /\ ProposalDated /\ PrevoteArmedQuorumTimed  )
  BY LockBackedByPrecommitInv, NilPrevoteInWindowInv,
     PrevoteArmedQuorumTimedInv, PrevoteNeedsProposalOrTimeoutInv,
     ProposalDatedInv, PTL, RoundVoteAfterEntryInv,
     StepPastProposeHasPrevoteInv, StepPrecommitHasPrecommitInv
<1>la. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
            /\ RoundEntryHistory /\ ValidBelowRound /\ EnteredAtLeNow
            /\ EnteredCurrentRound /\ GossipDeadline /\ EntryWindowCore
            /\ CrossingBacked /\ PrecommitBacked /\ PrevoteJustified
            /\ PrevoteOncePerRound /\ HonestProposalUnique
            /\ HonestProposalUnique' /\ ValidProposalValue /\ LockedLeValid
            /\ ValidStrictAtPropose /\ ProposeTimerValue /\ CascadeLockFloor
            /\ PrevoteNeedsProposalOrTimeout /\ LockBackedByPrecommit
            /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
            /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
            /\ DecidedStepOp /\ ProposalDated /\ PrevoteArmedQuorumTimed
            /\ [Next]_vars /\ CascadeReach(p, r, b)
            => CascadeReach(p, r, b)'  )
  BY BoxCascadeReachStep
<1>go. [](  TypeOK /\ ~SomeCorrectDecided /\ CascadeReach(p, r, b) /\ now > b
            => DecideEvidence(r) \/ BlockingLockDuring(p, r)  )
  BY BoxQuorumFromReach
<1> QED
  BY <1>cu, <1>nd, <1>ds, <1>inv, <1>inv2, <1>inv3, <1>la, <1>go, PTL

\* ---- The existential lift over the pin ------------------------------------
LEMMA CascadeReachCommute ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW TEMPORAL D,
         \A b \in Nat : [](CascadeReach(p, r, b) => D)
  PROVE  [](\A b \in Nat : (CascadeReach(p, r, b) => D))
OBVIOUS

LEMMA CascadeReachBoxFO ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  (\A b \in Nat :
                 (CascadeReach(p, r, b)
                    => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r))))
              => ((\E b \in Nat : CascadeReach(p, r, b))
                    => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r)))  )
<1>1. (\A b \in Nat :
         (CascadeReach(p, r, b)
            => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r))))
      => ((\E b \in Nat : CascadeReach(p, r, b))
            => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r)))
  OBVIOUS
<1> QED
  BY <1>1, PTL

\* The entry into the region. The deadline of the milestone state, plus two
\* gossip delays, is itself a natural, so it is its own witness for b.
LEMMA BoxCascadeReachFromMilestone ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ ProposalMilestone(p, r) /\ LocksDominateOrDated(p, r)
              /\ NilPrevoteBlocks(p, r) /\ CascadeCore(p, r)
              => (\E b \in Nat : CascadeReach(p, r, b))  )
<1>1. TypeOK /\ ProposalMilestone(p, r) /\ LocksDominateOrDated(p, r)
      /\ NilPrevoteBlocks(p, r) /\ CascadeCore(p, r)
        => (\E b \in Nat : CascadeReach(p, r, b))
  <2> SUFFICES ASSUME TypeOK, ProposalMilestone(p, r),
                      LocksDominateOrDated(p, r), NilPrevoteBlocks(p, r),
                      CascadeCore(p, r)
               PROVE  \E b \in Nat : CascadeReach(p, r, b)
    OBVIOUS
  <2>d. CascadeDurable(p, r) /\ RoundOrigin(p, r)
    BY DEFS CascadeDurable, ProposalMilestone, ProposalStage
  <2>ty. /\ enteredAt[p][r] \in Nat /\ Delta \in Nat
         /\ TimeoutPrecommit(r - 1) \in Nat
    <3>1. r > 0 /\ enteredAt[p][r] # OFF
      BY <2>d DEF RoundOrigin
    <3>2. TimeoutPrecommit(r - 1) \in Nat
      BY <3>1, RoundTypes
    <3> QED
      BY <3>1, <3>2, DeltaType DEFS OFF, TypeOK
  <2>1. /\ CascadeDeadline(p, r) + 2 * Delta \in Nat
        /\ CascadeDeadline(p, r) + 2 * Delta <= CascadeDeadline(p, r) + 2 * Delta
    BY <2>ty, NatLeReflexive DEF CascadeDeadline
  <2> QED
    BY <2>1, <2>d DEF CascadeReach
<1> QED
  BY <1>1, PTL

THEOREM QuorumReached ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided
  PROVE  (  ProposalMilestone(p, r) /\ LocksDominateOrDated(p, r)
            /\ NilPrevoteBlocks(p, r) /\ CascadeCore(p, r)  )
           ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
<1>1. \A b \in Nat :
        [](  CascadeReach(p, r, b)
             => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r))  )
  <2> SUFFICES ASSUME NEW b \in Nat
               PROVE  [](  CascadeReach(p, r, b)
                           => <>(DecideEvidence(r)
                                   \/ BlockingLockDuring(p, r))  )
    OBVIOUS
  <2>1. CascadeReach(p, r, b)
          ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
    BY QuorumReachedAt
  <2> QED
    BY <2>1, PTL
<1>2. [](  \A b \in Nat :
             (CascadeReach(p, r, b)
                => <>(DecideEvidence(r) \/ BlockingLockDuring(p, r)))  )
  BY <1>1, CascadeReachCommute
<1>3. (\E b \in Nat : CascadeReach(p, r, b))
        ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
  BY <1>2, CascadeReachBoxFO, PTL
<1>4. [](  TypeOK /\ ProposalMilestone(p, r) /\ LocksDominateOrDated(p, r)
           /\ NilPrevoteBlocks(p, r) /\ CascadeCore(p, r)
           => (\E b \in Nat : CascadeReach(p, r, b))  )
  BY BoxCascadeReachFromMilestone
<1>ty. []TypeOK
  BY InvProof, PTL DEFS Inv, Spec
<1> QED
  BY <1>3, <1>4, <1>ty, PTL
-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 15, Case B. The early polka, and the two invariants it needs.      *)
(*                                                                         *)
(* Case B is the state where valid[Proposer[r]].round is above the          *)
(* validRound of the round-r proposal. Item 6 shows that this forces a      *)
(* round-r polka for the proposed value into the pool AT the entry of p.    *)
(* Round r then decides, and no lock is involved. NilPrevoteBlocks is FALSE *)
(* here, because the lock behind a refusal need not be dated after the      *)
(* entry, so Case B cannot use CascadeCore. It uses the polka directly.     *)
(*                                                                         *)
(* Three clauses of LockWindowCore do the work of the whole induction.     *)
(* Read at the polka, clause 1 excludes a correct validator below r.       *)
(* Clause 2 excludes one at r in step "propose", and clause 5 excludes one *)
(* at r in step "prevote". One gossip delay above the polka, every correct *)
(* validator is therefore at r in step "precommit", at r in step           *)
(* "decided", or above r. Each of those three positions carries a          *)
(* precommit at r.                                                         *)
(*                                                                         *)
(* Two facts do not follow from the state alone. Each one is therefore a   *)
(* global invariant that carries the region facts in its antecedent, in    *)
(* the shape of ProposalDated and NilPrevoteInWindow. EarlyPolkaNoNil says *)
(* that no correct validator precommits nil at r. EarlyPolkaAbove says     *)
(* that a correct validator above r has precommitted the value at r. That  *)
(* is the first-to-leave argument. To leave r needs the precommit timer or *)
(* SkipRound, and both report evidence that dates the departure above the  *)
(* window.                                                                 *)
(*                                                                         *)
(* Both invariants carry the polka DATE as a parameter T, and never as the  *)
(* expression enteredAt[p][r]. Priming an invariant must not prime an       *)
(* operator ARGUMENT, or PolkaBack no longer matches. T >= GST and          *)
(* T <= enteredAt[p][r] are what the consumer supplies, and the consumer    *)
(* has both because the entry of p is above GST.                           *)
(*                                                                         *)
(* Each one also carries the clock guard now > enteredAt[p][r] + Delta,    *)
(* and that guard is useful three times. The fresh-entry case of the       *)
(* induction becomes arithmetic, because one Tick cannot clear a gossip    *)
(* delay. The guard licenses PolkaBack, because it forces now > T. The     *)
(* consumer stage establishes it in any case.                              *)
(***************************************************************************)

-----------------------------------------------------------------------------
\* Arithmetic in a minimal context, one fact per lemma.

\* The clock guard, read back across one step. A Tick cannot clear a gossip
\* delay, so the guard was within one instant of holding before the step.
LEMMA GuardBack ==
  ASSUME NEW n \in Nat, NEW np \in Int, NEW t \in Nat, NEW d \in Nat,
         d > 1, np <= n + 1, np > t + d
  PROVE  /\ n >= t + d
         /\ n > t
BY SMT

\* A nil precommit at the deadline would need prevote evidence a whole prevote
\* timeout earlier. That is below the entry, where there is no correct round-r
\* vote.
LEMMA BackingBelowEntry ==
  ASSUME NEW t \in Nat, NEW s2 \in Int, NEW tt \in Nat, NEW d \in Nat,
         NEW tv \in Int, d > 1, tv > 2 * d, s2 >= tt, s2 <= t - tv, t <= tt + d
  PROVE  FALSE
BY SMT

\* An armed prevote timer at r is due more than two gossip delays above the
\* entry. Clause 5 of LockWindowCore stops the clock one gossip delay above
\* it. The two readings cannot both hold.
LEMMA TimerAboveWindow ==
  ASSUME NEW n \in Nat, NEW tt \in Nat, NEW d \in Nat, NEW tm \in Int,
         NEW q2 \in Int, NEW tv \in Int,
         d > 1, tv > 2 * d, q2 >= tt, tm = q2 + tv, n >= tm, n <= tt + d
  PROVE  FALSE
BY SMT

\* The departure of a correct validator from r dates a correct precommit at r
\* a whole precommit timeout earlier. The clock is therefore above the
\* deadline.
LEMMA DepartureAboveWindow ==
  ASSUME NEW n \in Nat, NEW tt \in Nat, NEW d \in Nat, NEW k \in Nat,
         NEW s2 \in Int, d > 1, k > 2 * d, s2 >= tt, s2 <= n - k
  PROVE  n > tt + d
BY SMT

\* The polka date sits at or below the entry, so a bound read at the entry is a
\* bound read at the polka.
LEMMA WindowAtEntry ==
  ASSUME NEW n \in Nat, NEW t \in Nat, NEW tt \in Nat, NEW d \in Nat,
         t <= tt, n > tt + d
  PROVE  n > t + d
BY SMT

-----------------------------------------------------------------------------
\* RoundOrigin at the primed state, with the entry slot already written, holds
\* at the pre-state as well. An entry slot is write once, so every slot that
\* carries a value carries the same value at both states.
LEMMA RoundOriginBack ==
  ASSUME TypeOK, RoundEntryHistory, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds,
         enteredAt[p][r] # OFF, RoundOrigin(p, r)'
  PROVE  RoundOrigin(p, r)
<1>ud. EntryUpdateDiscipline
  BY EntryUpdateDisciplineStep
<1>1. enteredAt'[p][r] = enteredAt[p][r]
  BY <1>ud DEF EntryUpdateDiscipline
<1>2. r > 0 /\ enteredAt[p][r] > GST
  BY <1>1 DEF RoundOrigin
<1>3. ASSUME NEW c \in Honest, enteredAt[c][r] # OFF
      PROVE  enteredAt[c][r] >= enteredAt[p][r]
  <2>1. enteredAt'[c][r] = enteredAt[c][r]
    BY <1>3, <1>ud DEF EntryUpdateDiscipline
  <2>2. enteredAt'[c][r] >= enteredAt'[p][r]
    BY <1>3, <2>1 DEFS EntriesAtOrAfter, OFF, RoundOrigin
  <2> QED
    BY <1>1, <2>1, <2>2
<1> QED
  BY <1>2, <1>3 DEFS EntriesAtOrAfter, RoundOrigin

\* Every correct round-r vote is dated at or after the entry of p. This is
\* RoundVoteAfterEntry composed with the EntriesAtOrAfter conjunct of
\* RoundOrigin, and every anchor below reads it.
LEMMA RoundVoteAfterOrigin ==
  ASSUME TypeOK, RoundVoteAfterEntry,
         NEW p \in Honest, NEW r \in Rounds, RoundOrigin(p, r),
         NEW y \in Honest, NEW w \in ValuesOrNil
  PROVE  /\ (  Prevote(y, r, w) \in sent
               => sentTime[Prevote(y, r, w)] >= enteredAt[p][r]  )
         /\ (  Precommit(y, r, w) \in sent
               => sentTime[Precommit(y, r, w)] >= enteredAt[p][r]  )
<1>e. enteredAt[p][r] \in Int
  BY DEFS OFF, RoundOrigin, TypeOK
<1>1. ASSUME Prevote(y, r, w) \in sent
      PROVE  sentTime[Prevote(y, r, w)] >= enteredAt[p][r]
  <2>1. /\ enteredAt[y][r] # OFF
        /\ sentTime[Prevote(y, r, w)] >= enteredAt[y][r]
    BY <1>1 DEF RoundVoteAfterEntry
  <2>2. enteredAt[y][r] >= enteredAt[p][r]
    BY <2>1 DEFS EntriesAtOrAfter, RoundOrigin
  <2>m. Prevote(y, r, w) \in Message
    BY HonestSubValidators, MsgPrevote
  <2>ty. /\ sentTime[Prevote(y, r, w)] \in Int
         /\ enteredAt[y][r] \in Int
    BY <1>1, <2>1, <2>m DEFS OFF, sent, TypeOK
  <2> QED
    BY <1>e, <2>1, <2>2, <2>ty
<1>2. ASSUME Precommit(y, r, w) \in sent
      PROVE  sentTime[Precommit(y, r, w)] >= enteredAt[p][r]
  <2>1. /\ enteredAt[y][r] # OFF
        /\ sentTime[Precommit(y, r, w)] >= enteredAt[y][r]
    BY <1>2 DEF RoundVoteAfterEntry
  <2>2. enteredAt[y][r] >= enteredAt[p][r]
    BY <2>1 DEFS EntriesAtOrAfter, RoundOrigin
  <2>m. Precommit(y, r, w) \in Message
    BY HonestSubValidators, MsgPrecommit
  <2>ty. /\ sentTime[Precommit(y, r, w)] \in Int
         /\ enteredAt[y][r] \in Int
    BY <1>2, <2>1, <2>m DEFS OFF, sent, TypeOK
  <2> QED
    BY <1>e, <2>1, <2>2, <2>ty
<1> QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
\* Case B's first invariant. An early polka at r excludes a correct nil
\* precommit at r, once the clock has passed the entry by one gossip delay.
EarlyPolkaNoNil ==
  \A p \in Honest, r \in Rounds, v \in Values, c \in Honest, T \in Nat :
    ( /\ RoundOrigin(p, r)
      /\ Valid(v)
      /\ T >= GST
      /\ T <= enteredAt[p][r]
      /\ PolkaDated(r, v, T)
      /\ Lemma5Timeouts(r)
      /\ now > enteredAt[p][r] + Delta )
    => Precommit(c, r, nil) \notin sent \/ SomeCorrectDecided

LEMMA EarlyPolkaNoNilStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, SentTimeLeNow,
         RoundEntryHistory, LockWindowCore, PrevoteOncePerRound,
         PrecommitBacked, PrevoteArmedQuorumTimed, PrevoteJustified,
         RoundVoteAfterEntry, [Next]_vars, EarlyPolkaNoNil
  PROVE  EarlyPolkaNoNil'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
                    NEW c \in Honest, NEW T \in Nat,
                    RoundOrigin(p, r)', Valid(v), T >= GST,
                    T <= enteredAt'[p][r], PolkaDated(r, v, T)',
                    Lemma5Timeouts(r), now' > enteredAt'[p][r] + Delta,
                    Precommit(c, r, nil) \in sent',
                    ~ SomeCorrectDecided'
             PROVE  FALSE
  BY DEF EarlyPolkaNoNil
<1>nd. ~ SomeCorrectDecided
  BY DecidedLatchStep
<1>r0. r > 0
  BY DEF RoundOrigin
<1>ty. /\ now \in Nat /\ now' \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ GST \in Nat /\ r \in Nat /\ T \in Nat
       /\ TimeoutPrecommit(r - 1) \in Nat
       /\ TimeoutPrevote(r) \in Int /\ TimeoutPrevote(r) > 2 * Delta
  <2>1. /\ TimeoutPrecommit(r - 1) \in Nat
        /\ TimeoutPrecommit(r - 1) > 0
    BY <1>r0, RoundTypes
  <2>2. TimeoutPrevote(r) \in Int
    BY T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
  <2> QED
    BY <1>r0, <2>1, <2>2, DeltaType, GSTType
    DEFS Lemma5Timeouts, Rounds, TypeOK
<1>np. now' <= now + 1
  BY <1>ty, NowShape
\* A fresh entry pins the entry AT the clock, and one Tick cannot clear a
\* gossip delay. The guard of the clause cannot therefore have become true.
<1>a. CASE enteredAt[p][r] = OFF
  <2>1. enteredAt'[p][r] = now
    BY <1>a, EntryUpdateDisciplineStep
    DEFS EntryUpdateDiscipline, OFF, RoundOrigin
  <2> QED
    BY <1>np, <1>ty, <2>1
<1>b. CASE enteredAt[p][r] # OFF
  <2>fr. enteredAt'[p][r] = enteredAt[p][r]
    BY <1>b, EnteredAtFrozenStep
  <2>ro. RoundOrigin(p, r)
    BY <1>b, RoundOriginBack
  <2>ty. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
    BY <2>ro, GSTType DEFS OFF, RoundOrigin, TypeOK
  <2>le. T <= enteredAt[p][r]
    BY <2>fr
  <2>cl. /\ now >= enteredAt[p][r] + Delta
         /\ now > enteredAt[p][r]
    BY <1>np, <1>ty, <2>fr, <2>ty, GuardBack
\* PolkaBack takes the negated form, so it is stated that way. The conversion
\* from now > T needs both sides typed, and a leaf that has to do that as well
\* fails.
  <2>gT. ~ (now <= T)
    BY <1>ty, <2>cl, <2>le, <2>ty
  <2>pk. PolkaDated(r, v, T)
    BY <1>ty, <2>gT, PolkaBack DEF ValuesOrNil
  <2>any. AnyPrevoteDated(r, T)
    BY <2>pk, PolkaIsAnyPrevote DEF ValuesOrNil
  <2>ju. Justified(r, v, T)
    BY <1>ty, <2>pk, JustifiedFromPolka
\* The nil precommit is old. Either the guard held before the step, and the
\* pre-state instance closes it, or the clock is exactly at the deadline. In
\* that second case the backing of the precommit is dated below the entry.
  <2>1. CASE Precommit(c, r, nil) \in sent
    <3>1. CASE now > enteredAt[p][r] + Delta
      BY <1>nd, <1>ty, <2>1, <2>le, <2>pk, <2>ro, <3>1 DEF EarlyPolkaNoNil
    <3>2. CASE now = enteredAt[p][r] + Delta
      <4>m. Precommit(c, r, nil) \in Message
        BY HonestSubValidators, MsgPrecommit DEF ValuesOrNil
      <4>t. /\ sentTime[Precommit(c, r, nil)] \in Nat
            /\ sentTime[Precommit(c, r, nil)] <= now
            /\ sentTime[Precommit(c, r, nil)]
                 <= sentTime[Precommit(c, r, nil)]
        <5>1. /\ sentTime[Precommit(c, r, nil)] \in Nat
              /\ sentTime[Precommit(c, r, nil)] <= now
          BY <2>1, <4>m DEFS OFF, sent, SentTimeLeNow, TypeOK
        <5> QED
          BY <5>1, NatLeReflexive
      <4>1. Backing(r, nil, sentTime[Precommit(c, r, nil)])
        BY <2>1, <4>t DEFS PrecommitBacked, ValuesOrNil
      <4>2. CASE PolkaDated(r, nil, sentTime[Precommit(c, r, nil)])
        BY <2>pk, <4>2, NilNotInValues, TwoPolkasAgree DEF ValuesOrNil
      <4>3. CASE AnyPrevoteDated(r, sentTime[Precommit(c, r, nil)]
                                      - TimeoutPrevote(r))
        <5>1. PICK y \in Honest, w \in ValuesOrNil :
                /\ Prevote(y, r, w) \in sent
                /\ sentTime[Prevote(y, r, w)]
                     <= sentTime[Precommit(c, r, nil)] - TimeoutPrevote(r)
          BY <4>3, AnyPrevoteHasHonest
        <5>2. sentTime[Prevote(y, r, w)] >= enteredAt[p][r]
          BY <2>ro, <5>1, RoundVoteAfterOrigin
        <5>m. Prevote(y, r, w) \in Message
          BY HonestSubValidators, MsgPrevote
        <5>ty. sentTime[Prevote(y, r, w)] \in Int
          BY <5>1, <5>m DEFS OFF, sent, TypeOK
        <5> QED
          BY <1>ty, <2>ty, <3>2, <4>t, <5>1, <5>2, <5>ty, BackingBelowEntry
      <4> QED
        BY <4>1, <4>2, <4>3, NilNotInValues DEF Backing
    <3> QED
      BY <1>ty, <2>cl, <2>ty, <3>1, <3>2
\* The nil precommit is fresh. FreshPrecommitAction names the three emitters.
  <2>2. CASE Precommit(c, r, nil) \notin sent
    <3>m. Precommit(c, r, nil) \in Message
      BY HonestSubValidators, MsgPrecommit DEF ValuesOrNil
    <3>1. /\ round[c] = r
          /\ \/ OnPrevoteQuorumValueFirstTime(c)
             \/ OnPrevoteQuorumNil(c)
             \/ OnTimeoutPrevote(c)
      <4>1. /\ Precommit(c, r, nil).round
                 = round[Precommit(c, r, nil).sender]
            /\ \/ OnPrevoteQuorumValueFirstTime(Precommit(c, r, nil).sender)
               \/ OnPrevoteQuorumNil(Precommit(c, r, nil).sender)
               \/ OnTimeoutPrevote(Precommit(c, r, nil).sender)
        BY <2>2, <3>m, FreshPrecommitAction DEF Precommit
      <4> QED
        BY <4>1 DEF Precommit
\* A value precommit cannot be the fresh nil one.
    <3>2. CASE OnPrevoteQuorumValueFirstTime(c)
      <4>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
              Broadcast(c, Precommit(c, round[c], prop.value))
        BY <3>2 DEF OnPrevoteQuorumValueFirstTime
      <4>2. prop.value \in Values
        BY <4>1, HonestSubValidators, RProposalValueTyped DEFS Rounds, TypeOK
      <4>3. Precommit(c, r, nil) = Precommit(c, round[c], prop.value)
        BY <2>2, <3>m, <4>1 DEFS Broadcast, OFF, sent, TypeOK
      <4> QED
        BY <4>2, <4>3, NilNotInValues DEF Precommit
\* A nil polka in the view of c is a nil polka in the pool, and two polkas at
\* one round agree.
    <3>3. CASE OnPrevoteQuorumNil(c)
      <4>1. RExistsPrevoteQuorum(c, nil, round[c])
        BY <3>3 DEF OnPrevoteQuorumNil
      <4>2. PolkaDated(r, nil, now)
        BY <3>1, <4>1, ViewPolkaDated DEFS Rounds, TypeOK, ValuesOrNil
      <4> QED
        BY <2>pk, <4>2, NilNotInValues, TwoPolkasAgree DEF ValuesOrNil
\* The prevote timer of c is armed by a quorum that holds a correct round-r
\* prevote. It is therefore due more than two gossip delays above the entry.
\* Clause 5 of LockWindowCore stops the clock one gossip delay above the
\* polka.
    <3>4. CASE OnTimeoutPrevote(c)
      <4>1. /\ step[c] = "prevote"
            /\ timer[c]["prevote"] # OFF
            /\ now >= timer[c]["prevote"]
        BY <3>4 DEF OnTimeoutPrevote
      <4>2. now <= T + Delta
        BY <1>ty, <2>any, <2>ju, <2>pk, <3>1, <4>1 DEF LockWindowCore
      <4>3. PICK Q \in ByzQuorum :
              \A s \in Q : \E vv \in ValuesOrNil :
                /\ Prevote(s, round[c], vv) \in sent
                /\ sentTime[Prevote(s, round[c], vv)]
                     <= timer[c]["prevote"] - TimeoutPrevote(round[c])
        BY <4>1 DEF PrevoteArmedQuorumTimed
      <4>4. AnyPrevoteDated(r, timer[c]["prevote"] - TimeoutPrevote(r))
        BY <3>1, <4>3 DEF AnyPrevoteDated
      <4>5. PICK y \in Honest, w \in ValuesOrNil :
              /\ Prevote(y, r, w) \in sent
              /\ sentTime[Prevote(y, r, w)]
                   <= timer[c]["prevote"] - TimeoutPrevote(r)
        BY <4>4, AnyPrevoteHasHonest
      <4>6. sentTime[Prevote(y, r, w)] >= enteredAt[p][r]
        BY <2>ro, <4>5, RoundVoteAfterOrigin
      <4>m. Prevote(y, r, w) \in Message
        BY HonestSubValidators, MsgPrevote
      <4>ty. /\ timer[c]["prevote"] \in Int
             /\ sentTime[Prevote(y, r, w)] \in Int
        BY <4>5, <4>m, HonestSubValidators DEFS OFF, sent, TimerType, TypeOK
      <4>7. timer[c]["prevote"]
              = (timer[c]["prevote"] - TimeoutPrevote(r)) + TimeoutPrevote(r)
        BY <1>ty, <4>ty
\* The window bound reads at the entry, and the polka sits at or below it.
      <4>8. now <= enteredAt[p][r] + Delta
        BY <1>ty, <2>le, <2>ty, <4>2
      <4> QED
        BY <1>ty, <2>ty, <4>1, <4>5, <4>6, <4>7, <4>8, <4>ty, TimerAboveWindow
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>a, <1>b

THEOREM EarlyPolkaNoNilInv ==
  ASSUME Spec PROVE []EarlyPolkaNoNil
<1>1. EarlyPolkaNoNil
  BY ByzNonEmpty DEFS EarlyPolkaNoNil, Init, OFF, PolkaDated, sent, Spec
<1>2. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ RoundEntryHistory /\ LockWindowCore /\ PrevoteOncePerRound
           /\ PrecommitBacked /\ PrevoteArmedQuorumTimed /\ PrevoteJustified
           /\ RoundVoteAfterEntry /\ [Next]_vars  )
  BY InvProof, LockWindowCoreInv, PrecommitBackedInv,
     PrevoteArmedQuorumTimedInv, PrevoteJustifiedInv, PrevoteOncePerRoundInv,
     PTL, RoundEntryHistoryInv, RoundVoteAfterEntryInv, SentInvInv,
     SentTimeLeNowInv
  DEFS Inv, Spec
<1>3. [](EarlyPolkaNoNil => EarlyPolkaNoNil')
  BY <1>2, EarlyPolkaNoNilStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* The state reading that both the second invariant and its consumer need. A
\* correct validator at r in step "precommit" has precommitted the value of
\* the early polka at r.
LEMMA EarlyPolkaStepPrecommit ==
  ASSUME TypeOK, SentTimeLeNow, PrevoteOncePerRound, PrecommitBacked,
         StepPrecommitHasPrecommit, EarlyPolkaNoNil,
         NEW p \in Honest, NEW r \in Rounds, NEW v \in Values, NEW c \in Honest,
         NEW T \in Nat, RoundOrigin(p, r), Valid(v), Lemma5Timeouts(r),
         T >= GST, T <= enteredAt[p][r], PolkaDated(r, v, T),
         now > enteredAt[p][r] + Delta,
         ~ SomeCorrectDecided, round[c] = r, step[c] = "precommit"
  PROVE  Precommit(c, r, v) \in sent
<1>1. PICK w \in ValuesOrNil : Precommit(c, r, w) \in sent
  BY DEF StepPrecommitHasPrecommit
<1>2. w \in Values
  <2>1. Precommit(c, r, nil) \notin sent
    BY DEF EarlyPolkaNoNil
  <2> QED
    BY <1>1, <2>1 DEF ValuesOrNil
<1>m. Precommit(c, r, w) \in Message
  BY <1>1, HonestSubValidators, MsgPrecommit
<1>t. /\ sentTime[Precommit(c, r, w)] \in Nat
      /\ sentTime[Precommit(c, r, w)] <= sentTime[Precommit(c, r, w)]
  <2>1. sentTime[Precommit(c, r, w)] \in Nat
    BY <1>1, <1>m DEFS OFF, sent, SentTimeLeNow, TypeOK
  <2> QED
    BY <2>1, NatLeReflexive
<1>3. Backing(r, w, sentTime[Precommit(c, r, w)])
  BY <1>1, <1>t DEF PrecommitBacked
<1>4. PolkaDated(r, w, sentTime[Precommit(c, r, w)])
  BY <1>2, <1>3, NilNotInValues DEF Backing
<1>5. w = v
  BY <1>2, <1>4, TwoPolkasAgree DEF ValuesOrNil
<1> QED
  BY <1>1, <1>5

\* The second invariant of Case B, and the first-to-leave argument. A correct
\* validator above r has precommitted the value at r. To leave r needs the
\* precommit timer of r or SkipRound, and neither one moves the clock. The
\* guard therefore held at the departure. There clause 1 excludes a validator
\* below r, and clauses 2 and 5 leave only step "precommit" and step
\* "decided".
EarlyPolkaAbove ==
  \A p \in Honest, r \in Rounds, v \in Values, c \in Honest, T \in Nat :
    ( /\ RoundOrigin(p, r)
      /\ Valid(v)
      /\ T >= GST
      /\ T <= enteredAt[p][r]
      /\ PolkaDated(r, v, T)
      /\ Lemma5Timeouts(r)
      /\ now > enteredAt[p][r] + Delta
      /\ round[c] > r )
    => Precommit(c, r, v) \in sent \/ SomeCorrectDecided

LEMMA EarlyPolkaAboveStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, SentTimeLeNow,
         RoundEntryHistory, LockWindowCore, PrevoteOncePerRound,
         PrecommitBacked, PrevoteJustified, StepPrecommitHasPrecommit,
         RoundVoteAfterEntry, EnteredAtLeNow, EnteredCurrentRound,
         CrossingBacked, EarlyPolkaNoNil, DecidedStepOp, [Next]_vars,
         EarlyPolkaAbove
  PROVE  EarlyPolkaAbove'
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
                    NEW c \in Honest, NEW T \in Nat,
                    RoundOrigin(p, r)', Valid(v), T >= GST,
                    T <= enteredAt'[p][r], PolkaDated(r, v, T)',
                    Lemma5Timeouts(r), now' > enteredAt'[p][r] + Delta,
                    round'[c] > r, ~ SomeCorrectDecided'
             PROVE  Precommit(c, r, v) \in sent'
  BY DEF EarlyPolkaAbove
<1>nd. ~ SomeCorrectDecided
  BY DecidedLatchStep
<1>r0. r > 0
  BY DEF RoundOrigin
<1>ty. /\ now \in Nat /\ now' \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ GST \in Nat /\ r \in Nat /\ T \in Nat /\ round[c] \in Nat
       /\ TimeoutPrecommit(r) \in Nat /\ TimeoutPrecommit(r) > 2 * Delta
  <2>1. TimeoutPrecommit(r) \in Nat
    BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit
  <2> QED
    BY <1>r0, <2>1, DeltaType, GSTType, HonestSubValidators
    DEFS Lemma5Timeouts, Rounds, TypeOK
<1>np. now' <= now + 1
  BY <1>ty, NowShape
<1>a. CASE enteredAt[p][r] = OFF
  <2>1. enteredAt'[p][r] = now
    BY <1>a, EntryUpdateDisciplineStep
    DEFS EntryUpdateDiscipline, OFF, RoundOrigin
  <2> QED
    BY <1>np, <1>ty, <2>1
<1>b. CASE enteredAt[p][r] # OFF
  <2>fr. enteredAt'[p][r] = enteredAt[p][r]
    BY <1>b, EnteredAtFrozenStep
  <2>ro. RoundOrigin(p, r)
    BY <1>b, RoundOriginBack
  <2>ty. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
    BY <2>ro, GSTType DEFS OFF, RoundOrigin, TypeOK
  <2>le. T <= enteredAt[p][r]
    BY <2>fr
  <2>cl. /\ now >= enteredAt[p][r] + Delta
         /\ now > enteredAt[p][r]
    BY <1>np, <1>ty, <2>fr, <2>ty, GuardBack
\* PolkaBack takes the negated form, so it is stated that way. The conversion
\* from now > T needs both sides typed, and a leaf that has to do that as well
\* fails.
  <2>gT. ~ (now <= T)
    BY <1>ty, <2>cl, <2>le, <2>ty
  <2>pk. PolkaDated(r, v, T)
    BY <1>ty, <2>gT, PolkaBack DEF ValuesOrNil
  <2>any. AnyPrevoteDated(r, T)
    BY <2>pk, PolkaIsAnyPrevote DEF ValuesOrNil
  <2>ju. Justified(r, v, T)
    BY <1>ty, <2>pk, JustifiedFromPolka
\* Already above r before the step: the pre-state instance reports the
\* precommit, and the pool only grows.
  <2>1. CASE round[c] > r
    <3>1. CASE now > enteredAt[p][r] + Delta
      <4>1. Precommit(c, r, v) \in sent
        BY <1>nd, <1>ty, <2>1, <2>le, <2>pk, <2>ro, <3>1 DEF EarlyPolkaAbove
      <4> QED
        BY <1>sub, <4>1
\* At the deadline exactly. A validator above r left r. Its departure dates a
\* correct precommit at r a whole precommit timeout earlier, which puts the
\* clock above the deadline after all.
    <3>2. CASE now = enteredAt[p][r] + Delta
      <4>1. PICK h \in Honest, w \in ValuesOrNil :
              /\ Precommit(h, r, w) \in sent
              /\ sentTime[Precommit(h, r, w)] <= now - TimeoutPrecommit(r)
        BY <2>1, AboveNeedsCorrectPrecommit
      <4>2. sentTime[Precommit(h, r, w)] >= enteredAt[p][r]
        BY <2>ro, <4>1, RoundVoteAfterOrigin
      <4>m. Precommit(h, r, w) \in Message
        BY <4>1, HonestSubValidators, MsgPrecommit
      <4>ty. sentTime[Precommit(h, r, w)] \in Int
        BY <4>1, <4>m DEFS OFF, sent, TypeOK
      <4>3. now > enteredAt[p][r] + Delta
        BY <1>ty, <2>ty, <4>1, <4>2, <4>ty, DepartureAboveWindow
      <4> QED
        BY <1>ty, <2>ty, <3>2, <4>3
    <3> QED
      BY <1>ty, <2>cl, <2>ty, <3>1, <3>2
\* The departure step itself. It writes round, so it does not move the clock,
\* and the guard therefore held before it.
  <2>2. CASE round[c] <= r
    <3>1. now' = now
      <4>1. \E q \in Honest : \E rr \in Rounds :
              /\ round' = [round EXCEPT ![q] = rr]
              /\ (  (OnTimeoutPrecommit(q) /\ rr = round[q] + 1)
                    \/ SkipRound(q, rr)  )
        BY <1>ty, <2>2, RoundEnteredStep
      <4> QED
        BY <4>1 DEFS OnTimeoutPrecommit, SkipRound
    <3>gt. now > enteredAt[p][r] + Delta
      BY <2>fr, <3>1
    <3>gp. now > T + Delta
      BY <1>ty, <2>le, <2>ty, <3>gt, WindowAtEntry
    <3>4. step[c] # "decided"
      BY <1>nd, DecidedStepOp DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
\* Clause 1 excludes a validator below r, so the departure is FROM r.
    <3>5. round[c] = r
      <4>1. ~ (round[c] < r)
        BY <1>ty, <2>any, <2>ju, <3>4, <3>gp DEF LockWindowCore
      <4> QED
        BY <1>ty, <2>2, <4>1
    <3>2. step[c] # "propose"
      BY <1>ty, <2>any, <2>ju, <2>pk, <3>5, <3>gp DEF LockWindowCore
    <3>3. step[c] # "prevote"
      BY <1>ty, <2>any, <2>ju, <2>pk, <3>5, <3>gp DEF LockWindowCore
    <3>6. step[c] = "precommit"
      BY <3>2, <3>3, <3>4, HonestSubValidators DEFS Step, TypeOK
    <3>7. Precommit(c, r, v) \in sent
      BY <1>nd, <1>ty, <2>le, <2>pk, <2>ro, <3>5, <3>6, <3>gt,
         EarlyPolkaStepPrecommit
    <3> QED
      BY <1>sub, <3>7
  <2> QED
    BY <1>ty, <2>1, <2>2
<1> QED
  BY <1>a, <1>b

THEOREM EarlyPolkaAboveInv ==
  ASSUME Spec PROVE []EarlyPolkaAbove
<1>1. EarlyPolkaAbove
  BY ByzNonEmpty DEFS EarlyPolkaAbove, Init, OFF, PolkaDated, sent, Spec
<1>2. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ RoundEntryHistory /\ LockWindowCore /\ PrevoteOncePerRound
           /\ PrecommitBacked /\ PrevoteJustified /\ StepPrecommitHasPrecommit
           /\ RoundVoteAfterEntry /\ EnteredAtLeNow /\ EnteredCurrentRound
           /\ CrossingBacked /\ EarlyPolkaNoNil /\ DecidedStepOp
           /\ [Next]_vars  )
  BY CrossingBackedInv, DecidedStepInv, EarlyPolkaNoNilInv, EnteredAtLeNowInv,
     EnteredCurrentRoundInv, InvProof, LockWindowCoreInv, PrecommitBackedInv,
     PrevoteJustifiedInv, PrevoteOncePerRoundInv, PTL, RoundEntryHistoryInv,
     RoundVoteAfterEntryInv, SentInvInv, SentTimeLeNowInv,
     StepPrecommitHasPrecommitInv
  DEFS DecidedStepOp, Inv, Spec
<1>3. [](EarlyPolkaAbove => EarlyPolkaAbove')
  BY <1>2, EarlyPolkaAboveStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* The state argument of Case B. One gossip delay above the entry, three
\* clauses of LockWindowCore leave a correct validator only three positions.
\* They are at r in step "precommit", at r in step "decided", and above r. The
\* decided position is the decision itself. The other two carry a precommit
\* for the value of the polka at r, and the whole correct set is a Byzantine
\* quorum.
LEMMA EarlyPolkaGivesQuorum ==
  ASSUME TypeOK, SentTimeLeNow, LockWindowCore, PrevoteOncePerRound,
         PrecommitBacked, PrevoteJustified, StepPrecommitHasPrecommit,
         DecidedStepOp, EarlyPolkaNoNil, EarlyPolkaAbove,
         NEW p \in Honest, NEW r \in Rounds, NEW v \in Values, NEW T \in Nat,
         RoundOrigin(p, r), Valid(v), Lemma5Timeouts(r),
         T >= GST, T <= enteredAt[p][r], PolkaDated(r, v, T),
         Justified(r, v, T), now > enteredAt[p][r] + Delta,
         ~ SomeCorrectDecided
  PROVE  DecideEvidence(r)
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST /\ r \in Nat
  BY DeltaType, GSTType DEFS OFF, RoundOrigin, Rounds, TypeOK
<1>any. AnyPrevoteDated(r, T)
  BY PolkaIsAnyPrevote DEF ValuesOrNil
<1>gp. now > T + Delta
  BY <1>ty, WindowAtEntry
<1>1. ASSUME NEW c \in Honest
      PROVE  Precommit(c, r, v) \in sent
  <2>sd. step[c] # "decided"
    BY DecidedStepOp DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
  <2>rt. round[c] \in Nat
    BY HonestSubValidators DEFS Rounds, TypeOK
  <2>1. ~ (round[c] < r)
    BY <1>any, <1>gp, <1>ty, <2>sd DEF LockWindowCore
  <2>2. CASE round[c] > r
    BY <2>2 DEF EarlyPolkaAbove
  <2>3. CASE round[c] = r
    <3>1. step[c] # "propose"
      BY <1>any, <1>gp, <1>ty, <2>3 DEF LockWindowCore
    <3>2. step[c] # "prevote"
      BY <1>any, <1>gp, <1>ty, <2>3, PolkaIsAnyPrevote DEF LockWindowCore
    <3>3. step[c] = "precommit"
      BY <2>sd, <3>1, <3>2, HonestSubValidators DEFS Step, TypeOK
    <3> QED
      BY <2>3, <3>3, EarlyPolkaStepPrecommit
  <2> QED
    BY <1>ty, <2>1, <2>2, <2>3, <2>rt
<1>2. \E Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent
  BY <1>1, AllHonestGivesPrecommitQuorum
<1>3. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  BY JustifiedGivesProposal
<1> QED
  BY <1>2, <1>3 DEF DecideEvidence

-----------------------------------------------------------------------------
\* The stage of Case B. The pin is one gossip delay above the entry, which is
\* all that the state argument needs. The region carries no latched fact,
\* because both invariants of Case B are global.
EarlyReach(p, r, b) ==
  /\ EarlyPolka(p, r)
  /\ enteredAt[p][r] + Delta <= b

LEMMA BoxEarlyReachStep ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
              /\ [Next]_vars /\ EarlyReach(p, r, b)
              => EarlyReach(p, r, b)'  )
<1>1. TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory /\ [Next]_vars
      /\ EarlyReach(p, r, b)
        => EarlyReach(p, r, b)'
  <2> SUFFICES ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory,
                      [Next]_vars, EarlyReach(p, r, b)
               PROVE  EarlyReach(p, r, b)'
    OBVIOUS
  <2>d. /\ RoundOrigin(p, r)
        /\ WRDurable(r)
        /\ enteredAt[p][r] + Delta <= b
    BY DEFS CascadeDurable, EarlyPolka, EarlyReach
  <2>1. RoundOrigin(p, r)'
    BY <2>d, RoundOriginStep
  <2>2. WRDurable(r)'
    <3>1. now >= GST /\ (now' = now \/ now' = now + 1)
      BY <2>d, NowShape DEF WRDurable
    <3>2. now' >= GST
      BY <3>1, GSTType, GeAcrossTick DEF TypeOK
    <3> QED
      BY <2>d, <3>2 DEF WRDurable
  <2>3. enteredAt'[p][r] = enteredAt[p][r]
    BY <2>d, EnteredAtFrozenStep DEF RoundOrigin
  <2>4. PICK v \in Values, T \in Nat :
          /\ Valid(v)
          /\ T >= GST
          /\ T <= enteredAt[p][r]
          /\ PolkaDated(r, v, T)
          /\ Justified(r, v, T)
    BY DEFS EarlyPolka, EarlyReach
  <2>5. PolkaDated(r, v, T)' /\ Justified(r, v, T)'
    BY <2>4, JustifiedMove, PolkaMove DEF ValuesOrNil
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5
    DEFS CascadeDurable, EarlyPolka, EarlyReach
<1> QED
  BY <1>1, PTL

LEMMA BoxQuorumFromEarlyReach ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ SentTimeLeNow /\ LockWindowCore /\ PrevoteOncePerRound
              /\ PrecommitBacked /\ PrevoteJustified
              /\ StepPrecommitHasPrecommit /\ DecidedStepOp
              /\ EarlyPolkaNoNil /\ EarlyPolkaAbove /\ ~SomeCorrectDecided
              /\ EarlyReach(p, r, b) /\ now > b
              => DecideEvidence(r)  )
<1>1. TypeOK /\ SentTimeLeNow /\ LockWindowCore /\ PrevoteOncePerRound
      /\ PrecommitBacked /\ PrevoteJustified /\ StepPrecommitHasPrecommit
      /\ DecidedStepOp /\ EarlyPolkaNoNil /\ EarlyPolkaAbove
      /\ ~SomeCorrectDecided /\ EarlyReach(p, r, b) /\ now > b
        => DecideEvidence(r)
  <2> SUFFICES ASSUME TypeOK, SentTimeLeNow, LockWindowCore,
                      PrevoteOncePerRound, PrecommitBacked, PrevoteJustified,
                      StepPrecommitHasPrecommit, DecidedStepOp,
                      EarlyPolkaNoNil, EarlyPolkaAbove, ~SomeCorrectDecided,
                      EarlyReach(p, r, b), now > b
               PROVE  DecideEvidence(r)
    OBVIOUS
  <2>d. /\ RoundOrigin(p, r)
        /\ Lemma5Timeouts(r)
        /\ enteredAt[p][r] + Delta <= b
    BY DEFS CascadeDurable, EarlyPolka, EarlyReach, Lemma5Timeouts, WRDurable
  <2>1. PICK v \in Values, T \in Nat :
          /\ Valid(v)
          /\ T >= GST
          /\ T <= enteredAt[p][r]
          /\ PolkaDated(r, v, T)
          /\ Justified(r, v, T)
    BY DEFS EarlyPolka, EarlyReach
  <2>ty. /\ now \in Nat /\ Delta \in Nat /\ enteredAt[p][r] \in Nat
    BY <2>d, DeltaType DEFS OFF, RoundOrigin, TypeOK
  <2>gt. now > enteredAt[p][r] + Delta
    BY <2>d, <2>ty, GtFromPinned
  <2> QED
    BY <2>1, <2>d, <2>gt, EarlyPolkaGivesQuorum
<1> QED
  BY <1>1, PTL

THEOREM EarlyQuorumReachedAt ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided,
         NEW b \in Nat
  PROVE  EarlyReach(p, r, b) ~> DecideEvidence(r)
<1>cu. <>[](now > b)
  BY ClockUnbounded
<1>nd. []~SomeCorrectDecided
  OBVIOUS
<1>ds. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>inv. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
             /\ RoundEntryHistory /\ LockWindowCore /\ PrevoteOncePerRound
             /\ PrecommitBacked /\ PrevoteJustified
             /\ StepPrecommitHasPrecommit /\ EarlyPolkaNoNil
             /\ EarlyPolkaAbove /\ [Next]_vars  )
  BY EarlyPolkaAboveInv, EarlyPolkaNoNilInv, InvProof, LockWindowCoreInv,
     PrecommitBackedInv, PrevoteJustifiedInv, PrevoteOncePerRoundInv, PTL,
     RoundEntryHistoryInv, SentInvInv, SentTimeLeNowInv,
     StepPrecommitHasPrecommitInv
  DEFS Inv, Spec
<1>la. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
            /\ [Next]_vars /\ EarlyReach(p, r, b)
            => EarlyReach(p, r, b)'  )
  BY BoxEarlyReachStep
<1>go. [](  TypeOK /\ SentTimeLeNow /\ LockWindowCore /\ PrevoteOncePerRound
            /\ PrecommitBacked /\ PrevoteJustified
            /\ StepPrecommitHasPrecommit /\ DecidedStepOp
            /\ EarlyPolkaNoNil /\ EarlyPolkaAbove /\ ~SomeCorrectDecided
            /\ EarlyReach(p, r, b) /\ now > b
            => DecideEvidence(r)  )
  BY BoxQuorumFromEarlyReach
<1> QED
  BY <1>cu, <1>nd, <1>ds, <1>inv, <1>la, <1>go, PTL

LEMMA EarlyReachCommute ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW TEMPORAL D,
         \A b \in Nat : [](EarlyReach(p, r, b) => D)
  PROVE  [](\A b \in Nat : (EarlyReach(p, r, b) => D))
OBVIOUS

LEMMA EarlyReachBoxFO ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  (\A b \in Nat : (EarlyReach(p, r, b) => <>DecideEvidence(r)))
              => ((\E b \in Nat : EarlyReach(p, r, b))
                    => <>DecideEvidence(r))  )
<1>1. (\A b \in Nat : (EarlyReach(p, r, b) => <>DecideEvidence(r)))
      => ((\E b \in Nat : EarlyReach(p, r, b)) => <>DecideEvidence(r))
  OBVIOUS
<1> QED
  BY <1>1, PTL

LEMMA BoxEarlyReachFromPolka ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ EarlyPolka(p, r)
              => (\E b \in Nat : EarlyReach(p, r, b))  )
<1>1. TypeOK /\ EarlyPolka(p, r) => (\E b \in Nat : EarlyReach(p, r, b))
  <2> SUFFICES ASSUME TypeOK, EarlyPolka(p, r)
               PROVE  \E b \in Nat : EarlyReach(p, r, b)
    OBVIOUS
  <2>d. RoundOrigin(p, r)
    BY DEFS CascadeDurable, EarlyPolka
  <2>ty. enteredAt[p][r] \in Nat /\ Delta \in Nat
    BY <2>d, DeltaType DEFS OFF, RoundOrigin, TypeOK
  <2>1. /\ enteredAt[p][r] + Delta \in Nat
        /\ enteredAt[p][r] + Delta <= enteredAt[p][r] + Delta
    BY <2>ty, NatLeReflexive
  <2> QED
    BY <2>1 DEF EarlyReach
<1> QED
  BY <1>1, PTL

THEOREM EarlyQuorumReached ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided
  PROVE  EarlyPolka(p, r) ~> DecideEvidence(r)
<1>1. \A b \in Nat : [](EarlyReach(p, r, b) => <>DecideEvidence(r))
  <2> SUFFICES ASSUME NEW b \in Nat
               PROVE  [](EarlyReach(p, r, b) => <>DecideEvidence(r))
    OBVIOUS
  <2>1. EarlyReach(p, r, b) ~> DecideEvidence(r)
    BY EarlyQuorumReachedAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A b \in Nat : (EarlyReach(p, r, b) => <>DecideEvidence(r)))
  BY <1>1, EarlyReachCommute
<1>3. (\E b \in Nat : EarlyReach(p, r, b)) ~> DecideEvidence(r)
  BY <1>2, EarlyReachBoxFO, PTL
<1>4. [](TypeOK /\ EarlyPolka(p, r) => (\E b \in Nat : EarlyReach(p, r, b)))
  BY BoxEarlyReachFromPolka
<1>ty. []TypeOK
  BY InvProof, PTL DEFS Inv, Spec
<1> QED
  BY <1>3, <1>4, <1>ty, PTL
-----------------------------------------------------------------------------
\* Both outcome operators are DEFINITIONS, and no backend unfolds a
\* definition under [], so each is exposed to PTL through a clean boxed
\* identity. The assembly below cites the first one, so it sits above it.
LEMMA BlockingOutcomeBox ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](Lemma5BlockingOutcome(p, r)
              <=> (SomeCorrectDecided \/ BlockingLockDuring(p, r)))
<1>1. Lemma5BlockingOutcome(p, r)
        <=> (SomeCorrectDecided \/ BlockingLockDuring(p, r))
  BY DEF Lemma5BlockingOutcome
<1> QED
  BY <1>1, PTL

\* The decision latch, boxed in a context that is free of Spec. Necessitation
\* is refused while Spec is an assumed hypothesis. Spec therefore stands on
\* the LEFT of the implication here, and in every leg of the assembly below.
LEMMA DecidedLatchBox ==
  Spec => [](SomeCorrectDecided => []SomeCorrectDecided)
<1>1. [](TypeOK /\ [Next]_vars) => [](SomeCorrectDecided => SomeCorrectDecided')
  <2>1. TypeOK /\ [Next]_vars /\ SomeCorrectDecided => SomeCorrectDecided'
    BY DecidedLatchStep
  <2> QED
    BY <2>1, PTL
<1>2. Spec => [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEFS Inv, Spec
<1> QED
  BY <1>1, <1>2, PTL

\*  The cascade itself, on a run where no correct validator has decided. The
\*  hypotheses are at THEOREM level on purpose. A temporal ASSUME at step
\*  level does not reach the obligations of its children. Every citation of a
\*  stage would therefore lose the no-decision hypothesis that the stage
\*  needs.
THEOREM Lemma5CascadeUnderNoDecision ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec, []~SomeCorrectDecided
  PROVE  Lemma5Hyp(p, r) ~> Lemma5BlockingOutcome(p, r)
<1>nd. []~SomeCorrectDecided
  OBVIOUS
<1>bo. [](  Lemma5BlockingOutcome(p, r)
            <=> (SomeCorrectDecided \/ BlockingLockDuring(p, r))  )
  BY BlockingOutcomeBox
\* Item 6 splits the hypothesis state. Case A transfers clause (3) of
\* Lemma5Hyp to the validRound of the round-r proposal. Case B already carries
\* a round-r polka, dated at the entry of p.
<1>inv. [](  TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow
             /\ HonestProposalUnique /\ ProposalValidRoundGap
             /\ ProposalJustified /\ ValidBelowRound /\ ValidPrevoteBacked
             /\ ValidValueFromProposal  )
  BY HonestProposalUniqueInv, InvProof, ProposalJustifiedInv,
     ProposalValidRoundGapInv, PTL, SentTimeLeNowInv, ValidBelowRoundInv,
     ValidPrevoteBackedInv, ValidValueFromProposalInv
  DEFS Inv, Spec
<1>sp. [](  TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow
            /\ HonestProposalUnique /\ ProposalValidRoundGap
            /\ ProposalJustified /\ ValidBelowRound /\ ValidPrevoteBacked
            /\ ValidValueFromProposal /\ Lemma5Hyp(p, r)
            => (CaseA(p, r) \/ EarlyPolka(p, r))  )
  BY Lemma5HypSplitBox
<1>split. [](Lemma5Hyp(p, r) => CaseA(p, r) \/ EarlyPolka(p, r))
  BY <1>inv, <1>sp, PTL
\* CASE A. Item 10 reaches the proposal milestone, and the three latches hand
\* their region facts to that state, where item 14 runs the cascade.
<1>pm. Lemma5Hyp(p, r) ~> ProposalMilestone(p, r)
  BY ProposalReached
<1>ld. [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []LocksDominateOrDated(p, r))
  BY LocksDominateLatch
<1>np. [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []NilPrevoteBlocks(p, r))
  BY NilPrevoteBlocksLatch
<1>cc. [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []CascadeCore(p, r))
  BY CascadeCoreLatch
<1>qr. (  ProposalMilestone(p, r) /\ LocksDominateOrDated(p, r)
          /\ NilPrevoteBlocks(p, r) /\ CascadeCore(p, r)  )
         ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
  BY QuorumReached
<1>A. (Lemma5Hyp(p, r) /\ CaseA(p, r))
        ~> (DecideEvidence(r) \/ BlockingLockDuring(p, r))
  BY <1>cc, <1>ld, <1>np, <1>pm, <1>qr, PTL
\* CASE B. The early polka needs no region conjunct and no latch: both of its
\* invariants are global.
<1>B. EarlyPolka(p, r) ~> DecideEvidence(r)
  BY EarlyQuorumReached
\* Both legs end at the decide evidence, and one WF1 stage turns that into the
\* decision of a correct validator.
<1>dec. DecideEvidence(r) ~> SomeCorrectDecided
  BY QuorumDecides
<1> QED
  BY <1>A, <1>B, <1>bo, <1>dec, <1>split, PTL

\*  The interface theorem. This is paper Lemma 5, repaired. A correct
\*  validator decides, or a correct validator holds a lock that blocks round
\*  r. That lock was taken no earlier than the entry of p.
\*
\* The lock branch is the RELATIVIZED one. That is not extra content: the
\* cascade fails only if some correct validator refuses the proposal, and the
\* accept guard of OnProposalWithPOL,
\*   locked[c].round <= vr \/ locked[c].value = v,
\* negated IS the `vr < lr` and `w # v` pair of BlockingLockDuring, so the
\* strengthening follows the algorithm's own guard. `lr < r` holds because round
\* r carries only one proposal, so no competing polka can form at r itself.
\* TendermintPartialSyncTerminationLockRetry consumes this theorem and closes the
\* retry from it.
THEOREM Lemma5OrBlockingLock ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  Spec => (Lemma5Hyp(p, r) ~> Lemma5BlockingOutcome(p, r))
<1>bo. [](  Lemma5BlockingOutcome(p, r)
            <=> (SomeCorrectDecided \/ BlockingLockDuring(p, r))  )
  BY BlockingOutcomeBox
<1>lat. Spec => [](SomeCorrectDecided => []SomeCorrectDecided)
  BY DecidedLatchBox
<1>main. Spec /\ []~SomeCorrectDecided
           => (Lemma5Hyp(p, r) ~> Lemma5BlockingOutcome(p, r))
  BY Lemma5CascadeUnderNoDecision
<1> QED
  BY <1>bo, <1>lat, <1>main, PTL

-----------------------------------------------------------------------------
\* The published outcome, exposed to PTL through a boxed identity.
LEMMA Lemma5OutcomeBox ==
  ASSUME NEW r \in Rounds
  PROVE  [](Lemma5Outcome(r) <=> (SomeCorrectDecided \/ PostGSTPriorRoundLock(r)))
<1>1. Lemma5Outcome(r) <=> (SomeCorrectDecided \/ PostGSTPriorRoundLock(r))
  BY DEF Lemma5Outcome
<1> QED
  BY <1>1, PTL

\*  The reduction of the relativized branch to the published one. A blocking
\*  lock IS a correct lock below r after GST. It was sent no earlier than an
\*  entry instant, and that instant is itself after GST.
LEMMA BlockingImpliesPriorLockBox ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](TypeOK /\ RoundOrigin(p, r) /\ BlockingLockDuring(p, r)
              => PostGSTPriorRoundLock(r))
<1>1. TypeOK /\ RoundOrigin(p, r) /\ BlockingLockDuring(p, r)
        => PostGSTPriorRoundLock(r)
  <2> SUFFICES ASSUME TypeOK, RoundOrigin(p, r), BlockingLockDuring(p, r)
               PROVE  PostGSTPriorRoundLock(r)
    OBVIOUS
  <2>1. PICK v \in Values, w \in Values, vr \in Rounds \cup {-1}, c \in Honest, lr \in Rounds :
          /\ Proposal(Proposer[r], r, v, vr) \in sent
          /\ vr < lr
          /\ lr < r
          /\ w # v
          /\ VotedPrecommit(c, w, lr)
          /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]
    BY DEF BlockingLockDuring
  <2>m. Precommit(c, lr, w) \in Message
    BY <2>1 DEF VotedPrecommit, sent
  <2>t. sentTime[Precommit(c, lr, w)] \in Nat \cup {OFF}
    BY <2>m DEF TypeOK
  <2>e. enteredAt[p][r] \in Nat
    BY DEFS OFF, RoundOrigin, TypeOK
  <2>g. enteredAt[p][r] > GST
    BY DEF RoundOrigin
  <2>3. sentTime[Precommit(c, lr, w)] > GST
    BY <2>1, <2>t, <2>e, <2>g, GSTType DEF OFF
  <2> QED
    BY <2>1, <2>3 DEF PostGSTPriorRoundLock
<1> QED
  BY <1>1, PTL

\* Corollary, NOT an admission. The published interface still holds, so
\* everything downstream of it (Lemma5Reach, Lemma5ResolutionExists, the
\* composition's RecurringResolution, ...WithinRoundMC's
\* MCPostGSTPriorRoundLock scripts) keeps working unchanged.
THEOREM Lemma5OrPriorLock ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  Spec => (Lemma5Hyp(p, r) ~> Lemma5Outcome(r))
<1> SUFFICES ASSUME Spec PROVE Lemma5Hyp(p, r) ~> Lemma5Outcome(r)
  OBVIOUS
<1>ty. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
\* The citation is at IDENTITY, the only shape a ~> conclusion supports.
<1>hb. Lemma5Hyp(p, r) ~> Lemma5BlockingOutcome(p, r)
  BY Lemma5OrBlockingLock
<1>ob. [](Lemma5BlockingOutcome(p, r)
            <=> (SomeCorrectDecided \/ BlockingLockDuring(p, r)))
  BY BlockingOutcomeBox
<1>ou. [](Lemma5Outcome(r) <=> (SomeCorrectDecided \/ PostGSTPriorRoundLock(r)))
  BY Lemma5OutcomeBox
\* The hypothesis state fixes the entry instant, and the entry instant is
\* frozen from there on. The reduction therefore applies at the LATER state
\* where the blocking lock appears.
<1>ro. [](TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r))
  BY Lemma5HypRoundOriginBox
<1>st. [](RoundOrigin(p, r) => []RoundOrigin(p, r))
  BY RoundOriginStable
<1>bl. [](TypeOK /\ RoundOrigin(p, r) /\ BlockingLockDuring(p, r)
            => PostGSTPriorRoundLock(r))
  BY BlockingImpliesPriorLockBox
<1> QED
  BY <1>ty, <1>hb, <1>ob, <1>ou, <1>ro, <1>st, <1>bl, PTL
-----------------------------------------------------------------------------
LEMMA Lemma5ReachRule ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  Spec => Lemma5Reach(p, r)
BY Lemma5OrPriorLock DEF Lemma5Reach

\* Existential leads-to through the checked forall/box commute. The temporal
\* consequent is abstracted so the first-order backend never inspects <>.
LEMMA Lemma5Commute ==
  ASSUME NEW TEMPORAL D,
         \A p \in Honest : \A r \in Rounds : [](Lemma5Hyp(p, r) => D)
  PROVE  [](\A p \in Honest : \A r \in Rounds : (Lemma5Hyp(p, r) => D))
OBVIOUS

LEMMA Lemma5ResolutionBox ==
  [](  (\A p \in Honest : \A r \in Rounds :
          (Lemma5Hyp(p, r) => <>Lemma5Outcome(r)))
       => (GoodRoundExists => <>GoodRoundResolution)  )
<1>1. (\A p \in Honest : \A r \in Rounds :
          (Lemma5Hyp(p, r) => <>Lemma5Outcome(r)))
       => (GoodRoundExists => <>GoodRoundResolution)
  BY DEF GoodRoundExists, Lemma5Outcome, GoodRoundResolution
<1> QED
  BY <1>1, PTL

LEMMA Lemma5ResolutionFromAll ==
  ASSUME \A p \in Honest : \A r \in Rounds :
           (Lemma5Hyp(p, r) ~> Lemma5Outcome(r))
  PROVE  GoodRoundExists ~> GoodRoundResolution
<1>0. \A p \in Honest : \A r \in Rounds :
        [](Lemma5Hyp(p, r) => <>Lemma5Outcome(r))
  BY PTL
<1>1. [](\A p \in Honest : \A r \in Rounds :
           (Lemma5Hyp(p, r) => <>Lemma5Outcome(r)))
  BY <1>0, Lemma5Commute
<1>2. [](  (\A p \in Honest : \A r \in Rounds :
              (Lemma5Hyp(p, r) => <>Lemma5Outcome(r)))
           => (GoodRoundExists => <>GoodRoundResolution)  )
  BY Lemma5ResolutionBox
<1> QED
  BY <1>1, <1>2, PTL

THEOREM Lemma5ResolutionExists ==
  ASSUME Spec PROVE GoodRoundExists ~> GoodRoundResolution
BY Lemma5ResolutionFromAll, Lemma5ReachRule DEF Lemma5Reach
=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)