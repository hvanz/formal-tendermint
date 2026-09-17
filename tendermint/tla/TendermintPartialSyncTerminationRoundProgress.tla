------------ MODULE TendermintPartialSyncTerminationRoundProgress --------------
(***************************************************************************)
(* Post-GST round progress: the composition module's ProgressBeyond.       *)
(*                                                                         *)
(*  This module owns the clock-and-round frontier of paper Lemma 7. It     *)
(*  EXTENDS TendermintPartialSyncTerminationNonZeno (hence ...Base), which    *)
(*  brings the non-Zeno burst core into this branch. The composition       *)
(*  module EXTENDS this module, so ProgressBeyond and PostGSTRoundProgress *)
(*  stay in scope by name there.                                           *)
(*                                                                         *)
(*  THE REDUCTION (Layer 0, checked). ProgressBeyond asks for a state with *)
(*  now > GST AND a correct round above a bound. RoundBelowNowInv already  *)
(*  gives round[c] <= now, so a SINGLE instant with round[c] > b + GST     *)
(*  satisfies both conjuncts at once. The clock is therefore free: the     *)
(*  whole content is unbounded round growth (RoundGrowth), proved in Layer *)
(*  4 below. Base's Mreach / ReachExistsLT staircase is NOT on this route. *)
(*  The clock only has to advance far enough to fire the individual        *)
(*  timers, and that happens inside the round argument.                    *)
(*                                                                         *)
(*   ROUND GROWTH is a bounded-work region argument. Once the rounds are   *)
(*   bounded, the measure StepWork + BurstBottom + a round deficit is a    *)
(*   Nat with a CONSTANT bound. Only the RoundGap of ...Base mentions the  *)
(*   clock, through RoundCeiling. Deliver, FaultyStep and Tick leave the   *)
(*   measure unchanged, and every honest step strictly decreases it. Only  *)
(*   finitely many honest steps can therefore happen while the rounds stay *)
(*   bounded. The proof reduces to exhibiting one CONTINUOUSLY enabled     *)
(*   honest action in the region. The thirteen Enabled* lemmas and the     *)
(*   G*NetworkStable lemmas of ...NonZeno supply that action.              *)
(*                                                                         *)
(* Layers 1 to 4 below are the ingredients of that argument, and all of    *)
(* them are proved here.                                                   *)
(*   Layer 1  PrecommitArmedQuorum, RoundBacked, PrevoteSelfEvidence.      *)
(*   Layer 2  the no-deadlock lemma. Quiescence with nothing pending and   *)
(*            no live timer forces a correct decision.                     *)
(*   Layer 3  the Work(b) measure and the RoundGrowth staircase.           *)
(*   Layer 4  HonestStepsRecur, that honest steps keep happening while no  *)
(*            correct validator has decided.                               *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationNonZeno, TLAPS

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 0: the reduction of ProgressBeyond to round growth.               *)
(***************************************************************************)

\* Some correct validator is beyond round b.
RoundAbove(b) == \E c \in Honest : round[c] > b

\* Some correct validator is beyond BOTH round b and round GST. The round
\* bound GST is what makes the clock conjunct of ProgressBeyond free:
\* round[c] > GST plus round[c] <= now (RoundBelowNowInv) gives now > GST.
RoundAbovePastGST(b) == \E c \in Honest : round[c] > b /\ round[c] > GST

ProgressBeyond ==
  \A b \in Rounds : (<>SomeCorrectDecided \/ <>(now > GST /\ RoundAbove(b)))

\*  ---- Round growth, and why the GST threshold is in its STATEMENT ---------
\*  RoundGrowth (proved from HonestStepsRecur at the end of this module) says
\*  that for EVERY bound, some correct validator eventually passes it AND
\*  passes GST. That is the same claim at the larger bound b + GST.
\*
\* The threshold is folded in on purpose, so PostGSTRoundProgress can cite
\* RoundGrowth by IDENTITY instantiation. Citing it at a SUBSTITUTED bound
\* (b := b + GST) does NOT work: after coalescing, <>RoundAbove(b) is an
\* opaque atom, so no backend can instantiate the implicit \A b of the
\* ASSUME. Paying the shift inside RoundGrowth costs one operator (Bnd);
\* paying it at the interface is a wall.

\*  A clean state bridge, free of Spec, in atoms that are named operators, so
\*  that PTL can match it against the <> above. Above b and above GST is above
\*  b AND past GST.
LEMMA BoxRoundAboveGST ==
  ASSUME NEW b \in Rounds
  PROVE  [](  TypeOK /\ RoundBelowNow /\ RoundAbovePastGST(b)
              => (now > GST /\ RoundAbove(b))  )
<1>1. TypeOK /\ RoundBelowNow /\ RoundAbovePastGST(b) => (now > GST /\ RoundAbove(b))
  BY GSTType DEFS RoundAbove, RoundAbovePastGST, RoundBelowNow, Rounds, TypeOK
<1> QED
  BY <1>1, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 1: three inductive invariants.                                    *)
(*                                                                         *)
(* These are the state facts that make a LAGGING correct validator         *)
(* provably unstuck, which is what the region argument needs at its        *)
(* bottom.                                                                 *)
(***************************************************************************)

\* ---- Invariant 1: an armed precommit timer certifies a quorum ------------
\* ScheduleTimeoutPrecommit is the only writer that turns the precommit timer
\* on, and its guard is exactly this quorum at the current round. Every round
\* change resets the timer to OFF (ResetTimersFor), so the certificate can
\* never outlive the round it was earned in, and rcvd only grows.
PrecommitArmedQuorum ==
  \A c \in Honest :
    timer[c]["precommit"] # OFF => RExistsAnyPrecommitQuorum(c, round[c])

LEMMA PrecommitArmedQuorumStepL ==
  ASSUME TypeOK, [Next]_vars, PrecommitArmedQuorum
  PROVE  PrecommitArmedQuorum'
BY RcvdMonotoneStep
DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrecommitArmedQuorum, Propose, ResetTimersFor, RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TimerType, TypeOK, vars

THEOREM PrecommitArmedQuorumInv == ASSUME Spec PROVE []PrecommitArmedQuorum
<1>1. PrecommitArmedQuorum
  BY DEFS Init, PrecommitArmedQuorum, Spec, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](PrecommitArmedQuorum => PrecommitArmedQuorum')
  BY <1>2, PrecommitArmedQuorumStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- Invariant 2: a validator only leaves a round it can certify --------
\*  A 2f+1 precommit quorum for round r sits in the GLOBAL pool once any
\*  correct validator has passed round r. This is the fact that frees a
\*  correct validator that lags. The certificate is in `sent`, so fair
\*  delivery hands it to that validator, which then arms its own precommit
\*  timer.
PrecommitQuorumInSent(r) ==
  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil : Precommit(s, r, v) \in sent

RoundBacked ==
  \A c \in Honest : \A r \in Rounds : r < round[c] => PrecommitQuorumInSent(r)

\* Any received precommit is a genuine global-pool Precommit message. Value-free
\* sibling of Base's PrecommitSenderVoted (which pins the value).
LEMMA AnyPrecommitSenderVoted ==
  ASSUME TypeOK, NEW c \in Honest, rcvd[c] \subseteq sent,
         NEW rr \in Rounds, NEW s, s \in RSendersOfTypeAtRound(c, "Precommit", rr)
  PROVE  \E v \in ValuesOrNil : Precommit(s, rr, v) \in sent
BY DEFS Message, Precommit, PrecommitMsg, PrevoteMsg, ProposalMsg,
   RSendersOfTypeAtRound, sent, TypeOK, ValuesOrNil

\* An armed precommit timer turns into a global-pool certificate.
LEMMA ArmedPrecommitCertifies ==
  ASSUME TypeOK, RcvdSubsetSent, NEW c \in Honest,
         RExistsAnyPrecommitQuorum(c, round[c])
  PROVE  PrecommitQuorumInSent(round[c])
BY AnyPrecommitSenderVoted DEFS PrecommitQuorumInSent, RcvdSubsetSent, RExistsAnyPrecommitQuorum, TypeOK

\* A weak quorum of round-r senders contains an honest validator that has
\* itself reached round r (SentInv bounds an honest sender's rounds by its own).
LEMMA SkipEvidenceHonestRound ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, NEW p \in Honest, NEW r \in Rounds,
         \E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, r)
  PROVE  \E h \in Honest : r <= round[h]
BY WeakQuorumHasHonest DEFS HonestSentOK, RcvdSubsetSent, RSendersOfAnyMessageAt, RSendersOfTypeAtRound, SentInv

LEMMA RoundBackedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         PrecommitArmedQuorum, RoundBacked
  PROVE  RoundBacked'
<1> SUFFICES ASSUME NEW c \in Honest, NEW r \in Rounds, r < round'[c]
             PROVE  (PrecommitQuorumInSent(r))'
  BY DEF RoundBacked
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>keep. ASSUME PrecommitQuorumInSent(r)
         PROVE  (PrecommitQuorumInSent(r))'
  BY <1>mono, <1>keep DEF PrecommitQuorumInSent
<1>ty. \A q \in Honest : round[q] \in Nat
  BY DEFS Rounds, TypeOK
<1>rn. r \in Nat
  BY DEF Rounds
<1>1. CASE \E p \in Honest : OnTimeoutPrecommit(p)
  BY <1>1, <1>keep, <1>rn, <1>ty, ArmedPrecommitCertifies
  DEFS OnTimeoutPrecommit, PrecommitArmedQuorum, RoundBacked, TypeOK
<1>2. CASE \E p \in Honest : \E rr \in Rounds : SkipRound(p, rr)
  BY <1>2, <1>keep, <1>rn, <1>ty, SkipEvidenceHonestRound DEFS RoundBacked, Rounds, SkipRound, TypeOK
<1>3. CASE /\ ~(\E p \in Honest : OnTimeoutPrecommit(p))
           /\ ~(\E p \in Honest : \E rr \in Rounds : SkipRound(p, rr))
  BY <1>3, <1>keep DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep,
    Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
    OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrevote,
    OnTimeoutPropose, Propose, RoundBacked, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM RoundBackedInv == ASSUME Spec PROVE []RoundBacked
<1>1. RoundBacked
  BY DEFS Init, RoundBacked, Rounds, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ PrecommitArmedQuorum /\ [Next]_vars)
  BY InvProof, PrecommitArmedQuorumInv, SentInvInv, PTL DEF Spec, Inv
<1>3. [](RoundBacked => RoundBacked')
  BY <1>2, RoundBackedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- Invariant 3: a prevote/precommit validator has prevoted ------------
\*  Base's SelfVoteEvidenceOp gives a prevote validator its own prevote and a
\*  precommit validator its own precommit. The all-rounds-equal branch of the
\*  no-deadlock lemma needs the PREVOTE of a PRECOMMIT validator too. Every
\*  path into "precommit" at r runs through "prevote" at r, and that step
\*  broadcast a prevote at r and self-delivered it.
PrevoteSelfEvidence ==
  \A c \in Honest : step[c] \in {"prevote", "precommit"} =>
    \E m \in rcvd[c] : m.type = "Prevote" /\ m.sender = c /\ m.round = round[c]

LEMMA PrevoteSelfEvidenceStepL ==
  ASSUME TypeOK, [Next]_vars, PrevoteSelfEvidence
  PROVE  PrevoteSelfEvidence'
BY RcvdMonotoneStep DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep,
  Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
  OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
  OnTimeoutPrevote, OnTimeoutPropose, Prevote, PrevoteSelfEvidence, Propose,
  ResetTimersFor, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

THEOREM PrevoteSelfEvidenceInv == ASSUME Spec PROVE []PrevoteSelfEvidence
<1>1. PrevoteSelfEvidence
  BY DEFS Init, PrevoteSelfEvidence, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](PrevoteSelfEvidence => PrevoteSelfEvidence')
  BY <1>2, PrevoteSelfEvidenceStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 2: the system cannot stop.                                        *)
(*                                                                         *)
(*  Tick is the only action that moves the clock, and it needs TickUseful. *)
(*  The whole system can therefore come to rest in ONE way only. That way  *)
(*  is quiescence, where no correct validator can compute, together with   *)
(*  ~TickUseful, where nothing is in flight and no timer is live. That     *)
(*  state forces a correct decision, which is how the region argument for  *)
(*  RoundGrowth reaches its conclusion.                                    *)
(*                                                                         *)
(* With every correct validator undecided:                                 *)
(* - Nobody is in step "propose". The propose timer is armed, by           *)
(*   ProposeTimerArmedOp, and it is live. ~TickUseful therefore forces now *)
(*   >= that deadline, and OnTimeoutPropose is then enabled. That          *)
(*   contradicts quiescence.                                               *)
(* - The precommit timer is OFF everywhere, and the prevote timer of a     *)
(*   prevote validator is OFF. The same argument on their own timeouts     *)
(*   gives both.                                                           *)
(* - Nothing is in flight, so every correct validator holds the whole      *)
(*   global pool.                                                          *)
(* - If the correct rounds are NOT all equal, the validator with the       *)
(*   minimum round sits strictly below another one. RoundBacked then puts  *)
(*   a precommit certificate for ITS OWN round in the pool. That validator *)
(*   holds the certificate, so ScheduleTimeoutPrecommit is enabled.        *)
(* - If the correct rounds are all equal, every correct validator has      *)
(*   prevoted at the common round, by PrevoteSelfEvidence. A prevote       *)
(*   validator therefore holds an any-value prevote quorum, which is the   *)
(*   all-honest quorum of QuorumAvailable, and ScheduleTimeoutPrevote is   *)
(*   enabled. In every other case everyone is in step "precommit". The     *)
(*   same counting on their own precommits, by SelfVoteEvidenceOp, then    *)
(*   enables ScheduleTimeoutPrecommit.                                     *)
(***************************************************************************)

\* Nothing in flight: every correct validator holds the whole global pool.
AllDelivered == \A c \in Honest : sent \subseteq rcvd[c]

\* Minimum correct round. FiniteSetTheorems has no extremum theorem, so this
\* is an FS_Induction over the subsets of Honest (mirror of the composition
\* module's MaxLockedRound).
LEMMA MinRoundExists ==
  ASSUME TypeOK
  PROVE  \E p \in Honest : \A q \in Honest : round[p] <= round[q]
<1> DEFINE P(S) == S # {} => \E p \in S : \A q \in S : round[p] <= round[q]
<1>int. \A q \in Honest : round[q] \in Int
  BY DEFS Rounds, TypeOK
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T \in SUBSET Honest, IsFiniteSet(T), P(T), NEW x \in Honest \ T
      PROVE  P(T \cup {x})
  BY <1>2, <1>int
<1>3. P(Honest)
  <2> HIDE DEF P
  <2> QED
    BY <1>1, <1>2, HonestFinite, FS_Induction, IsaM("blast")
<1> QED
  BY <1>3, HonestNonEmptyL DEF P

\* Anything the WHOLE correct set has sent at round r is an any-value quorum
\* in every correct validator's own view, once nothing is in flight. The
\* witness is QuorumAvailable's all-honest 2f+1 quorum.
LEMMA AllHonestVotesGiveQuorum ==
  ASSUME TypeOK, AllDelivered, NEW t, NEW r, NEW c \in Honest,
         \A q \in Honest : \E m \in sent :
           m.type = t /\ m.sender = q /\ m.round = r
  PROVE  \E Q \in ByzQuorum : Q \subseteq RSendersOfTypeAtRound(c, t, r)
BY QuorumAvailable DEFS AllDelivered, RSendersOfTypeAtRound

\* A global-pool precommit certificate for r is an any-value precommit quorum
\* in every correct validator's own view, once nothing is in flight.
LEMMA CertInSentGivesQuorum ==
  ASSUME TypeOK, AllDelivered, NEW c \in Honest, NEW r,
         PrecommitQuorumInSent(r)
  PROVE  RExistsAnyPrecommitQuorum(c, r)
BY DEFS AllDelivered, Precommit, PrecommitQuorumInSent, RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound

LEMMA QuiescentDeadlockDecides ==
  ASSUME TypeOK, RcvdSubsetSent,
         ProposeTimerArmedOp, DecidedStepOp, SelfVoteEvidenceOp,
         PrevoteSelfEvidence, RoundBacked,
         HonestQuiescent, ~TickUseful
  PROVE  SomeCorrectDecided
<1> SUFFICES ASSUME \A c \in Honest : ~HasDecided(c)
             PROVE  FALSE
  BY DEF SomeCorrectDecided
<1>nd. \A q \in Honest : decision[q] = nil /\ step[q] # "decided"
  BY DEFS DecidedStepOp, HasDecided
<1>nq. \A q \in Honest : ~ CanCompute(q)
  BY DEF HonestQuiescent
<1>ng. \A q \in Honest : ~ ComputationGuard(q)
  BY <1>nq, ComputationGuardIsCanCompute
<1>del. AllDelivered
  \* Name the pair << c, m >>. The hypothesis ~TickUseful does not contain that
  \* term, so no backend instantiates the empty set-builder at it. Membership is
  \* the direction the backends close (see DeliveredByDeadline).
  <2> SUFFICES ASSUME NEW c \in Honest, NEW m \in sent, m \notin rcvd[c]
               PROVE  FALSE
    BY DEF AllDelivered
  <2>1. << c, m >> \in PendingDeliveries
    BY DEF PendingDeliveries
  <2>2. PendingDeliveries = {}
    BY DEF TickUseful
  <2> QED
    BY <2>1, <2>2
<1>rty. \A q \in Honest : round[q] \in Rounds
  BY DEF TypeOK
\* ~TickUseful: no armed, live timer has a deadline still ahead of the clock.
<1>nolive. \A q \in Honest, k \in TimerType :
             timer[q][k] # OFF /\ TimerLive(q, k) => now >= timer[q][k]
  BY DEFS TickUseful, TypeOK
<1>a. \A q \in Honest : step[q] # "propose"
  BY <1>ng, <1>nolive DEFS ComputationGuard, GTimeoutPropose, ProposeTimerArmedOp, TimerLive, TimerType
<1>b. \A q \in Honest : timer[q]["precommit"] = OFF
  BY <1>nd, <1>ng, <1>nolive DEFS ComputationGuard, GTimeoutPrecommit, TimerLive, TimerType
<1>c. \A q \in Honest : step[q] = "prevote" => timer[q]["prevote"] = OFF
  BY <1>ng, <1>nolive DEFS ComputationGuard, GTimeoutPrevote, TimerLive, TimerType
<1>d. \A q \in Honest : step[q] \in {"prevote", "precommit"}
  BY <1>a, <1>nd DEFS Step, TypeOK
<1>e. \A q \in Honest : ~ RExistsAnyPrecommitQuorum(q, round[q])
  BY <1>b, <1>nd, <1>ng DEFS ComputationGuard, GSchedulePrecommit
<1>f. \A q \in Honest : step[q] = "prevote" => ~ RExistsAnyPrevoteQuorum(q, round[q])
  BY <1>c, <1>ng DEFS ComputationGuard, GSchedulePrevote
<1>g. \A q \in Honest : \E m \in sent :
        m.type = "Prevote" /\ m.sender = q /\ m.round = round[q]
  BY <1>d DEFS PrevoteSelfEvidence, RcvdSubsetSent
<1>min. PICK p \in Honest : \A q \in Honest : round[p] <= round[q]
  BY MinRoundExists
<1>1. CASE \E q \in Honest : round[p] < round[q]
  BY <1>1, <1>del, <1>e, <1>rty, CertInSentGivesQuorum DEF RoundBacked
<1>2. CASE ~(\E q \in Honest : round[p] < round[q])
  BY <1>2, <1>d, <1>del, <1>e, <1>f, <1>g, <1>min, <1>rty, AllHonestVotesGiveQuorum
  DEFS RcvdSubsetSent, RExistsAnyPrecommitQuorum, RExistsAnyPrevoteQuorum, Rounds, SelfVoteEvidenceOp
<1> QED
  BY <1>1, <1>2

\* Boxed form for the region argument: the invariants it needs are all
\* []-facts, so this is the shape RoundGrowth will consume under PTL.
LEMMA BoxQuiescentDeadlockDecides ==
  [](  TypeOK /\ RcvdSubsetSent /\ ProposeTimerArmedOp /\ DecidedStepOp
         /\ SelfVoteEvidenceOp /\ PrevoteSelfEvidence /\ RoundBacked
         /\ HonestQuiescent /\ ~TickUseful
       => SomeCorrectDecided  )
<1>1. TypeOK /\ RcvdSubsetSent /\ ProposeTimerArmedOp /\ DecidedStepOp
        /\ SelfVoteEvidenceOp /\ PrevoteSelfEvidence /\ RoundBacked
        /\ HonestQuiescent /\ ~TickUseful
        => SomeCorrectDecided
  BY QuiescentDeadlockDecides
<1> QED
  BY <1>1, PTL

THEOREM NoDeadlockInv ==
  ASSUME Spec PROVE [](HonestQuiescent /\ ~TickUseful => SomeCorrectDecided)
\* ProposeTimerArmedInv / DecidedStepInv are stated in Base in their
\* SPELLED-OUT forms, so the named-operator atoms this lemma needs come
\* through their boxed <=> bridges (no backend unfolds a DEF under []).
BY BoxQuiescentDeadlockDecides, DecidedStepBox, DecidedStepInv, InvProof, PrevoteSelfEvidenceInv, ProposeTimerArmedBox, ProposeTimerArmedInv, PTL, RoundBackedInv, SelfVoteEvidenceInv
DEF Inv

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 3: the bounded-work region argument for RoundGrowth.              *)
(*                                                                         *)
(*  Suppose the goal never happens: no correct validator ever decides and  *)
(*  no correct round ever passes Bnd(b). Then (1) Work(b) is a Nat with a  *)
(*  CONSTANT bound. Deliver, FaultyStep and Tick leave it unchanged, and   *)
(*  every honest step strictly decreases it. And (2) honest steps still    *)
(*  keep happening forever, by HonestStepsRecur of Layer 4. Facts (1) and  *)
(*  (2) contradict each other on a well-founded staircase.                 *)
(*                                                                         *)
(* Everything below is stated over the AMBIENT b, never at a substituted   *)
(* bound: Bnd is an operator, so each citation is an identity              *)
(* instantiation.                                                          *)
(***************************************************************************)

\* The shifted bound and the ceiling above it.
Bnd(b) == b + GST
Cap(b) == Bnd(b) + 1

\* The success predicate, and the state consequence of its negation.
Won(b) == SomeCorrectDecided \/ RoundAbove(Bnd(b))
RoundsCapped(b) == \A c \in Honest : round[c] <= Bnd(b)

\*   Round deficit. This is the RoundGap of ...Base, with the CONSTANT ceiling
\*   Cap(b) in place of the clock-dependent RoundCeiling. The sum Sum_{c \in
\*   Honest} (Cap(b) - round[c]) uses the same encoding by a product set,
\*   because FiniteSetTheorems has no operator for a sum. RoundGap is not
\*   TICK-INVARIANT, and this measure is, which is exactly what bounds the
\*   honest work while the clock diverges.
RoundDeficit(b) ==
  Cardinality({ pj \in Honest \X (1 .. Cap(b)) : pj[2] + round[pj[1]] <= Cap(b) })

\* The region measure: Base's Horner collapse with RoundDeficit(b) on top of
\* StepWork and BurstBottom, so a round raise dominates the two lower
\* components (Collapse3).
Work(b) ==
  (BurstBound + 1) * ((BurstBound + 1) * RoundDeficit(b) + StepWork) + BurstBottom

\* Named so the staircase's PTL steps see matching atoms.
WorkLess(b, n) == Work(b) < n

\*  "Some correct validator moved." The FAIR actions are the individual
\*  disjuncts of HonestStep. This is only the progress atom of the staircase.
HonestAct == \E p \in Honest : HonestStep(p)

\* Both-state facts the staircase legs need. Parameterized by b so RegOK(b)'
\* also supplies RoundDeficit(b)' \in Nat, which no lemma citation can
\* produce (a lemma cannot be applied "at the primed state").
RegOK(b) ==
  /\ TypeOK /\ RoundBelowNow /\ DecidedStepOp /\ BurstFactsOp
  /\ RoundDeficit(b) \in Nat

RegStep(b) == RegOK(b) /\ ~Won(b) /\ Next /\ RegOK(b)'

\* ---- Measure typing and invariance (non-temporal) ------------------------
LEMMA BndCapNat ==
  ASSUME NEW b \in Rounds
  PROVE  Bnd(b) \in Nat /\ Cap(b) \in Nat /\ Bnd(b) < Cap(b)
BY GSTType DEFS Bnd, Cap, Rounds

LEMMA RoundDeficitNat ==
  ASSUME TypeOK, NEW b \in Rounds
  PROVE  RoundDeficit(b) \in Nat
BY BndCapNat, FS_CardinalityType, FS_Interval, FS_Product, FS_Subset, HonestFinite DEF RoundDeficit

LEMMA RoundDeficitUnchanged ==
  ASSUME NEW b \in Rounds, round' = round
  PROVE  RoundDeficit(b)' = RoundDeficit(b)
BY DEFS RoundDeficit, Bnd, Cap

\*  This mirrors RoundGapDecreaseRaise of ...Base, at the constant ceiling.
\*  The witness pair << p, Cap(b) - round[p] >> of the raised validator leaves
\*  the deficit set, and nothing enters it. The cardinality therefore strictly
\*  drops.
LEMMA RoundDeficitDecreaseRaise ==
  ASSUME TypeOK, NEW b \in Rounds, NEW p \in Honest, round[p] < Cap(b),
         round' \in [Honest -> Nat],
         round'[p] > round[p],
         \A q \in Honest : q # p => round'[q] = round[q]
  PROVE  RoundDeficit(b)' < RoundDeficit(b)
<1> DEFINE S1 == { pj \in Honest \X (1 .. Cap(b)) : pj[2] + round[pj[1]]  <= Cap(b) }
<1> DEFINE S2 == { pj \in Honest \X (1 .. Cap(b)) : pj[2] + round'[pj[1]] <= Cap(b) }
<1> DEFINE x  == << p, Cap(b) - round[p] >>
<1>cn. Cap(b) \in Nat /\ Cap(b)' = Cap(b)
  BY BndCapNat DEFS Bnd, Cap
<1>0. p \in Honest /\ round[p] \in Nat /\ Cap(b) \in Nat /\ round[p] < Cap(b)
  BY <1>cn DEFS Rounds, TypeOK
<1>typ. round \in [Honest -> Nat] /\ round'[p] \in Nat
  BY DEFS Rounds, TypeOK
<1>gt. round'[p] > round[p]
  OBVIOUS
<1>rc1. RoundDeficit(b) = Cardinality(S1)
  BY DEF RoundDeficit
<1>rc2. RoundDeficit(b)' = Cardinality(S2)
  BY <1>cn DEF RoundDeficit
<1>xc. x[1] = p /\ x[2] = Cap(b) - round[p]
  OBVIOUS
<1>fin. IsFiniteSet(S1)
  BY <1>0, FS_Interval, FS_Product, FS_Subset, HonestFinite
<1>sub. S2 \subseteq S1
  BY <1>0, <1>typ, SMT
<1>xin. x \in S1
  BY <1>0, <1>xc, SMT
<1>xout. x \notin S2
  BY <1>0, <1>gt, <1>typ, <1>xc, SMT
<1> HIDE DEF S1, S2, x
<1>card. Cardinality(S2) < Cardinality(S1)
  BY <1>fin, <1>sub, <1>xin, <1>xout, StrictSubsetCard
<1> QED
  BY <1>card, <1>rc1, <1>rc2

LEMMA WorkNat ==
  ASSUME TypeOK, NEW b \in Rounds
  PROVE  Work(b) \in Nat
BY BurstBoundNat, BurstFactsFromType, RoundDeficitNat DEFS BurstFactsOp, Work

\*  Deliver, FaultyStep, Tick and stuttering all leave the measure alone. None
\*  of them touches round, step, timer, valid or sentTime. Work(b) also does
\*  not read `now`, and the ComputeWork of ...Base does.
LEMMA WorkUnchangedFrame ==
  ASSUME NEW b \in Rounds,
         round' = round, step' = step, timer' = timer, valid' = valid,
         sentTime' = sentTime
  PROVE  Work(b)' = Work(b)
BY OffLiveTimersUnchanged, ProposeOwedUnchanged, RoundDeficitUnchanged, StepWorkUnchanged, ValidStaleUnchanged
DEFS BurstBottom, BurstBound, Work

LEMMA WorkFromComponents ==
  ASSUME NEW b \in Rounds,
         RoundDeficit(b)' = RoundDeficit(b), StepWork' = StepWork,
         BurstBottom' = BurstBottom
  PROVE  Work(b)' = Work(b)
BY DEFS BurstBound, Work

LEMMA WorkPrimedNat ==
  ASSUME NEW b \in Rounds, BurstFactsOp', RoundDeficit(b)' \in Nat
  PROVE  Work(b)' \in Nat
BY BurstBoundNat DEFS BurstBound, BurstFactsOp, Work

\* Only FaultyStep needs care here: it WRITES sentTime, which ProposeOwed
\* reads through `sent`, so the plain frame argument does not apply. Base's
\* ComputeWorkUnchangedFaulty is exactly the missing step (a faulty send is
\* never an honest proposal).
LEMMA WorkUnchangedNonHonest ==
  ASSUME TypeOK, NEW b \in Rounds, [Next]_vars,
         ~(\E p \in Honest : HonestStep(p))
  PROVE  Work(b)' = Work(b)
BY ComputeWorkUnchangedDeliver, ComputeWorkUnchangedFaulty, RoundDeficitUnchanged, WorkFromComponents, WorkUnchangedFrame
DEFS Deliver, FaultyStep, HonestNext, Next, Tick, vars

\*  Every honest step strictly decreases the measure while the rounds are
\*  capped. A raise of a round drops RoundDeficit, which dominates, by
\*  Collapse3. Any other honest action freezes round, and therefore
\*  RoundDeficit. An honest action also freezes `now`, and therefore the
\*  RoundGap of ...Base. The per-action lexicographic result of ...Base
\*  therefore reduces to its two lower components.
LEMMA WorkDecreasesHonest ==
  ASSUME TypeOK, RoundBelowNow, DecidedStepOp, BurstFactsOp, BurstFactsOp',
         NEW b \in Rounds, RoundsCapped(b), RoundDeficit(b) \in Nat,
         RoundDeficit(b)' \in Nat, NEW p \in Honest, HonestStep(p)
  PROVE  Work(b)' < Work(b)
<1>bn. BurstBound \in Nat /\ BurstBound' = BurstBound
  BY BurstBoundNat DEF BurstBound
<1>now. now' = now
  BY DEFS HonestStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
    OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL,
    OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose,
    Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound
<1>lex. \/ RoundDeficit(b)' < RoundDeficit(b)
        \/ (RoundDeficit(b)' = RoundDeficit(b) /\ StepWork' < StepWork)
        \/ (RoundDeficit(b)' = RoundDeficit(b) /\ StepWork' = StepWork
              /\ BurstBottom' < BurstBottom)
  BY <1>now, BndCapNat, ComputeWorkDecreasesCompute, RoundDeficitDecreaseRaise, RoundDeficitUnchanged, RoundGapUnchanged
  DEFS DecidedStepOp, HonestStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, RoundBelowNow, Rounds, RoundsCapped, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TypeOK
<1>n1. /\ StepWork \in Nat /\ BurstBottom \in Nat
       /\ StepWork' \in Nat /\ BurstBottom' \in Nat
       /\ StepWork' <= BurstBound /\ BurstBottom' <= BurstBound
  BY <1>bn DEF BurstFactsOp
<1>col. (BurstBound + 1) * ((BurstBound + 1) * RoundDeficit(b)' + StepWork') + BurstBottom'
          < (BurstBound + 1) * ((BurstBound + 1) * RoundDeficit(b) + StepWork) + BurstBottom
  BY <1>lex, <1>bn, <1>n1, Collapse3
<1>defp. Work(b)'
           = (BurstBound + 1) * ((BurstBound + 1) * RoundDeficit(b)' + StepWork') + BurstBottom'
  BY <1>bn DEF Work
<1> QED
  BY <1>col, <1>defp DEF Work

\* ---- Boxed staircase legs (clean, Spec-free, so PTL can necessitate) -----
LEMMA BoxWonSplit ==
  ASSUME NEW b \in Rounds
  PROVE  [](Won(b) <=> (SomeCorrectDecided \/ RoundAbove(Bnd(b))))
<1>1. Won(b) <=> (SomeCorrectDecided \/ RoundAbove(Bnd(b)))
  BY DEF Won
<1> QED
  BY <1>1, PTL

LEMMA BoxBndAbovePastGST ==
  ASSUME NEW b \in Rounds
  PROVE  [](TypeOK /\ RoundAbove(Bnd(b)) => RoundAbovePastGST(b))
<1>1. TypeOK /\ RoundAbove(Bnd(b)) => RoundAbovePastGST(b)
  BY GSTType DEFS Bnd, RoundAbove, RoundAbovePastGST, Rounds, TypeOK
<1> QED
  BY <1>1, PTL

LEMMA BoxRegOK ==
  ASSUME NEW b \in Rounds
  PROVE  [](  TypeOK /\ RoundBelowNow /\ DecidedStepOp /\ BurstFactsOp
              => RegOK(b)  )
<1>1. TypeOK /\ RoundBelowNow /\ DecidedStepOp /\ BurstFactsOp => RegOK(b)
  BY RoundDeficitNat DEF RegOK
<1> QED
  BY <1>1, PTL

LEMMA BoxWorkNonNeg ==
  ASSUME NEW b \in Rounds
  PROVE  [](RegOK(b) => ~WorkLess(b, 0))
<1>1. RegOK(b) => ~WorkLess(b, 0)
  BY WorkNat DEFS RegOK, WorkLess
<1> QED
  BY <1>1, PTL

LEMMA BoxCappedFromWon ==
  ASSUME NEW b \in Rounds
  PROVE  [](TypeOK /\ ~Won(b) => RoundsCapped(b))
<1>1. TypeOK /\ ~Won(b) => RoundsCapped(b)
  BY BndCapNat DEFS RoundAbove, Rounds, RoundsCapped, TypeOK, Won
<1> QED
  BY <1>1, PTL

\* The measure never grows inside the region: an honest step lowers it, and
\* nothing else touches it.
LEMMA BoxWorkNonIncrease ==
  ASSUME NEW b \in Rounds, NEW n \in Nat
  PROVE  [](WorkLess(b, n + 1) /\ [RegStep(b)]_vars => (WorkLess(b, n + 1))')
<1>1. WorkLess(b, n + 1) /\ [RegStep(b)]_vars => (WorkLess(b, n + 1))'
  <2> SUFFICES ASSUME WorkLess(b, n + 1), [RegStep(b)]_vars
               PROVE  Work(b)' < n + 1
    BY DEF WorkLess
  <2>1. CASE vars' = vars
    BY <2>1, WorkUnchangedFrame DEFS vars, WorkLess
  <2>2. CASE RegStep(b)
    <3>0. TypeOK /\ RoundBelowNow /\ DecidedStepOp /\ BurstFactsOp
            /\ RoundDeficit(b) \in Nat /\ BurstFactsOp'
            /\ RoundDeficit(b)' \in Nat /\ Next /\ ~Won(b)
      BY <2>2 DEFS RegOK, RegStep
    <3>1. RoundsCapped(b)
      BY <3>0, BoxCappedFromWon, PTL
    <3>2. CASE \E p \in Honest : HonestStep(p)
      BY <3>0, <3>1, <3>2, WorkDecreasesHonest, WorkNat, WorkPrimedNat DEF WorkLess
    <3>3. CASE ~(\E p \in Honest : HonestStep(p))
      BY <3>0, <3>3, WorkUnchangedNonHonest DEF WorkLess
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, PTL

\* One honest step inside the region takes the measure a full step down.
LEMMA BoxWorkDrop ==
  ASSUME NEW b \in Rounds, NEW n \in Nat
  PROVE  [](  WorkLess(b, n + 1) /\ [RegStep(b)]_vars /\ <<HonestAct>>_vars
              => (WorkLess(b, n))'  )
<1>1. WorkLess(b, n + 1) /\ [RegStep(b)]_vars /\ <<HonestAct>>_vars
        => (WorkLess(b, n))'
  <2> SUFFICES ASSUME Work(b) < n + 1, [RegStep(b)]_vars, <<HonestAct>>_vars
               PROVE  Work(b)' < n
    BY DEF WorkLess
  <2>1. vars' # vars
    BY DEF HonestAct
  <2>2. RegStep(b)
    BY <2>1
  <2>3. TypeOK /\ RoundBelowNow /\ DecidedStepOp /\ BurstFactsOp
          /\ RoundDeficit(b) \in Nat /\ BurstFactsOp' /\ RoundDeficit(b)' \in Nat
          /\ ~Won(b)
    BY <2>2 DEFS RegOK, RegStep
  <2>4. RoundsCapped(b)
    BY <2>3, BoxCappedFromWon, PTL
  <2>5. PICK p \in Honest : HonestStep(p)
    BY DEF HonestAct
  <2>6. Work(b)' < Work(b)
    BY <2>3, <2>4, <2>5, WorkDecreasesHonest
  <2>7. Work(b) \in Nat /\ Work(b)' \in Nat
    BY <2>3, WorkNat, WorkPrimedNat
  <2> QED
    BY <2>6, <2>7
<1> QED
  BY <1>1, PTL

\* ---- Guard persistence with no honest step (non-temporal) ----
\* A step that is not an honest computation step is a Deliver, a FaultyStep, a
\* Tick or stuttering. Across all four, round, step, locked, valid, decision
\* and timer are FROZEN. `rcvd` only grows, and `now` only grows. Every
\* CanCompute disjunct is monotone under exactly those changes.
\*   - No disjunct bounds `now` from above, so the three OnTimeout* guards
\*     survive a Tick, because now >= deadline stays true.
\*   - The disjuncts for a quorum, and for a proposal, read only rcvd[p],
\*     which grows.
\*   - There is ONE anti-monotone conjunct, which is the "p has not proposed
\*     at its current round yet" of GPropose. Only the Propose of p itself can
\*     falsify it, and that is an honest step, because no other sender can use
\*     the name of p.
\* ...NonZeno proves the half for Deliver and for FaultyStep, in
\* G*NetworkStable. These lemmas add the halves for Tick and for stuttering.
\* Together they are what makes a guard that ever holds in the region hold
\* FOREVER, so weak fairness must fire it.
QuietStep == [Next]_vars /\ ~ <<HonestAct>>_vars

LEMMA QuietStepCases ==
  ASSUME QuietStep
  PROVE  NetworkStep \/ Tick \/ vars' = vars
BY DEFS HonestAct, HonestNext, Next, NetworkStep, QuietStep, vars

LEMMA CanComputeQuiet ==
  ASSUME TypeOK, NEW p \in Honest, CanCompute(p), QuietStep
  PROVE  CanCompute(p)'
<1>g. ComputationGuard(p)
  BY ComputationGuardIsCanCompute
\*  The aggregate: honest computability itself persists with no honest step.
\*  The lemmas above, one for each guard, stay, because weak fairness is per
\*  ACTION. The case split of the frontier has to name the guard that holds,
\*  in order to name the fair action that must fire. Primed form of
\*  ...NonZeno's ComputationGuardIsCanCompute. A lemma cannot be applied AT
\*  the primed state, so the equivalence is re-derived by unfolding: priming
\*  distributes over the definitions, and RangeCo is state-free.
<1> SUFFICES ComputationGuard(p)'
  BY RangeCo DEF ComputationGuard, CanCompute, GPropose, GTimeoutPropose,
   GProposalNoPOL, GProposalWithPOL, GSchedulePrevote, GPrevoteValueFirst,
   GPrevoteValueLate, GPrevoteNil, GTimeoutPrevote, GSchedulePrecommit,
   GPrecommitValue, GTimeoutPrecommit, GSkip
<1> USE QuietStepCases DEF ComputationGuard, Tick, vars
<1>1. CASE GPropose(p)
  BY <1>1, GProposeNetworkStable DEFS GPropose, sent
<1>2. CASE GTimeoutPropose(p)
  BY <1>2, GTimeoutProposeNetworkStable DEFS GTimeoutPropose, TimerType, TypeOK
<1>3. CASE GProposalNoPOL(p)
  BY <1>3, GProposalNoPOLNetworkStable DEFS GProposalNoPOL, RProposals, RProposalsFromProposerAt
<1>4. CASE GProposalWithPOL(p)
  BY <1>4, GProposalWithPOLNetworkStable
  DEFS GProposalWithPOL, RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor, RProposals, RProposalsFromProposerAt
<1>5. CASE GSchedulePrevote(p)
  BY <1>5, GSchedulePrevoteNetworkStable
  DEFS GSchedulePrevote, RExistsAnyPrevoteQuorum, RSendersOfTypeAtRound
<1>6. CASE GPrevoteValueFirst(p)
  BY <1>6, GPrevoteValueFirstNetworkStable
  DEFS GPrevoteValueFirst, RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor, RProposals, RProposalsFromProposerAt
<1>7. CASE GPrevoteValueLate(p)
  BY <1>7, GPrevoteValueLateNetworkStable
  DEFS GPrevoteValueLate, RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor, RProposals, RProposalsFromProposerAt
<1>8. CASE GPrevoteNil(p)
  BY <1>8, GPrevoteNilNetworkStable
  DEFS GPrevoteNil, RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor
<1>9. CASE GTimeoutPrevote(p)
  BY <1>9, GTimeoutPrevoteNetworkStable DEFS GTimeoutPrevote, TimerType, TypeOK
<1>10. CASE GSchedulePrecommit(p)
  BY <1>10, GSchedulePrecommitNetworkStable
  DEFS GSchedulePrecommit, RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound
<1>11. CASE GPrecommitValue(p)
  BY <1>11, GPrecommitValueNetworkStable
  DEFS GPrecommitValue, RExistsPrecommitQuorum, RPrecommits, RPrecommitSendersFor, RProposals, RProposalsFromProposerAt
<1>12. CASE GTimeoutPrecommit(p)
  BY <1>12, GTimeoutPrecommitNetworkStable DEFS GTimeoutPrecommit, TimerType, TypeOK
<1>13. CASE \E r \in Rounds : GSkip(p, r)
  BY <1>13, GSkipNetworkStable DEFS GSkip, RSendersOfAnyMessageAt, RSendersOfTypeAtRound
<1> QED
  BY <1>g, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 4: honest steps recur.                                            *)
(*                                                                         *)
(*  THE SHAPE. []<><<HonestAct>>_vars comes from ONE leads-to, RecurInv ~> *)
(*  <<HonestAct>>_vars, under []RecurInv: a leads-to out of an always-true *)
(*  region IS a recurrence. Nothing here needs the round bound. The        *)
(*  []~Won(b) of the caller supplies only []~SomeCorrectDecided. The work  *)
(*  is therefore done at that weaker hypothesis, and it is specialized     *)
(*  last.                                                                  *)
(*                                                                         *)
(*  THE TREE. Each branch is one WF1. The fair action that it fires, and   *)
(*  the ingredient that it consumes, are on the right.                     *)
(*                                                                         *)
(*   HonestStepsRecur                                                      *)
(*   +- NoDecisionStepsRecur              RecurInv ~> <<HonestAct>>_vars   *)
(*      +- A GuardedHonestStep            fires: any honest action         *)
(*      |  +- AggregateComputationFairness    (...NonZeno's burst core)    *)
(*      |  +- QuietKeepsWorkAndGuard                                       *)
(*      +- QuiescenceBreaks               quiescence cannot persist        *)
(*         +- B DeliverRegionBreaks       fires: Deliver(c)                *)
(*         |  +- QuiescentTailWitness         (Layers 1 and 2)             *)
(*         +- C ClockRegionBreaks         NatInduction over ClockWork(t)   *)
(*            +- TickPaysDistance         fires: Tick                      *)
(*            +- DrainPaysFrontier        fires: Deliver(c)                *)
(*                                                                         *)
(*  Each branch lands on a NAMED state predicate (TailGoal, ClockGoal,     *)
(*  TimerReached) and bridges to ~HonestQuiescent in a separate boxed      *)
(*  step. An action leg of a WF1 must produce Goal', and no lemma can be   *)
(*  applied AT the primed state. The target must therefore be something    *)
(*  that priming distributes over. That is a monotone pool, a frozen       *)
(*  timer, or a cardinality.                                               *)
(*                                                                         *)
(* THE THREE BRANCHES.                                                     *)
(*                                                                         *)
(*  A. ~HonestQuiescent, that is some honest guard is live. The            *)
(*  maximal-progress gate of Tick IS ~HonestQuiescent, so a live guard     *)
(*  FREEZES the clock. With the clock frozen, ComputeWork cannot rise,     *)
(*  because Deliver, FaultyStep and stuttering leave it alone. The         *)
(*  AggregateComputationFairness of ...NonZeno makes it DROP. Only an      *)
(*  honest step can drop it, so the thirteen-way fairness split of the     *)
(*  burst core is not repeated here.                                       *)
(*                                                                         *)
(*  B. HonestQuiescent with no live timer. Layers 1 and 2 put a quorum     *)
(*  certificate in `sent` for some correct c that has NOT received it.     *)
(*  Deliver(c) is therefore continuously enabled, and ONE batched          *)
(*  Deliver(c) hands c the whole pool. c can then compute again.           *)
(*                                                                         *)
(*  C. HonestQuiescent with a live timer at t. A staircase of Tick and     *)
(*  Deliver steps over ClockWork(t) drives the clock to t, where the       *)
(*  OnTimeout* guard of that timer fires. Tick is gated on the Gossip      *)
(*  deadline, so the staircase alternates. While some correct validator    *)
(*  still misses an OLD message, fair Deliver steps drain the frontier.    *)
(*  The frontier cannot grow at a standing clock, because a fresh          *)
(*  activation carries sentTime = now. Once the frontier is empty, Tick is *)
(*  enabled, and it reduces the distance to t.                             *)
(***************************************************************************)

\* ---- The region -----------------------------------------------------------
\* ...NonZeno's burst core (TypeOK, RcvdSubsetSent, SentInv, RoundBelowNow,
\* DecidedStepOp, BurstFactsOp) plus the delivery timestamp fact and the four
\* evidence invariants of Layers 1 and 2. RecurNext is the step form, so the
\* staircase legs below see the invariants on BOTH sides of a step (the NZNext
\* idiom).
RecurInv ==
  /\ NZCore
  /\ SentTimeLeNow
  /\ ProposeTimerArmedOp
  /\ SelfVoteEvidenceOp
  /\ PrevoteSelfEvidence
  /\ RoundBacked

RecurNext == Next /\ RecurInv /\ RecurInv'

THEOREM RecurInvThm == ASSUME Spec PROVE []RecurInv
BY NZCoreInv, PrevoteSelfEvidenceInv, ProposeTimerArmedBox, ProposeTimerArmedInv,
   RoundBackedInv, SelfVoteEvidenceInv, SentTimeLeNowInv, PTL DEF RecurInv

THEOREM RecurNextThm == ASSUME Spec PROVE [][RecurNext]_vars
<1>1. []RecurInv
  BY RecurInvThm
<1>2. [][Next]_vars
  BY DEF Spec
<1> QED
  BY <1>1, <1>2, PTL DEF RecurNext

\*  ---- Quiescence rules out an honest step ---------------------------------
\*  CanCompute is exactly the disjunction of the guards of the honest actions.
\*  A quiescent state therefore has no honest successor at all. Every step out
\*  of it is a QuietStep, and the frame lemmas below apply to it.
LEMMA HonestStepCanCompute ==
  ASSUME TypeOK, NEW q \in Honest, HonestStep(q)
  PROVE  CanCompute(q)
BY RangeCo
   DEFS CanCompute, HonestStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
   OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL,
   OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose,
   Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound

LEMMA QuiescentQuietStep ==
  ASSUME TypeOK, HonestQuiescent, [Next]_vars
  PROVE  QuietStep
BY HonestStepCanCompute DEFS HonestAct, HonestQuiescent, QuietStep

\* A quiet step freezes the whole consensus state of every correct validator
\* and only grows the pool and the clock. This is the frame every stability
\* leg below rests on.
LEMMA QuietFreezesState ==
  ASSUME TypeOK, QuietStep
  PROVE  /\ round' = round /\ step' = step /\ timer' = timer
         /\ decision' = decision /\ valid' = valid
         /\ sent \subseteq sent' /\ now <= now'
BY NowMonotoneStep, QuietStepCases, SentMonotoneStep DEFS Deliver, FaultyStep, NetworkStep, QuietStep, Tick, vars

\*  A message that is already activated keeps its timestamp across a quiet
\*  step. The only writer of sentTime that a quiet step allows is FaultyStep,
\*  and its guard is sentTime[m] = OFF. It therefore never touches a slot that
\*  is already set.
LEMMA QuietFreezesSentTime ==
  ASSUME TypeOK, QuietStep, NEW m, m \in sent
  PROVE  sentTime'[m] = sentTime[m]
BY QuietStepCases DEFS Deliver, FaultyStep, NetworkStep, sent, Tick, TypeOK, vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* BRANCH A: a live guard forces an honest step.                           *)
(***************************************************************************)

\*  With a guard live, the clock is pinned, because Tick needs maximal
\*  progress. No step other than an honest one can therefore move ComputeWork.
\*  The guard itself also survives, by CanComputeQuiet.
LEMMA QuietKeepsWorkAndGuard ==
  ASSUME NZCore, ~HonestQuiescent, QuietStep
  PROVE  ComputeWork' = ComputeWork /\ ~HonestQuiescent'
BY CanComputeQuiet, ComputeWorkStutter, NetworkStepKeepsWork, QuietStepCases DEFS HonestQuiescent, NZCore, Tick

LEMMA BoxGuardAntecedent ==
  [](  RecurInv /\ ~HonestQuiescent
       => NZCore /\ (\E p \in Honest : CanCompute(p))  )
<1>1. RecurInv /\ ~HonestQuiescent => NZCore /\ (\E p \in Honest : CanCompute(p))
  BY DEFS HonestQuiescent, RecurInv
<1> QED
  BY <1>1, PTL

LEMMA BoxWorkEqNotBelow ==
  ASSUME NEW n \in Nat
  PROVE  [](ComputeWork = n + 1 => ~(ComputeWork <= n))
<1>1. ComputeWork = n + 1 => ~(ComputeWork <= n)
  OBVIOUS
<1> QED
  BY <1>1, PTL

LEMMA BoxGuardWorkStabLeg ==
  ASSUME NEW n \in Nat
  PROVE  [](  RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1 /\ [Next]_vars
              => (~HonestQuiescent /\ ComputeWork = n + 1)'
                 \/ <<HonestAct>>_vars  )
<1>1. RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1 /\ [Next]_vars
        => (~HonestQuiescent /\ ComputeWork = n + 1)' \/ <<HonestAct>>_vars
  BY QuietKeepsWorkAndGuard DEFS QuietStep, RecurInv
<1> QED
  BY <1>1, PTL

\*   WF1 is not necessary here. The aggregate fairness of the burst core
\*   already gives the eventual drop. The leg above says that the drop cannot
\*   happen without an honest step.
THEOREM GuardedHonestStepAt ==
  ASSUME Spec, NEW n \in Nat
  PROVE  (RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
           ~> <<HonestAct>>_vars
<1>inv. []RecurInv
  BY RecurInvThm
<1>nx. [][Next]_vars
  BY DEF Spec
<1>agg. (NZCore /\ ComputeWork = n + 1 /\ (\E p \in Honest : CanCompute(p)))
          ~> (ComputeWork <= n)
  BY AggregateComputationFairness
<1>ant. [](  RecurInv /\ ~HonestQuiescent
             => NZCore /\ (\E p \in Honest : CanCompute(p))  )
  BY BoxGuardAntecedent
<1>ne. [](ComputeWork = n + 1 => ~(ComputeWork <= n))
  BY BoxWorkEqNotBelow
<1>st. [](  RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1 /\ [Next]_vars
            => (~HonestQuiescent /\ ComputeWork = n + 1)' \/ <<HonestAct>>_vars  )
  BY BoxGuardWorkStabLeg
<1> QED
  BY <1>agg, <1>ant, <1>inv, <1>ne, <1>nx, <1>st, PTL

\* ---- Existential lift over the rank ---------------------------------------
LEMMA BoxGuardWorkExN ==
  [](  RecurInv /\ ~HonestQuiescent
       => (\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)  )
<1>1. RecurInv /\ ~HonestQuiescent
        => (\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
  <2> SUFFICES ASSUME RecurInv, ~HonestQuiescent
               PROVE  \E n \in Nat : ComputeWork = n + 1
    OBVIOUS
  <2>1. ComputeWork \in Nat
    BY ComputeWorkType DEFS NZCore, RecurInv
  <2>2. ~(ComputeWork <= 0)
    BY ComputeWorkZeroImpliesQuiescent DEF RecurInv
  <2>3. ComputeWork - 1 \in Nat
    BY <2>1, <2>2
  <2> WITNESS ComputeWork - 1 \in Nat
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, PTL

LEMMA GuardWorkCommute ==
  ASSUME NEW TEMPORAL D,
         \A n \in Nat :
           [](  (RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1) => D  )
  PROVE  [](\A n \in Nat :
              ((RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1) => D))
OBVIOUS

LEMMA GuardWorkBoxFO ==
  [](  (\A n \in Nat :
          ((RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
             => <><<HonestAct>>_vars))
       => ((\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
             => <><<HonestAct>>_vars)  )
<1>1. (\A n \in Nat :
         ((RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
            => <><<HonestAct>>_vars))
       => ((\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
            => <><<HonestAct>>_vars)
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM GuardedHonestStep ==
  ASSUME Spec
  PROVE  (RecurInv /\ ~HonestQuiescent) ~> <<HonestAct>>_vars
<1>1. \A n \in Nat :
        [](  (RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
             => <><<HonestAct>>_vars  )
  <2> SUFFICES ASSUME NEW n \in Nat
               PROVE  [](  (RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
                           => <><<HonestAct>>_vars  )
    OBVIOUS
  <2>1. (RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
          ~> <<HonestAct>>_vars
    BY GuardedHonestStepAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A n \in Nat :
           ((RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
              => <><<HonestAct>>_vars))
  BY <1>1, GuardWorkCommute
<1>3. (\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)
        ~> <<HonestAct>>_vars
  BY <1>2, GuardWorkBoxFO, PTL
<1>4. [](  RecurInv /\ ~HonestQuiescent
           => (\E n \in Nat : RecurInv /\ ~HonestQuiescent /\ ComputeWork = n + 1)  )
  BY BoxGuardWorkExN
<1> QED
  BY <1>3, <1>4, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* BRANCH B: one batched delivery unsticks the certificate holder.         *)
(*                                                                         *)
(*  What a quiescent correct validator can still be handed is in `sent`,   *)
(*  and Layers 1 and 2 say what is there. Two shapes are enough. The first *)
(*  is an any-value precommit quorum for its own round, which arms its     *)
(*  precommit timer. The second is an any-value prevote quorum for its own *)
(*  round, which arms its prevote timer. Deliver is BATCHED, so ONE        *)
(*  delivery closes the gap.                                               *)
(***************************************************************************)

PrevoteQuorumInSent(r) ==
  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil : Prevote(s, r, v) \in sent

\* p holds the whole global pool.
AllTo(p) == sent \subseteq rcvd[p]

ArmablePrecommit(p) ==
  /\ step[p] # "decided"
  /\ timer[p]["precommit"] = OFF
  /\ PrecommitQuorumInSent(round[p])

ArmablePrevote(p) ==
  /\ step[p] = "prevote"
  /\ timer[p]["prevote"] = OFF
  /\ PrevoteQuorumInSent(round[p])

\* p is one Deliver away from computing again.
Deliverable(p) == ArmablePrecommit(p) \/ ArmablePrevote(p)

\* Some correct validator is Deliverable AND already holds the pool: such a
\* state is not quiescent.
Unstuck == \E p \in Honest : Deliverable(p) /\ AllTo(p)

\* The two exits from the quiescent tail, as one named atom for the PTL glue.
TailGoal == Unstuck \/ ~HonestQuiescent

\* A global-pool quorum is a quorum in the view of a validator that holds the
\* pool (value-free siblings of CertInSentGivesQuorum).
LEMMA SentPrecommitQuorumInView ==
  ASSUME TypeOK, NEW p \in Honest, AllTo(p), NEW r, PrecommitQuorumInSent(r)
  PROVE  RExistsAnyPrecommitQuorum(p, r)
BY DEFS AllTo, Precommit, PrecommitQuorumInSent, RExistsAnyPrecommitQuorum,
   RSendersOfTypeAtRound

LEMMA SentPrevoteQuorumInView ==
  ASSUME TypeOK, NEW p \in Honest, AllTo(p), NEW r, PrevoteQuorumInSent(r)
  PROVE  RExistsAnyPrevoteQuorum(p, r)
BY DEFS AllTo, Prevote, PrevoteQuorumInSent, RExistsAnyPrevoteQuorum,
   RSendersOfTypeAtRound

LEMMA UnstuckCanCompute ==
  ASSUME TypeOK, Unstuck
  PROVE  ~HonestQuiescent
BY ComputationGuardIsCanCompute, SentPrecommitQuorumInView, SentPrevoteQuorumInView
DEFS ArmablePrecommit, ArmablePrevote, ComputationGuard, Deliverable, GSchedulePrecommit, GSchedulePrevote, HonestQuiescent, Unstuck

LEMMA BoxTailGoalQuiescence ==
  [](RecurInv /\ TailGoal => ~HonestQuiescent)
<1>1. RecurInv /\ TailGoal => ~HonestQuiescent
  BY UnstuckCanCompute DEFS NZCore, RecurInv, TailGoal
<1> QED
  BY <1>1, PTL

\*  ---- What `sent` contains in a stalled quiescent state -------------------
\*  A sent message of a vote type IS the canonical vote record. The three
\*  message shapes have disjoint `type` fields, so sender, round and valueID
\*  determine it.
LEMMA SentPrecommitCanonical ==
  ASSUME TypeOK, NEW m, m \in sent, m.type = "Precommit"
  PROVE  \E v \in ValuesOrNil : Precommit(m.sender, m.round, v) \in sent
BY DEFS Message, PrecommitMsg, Precommit, PrevoteMsg, ProposalMsg, sent, TypeOK,
   ValuesOrNil

LEMMA SentPrevoteCanonical ==
  ASSUME TypeOK, NEW m, m \in sent, m.type = "Prevote"
  PROVE  \E v \in ValuesOrNil : Prevote(m.sender, m.round, v) \in sent
BY DEFS Message, PrecommitMsg, Prevote, PrevoteMsg, ProposalMsg, sent, TypeOK,
   ValuesOrNil

\* Votes of the WHOLE correct set at one round are a global-pool quorum: the
\* witness is QuorumAvailable's all-honest 2f+1 quorum.
LEMMA AllHonestPrecommitsInSent ==
  ASSUME TypeOK, NEW r,
         \A d \in Honest :
           \E m \in sent : m.type = "Precommit" /\ m.sender = d /\ m.round = r
  PROVE  PrecommitQuorumInSent(r)
BY QuorumAvailable, SentPrecommitCanonical DEF PrecommitQuorumInSent

LEMMA AllHonestPrevotesInSent ==
  ASSUME TypeOK, NEW r,
         \A d \in Honest :
           \E m \in sent : m.type = "Prevote" /\ m.sender = d /\ m.round = r
  PROVE  PrevoteQuorumInSent(r)
BY QuorumAvailable, SentPrevoteCanonical DEF PrevoteQuorumInSent

\* No armed live timer is still ahead of the clock: what ~TickUseful asks for,
\* minus the delivery frontier.
NoLiveTimer ==
  \A q \in Honest, k \in TimerType :
    ~(timer[q][k] # OFF /\ now < timer[q][k] /\ TimerLive(q, k))

\*  The state analysis of Layer 2, stopped one step earlier. It does not
\*  conclude a decision from a DELIVERED certificate. It exhibits the
\*  certificate in the pool, and the correct validator that the certificate
\*  belongs to.
LEMMA QuiescentTailWitness ==
  ASSUME TypeOK, RcvdSubsetSent, ProposeTimerArmedOp, DecidedStepOp,
         SelfVoteEvidenceOp, PrevoteSelfEvidence, RoundBacked,
         HonestQuiescent, NoLiveTimer, ~SomeCorrectDecided
  PROVE  \E p \in Honest : Deliverable(p)
<1>nd. \A q \in Honest : decision[q] = nil /\ step[q] # "decided"
  BY DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
<1>ng. \A q \in Honest : ~ ComputationGuard(q)
  BY ComputationGuardIsCanCompute DEF HonestQuiescent
<1>nolive. \A q \in Honest, k \in TimerType :
             timer[q][k] # OFF /\ TimerLive(q, k) => now >= timer[q][k]
  BY DEFS NoLiveTimer, TimerType, TypeOK
<1>a. \A q \in Honest : step[q] # "propose"
  BY <1>ng, <1>nolive
  DEFS ComputationGuard, GTimeoutPropose, ProposeTimerArmedOp, TimerLive, TimerType
<1>b. \A q \in Honest : timer[q]["precommit"] = OFF
  BY <1>nd, <1>ng, <1>nolive
  DEFS ComputationGuard, GTimeoutPrecommit, TimerLive, TimerType
<1>c. \A q \in Honest : step[q] = "prevote" => timer[q]["prevote"] = OFF
  BY <1>ng, <1>nolive DEFS ComputationGuard, GTimeoutPrevote, TimerLive, TimerType
<1>d. \A q \in Honest : step[q] \in {"prevote", "precommit"}
  BY <1>a, <1>nd DEFS Step, TypeOK
<1>rty. \A q \in Honest : round[q] \in Rounds
  BY DEF TypeOK
<1>min. PICK p \in Honest : \A q \in Honest : round[p] <= round[q]
  BY MinRoundExists
<1>1. CASE \E q \in Honest : round[p] < round[q]
  BY <1>1, <1>b, <1>min, <1>nd, <1>rty DEFS ArmablePrecommit, Deliverable, RoundBacked
<1>2. CASE ~(\E q \in Honest : round[p] < round[q])
  BY <1>2, <1>b, <1>c, <1>d, <1>min, <1>nd, <1>rty, AllHonestPrecommitsInSent, AllHonestPrevotesInSent
  DEFS ArmablePrecommit, ArmablePrevote, Deliverable, PrevoteSelfEvidence, RcvdSubsetSent, Rounds, SelfVoteEvidenceOp
<1> QED
  BY <1>1, <1>2

\*  ---- The WF1 on Deliver(p) -----------------------------------------------
\*  p is Deliverable and still missing something. Only the delivery of p
\*  itself can empty Available(p). A faulty activation hands its message to
\*  ONE correct validator, and it grows `sent` by the same message. Deliver(p)
\*  therefore stays enabled, and weak fairness fires it.
DeliverRegion(p) == HonestQuiescent /\ Deliverable(p) /\ ~AllTo(p)

LEMMA DeliverableQuietStable ==
  ASSUME TypeOK, NEW p \in Honest, Deliverable(p), QuietStep
  PROVE  Deliverable(p)'
BY QuietFreezesState
   DEFS ArmablePrecommit, ArmablePrevote, Deliverable, PrecommitQuorumInSent,
   PrevoteQuorumInSent

\* Deliver is batched and every activated message is deliverable
\* (SentTimeLeNow), so one Deliver(p) hands p the whole pool.
LEMMA DeliverGivesPool ==
  ASSUME TypeOK, SentTimeLeNow, NEW p \in Honest, Deliver(p)
  PROVE  AllTo(p)'
BY DEFS AllTo, Available, Deliver, sent, SentTimeLeNow, TypeOK

LEMMA BoxDeliverActLeg ==
  ASSUME NEW c \in Honest
  PROVE  [](RecurInv /\ DeliverRegion(c) /\ <<Deliver(c)>>_vars => TailGoal')
<1>1. RecurInv /\ DeliverRegion(c) /\ <<Deliver(c)>>_vars => TailGoal'
  BY DeliverableQuietStable, DeliverGivesPool, QuiescentQuietStep
  DEFS Deliver, DeliverRegion, HonestNext, Next, NZCore, RecurInv, TailGoal, Unstuck, vars
<1> QED
  BY <1>1, PTL

LEMMA BoxDeliverEnabledLeg ==
  ASSUME NEW c \in Honest
  PROVE  [](RecurInv /\ DeliverRegion(c) => ENABLED <<Deliver(c)>>_vars)
<1>1. RecurInv /\ DeliverRegion(c) => ENABLED <<Deliver(c)>>_vars
  BY EnabledDeliver DEFS AllTo, DeliverRegion, NZCore, RecurInv, sent
<1> QED
  BY <1>1, PTL

LEMMA BoxDeliverStabLeg ==
  ASSUME NEW c \in Honest
  PROVE  [](  RecurInv /\ DeliverRegion(c) /\ [Next]_vars
              => DeliverRegion(c)' \/ TailGoal'  )
<1>1. RecurInv /\ DeliverRegion(c) /\ [Next]_vars => DeliverRegion(c)' \/ TailGoal'
  BY DeliverableQuietStable, QuiescentQuietStep DEFS DeliverRegion, NZCore, RecurInv, TailGoal, Unstuck
<1> QED
  BY <1>1, PTL

THEOREM DeliverBreaksQuiescenceAt ==
  ASSUME Spec, NEW c \in Honest
  PROVE  (RecurInv /\ DeliverRegion(c)) ~> ~HonestQuiescent
<1>inv. []RecurInv
  BY RecurInvThm
<1>nx. [][Next]_vars
  BY DEF Spec
<1>wf. WF_vars(Deliver(c))
  BY DEF Spec, Fairness
<1>a. [](RecurInv /\ DeliverRegion(c) /\ <<Deliver(c)>>_vars => TailGoal')
  BY BoxDeliverActLeg
<1>e. [](RecurInv /\ DeliverRegion(c) => ENABLED <<Deliver(c)>>_vars)
  BY BoxDeliverEnabledLeg
<1>s. [](  RecurInv /\ DeliverRegion(c) /\ [Next]_vars
           => DeliverRegion(c)' \/ TailGoal'  )
  BY BoxDeliverStabLeg
<1>1. (RecurInv /\ DeliverRegion(c)) ~> TailGoal
  BY <1>a, <1>e, <1>inv, <1>nx, <1>s, <1>wf, PTL
<1>2. [](RecurInv /\ TailGoal => ~HonestQuiescent)
  BY BoxTailGoalQuiescence
<1> QED
  BY <1>1, <1>2, <1>inv, PTL

LEMMA DeliverRegionCommute ==
  ASSUME NEW TEMPORAL D,
         \A c \in Honest : []((RecurInv /\ DeliverRegion(c)) => D)
  PROVE  [](\A c \in Honest : ((RecurInv /\ DeliverRegion(c)) => D))
OBVIOUS

LEMMA DeliverRegionBoxFO ==
  [](  (\A c \in Honest :
          ((RecurInv /\ DeliverRegion(c)) => <>~HonestQuiescent))
       => ((\E c \in Honest : RecurInv /\ DeliverRegion(c))
             => <>~HonestQuiescent)  )
<1>1. (\A c \in Honest : ((RecurInv /\ DeliverRegion(c)) => <>~HonestQuiescent))
       => ((\E c \in Honest : RecurInv /\ DeliverRegion(c))
            => <>~HonestQuiescent)
  OBVIOUS
<1> QED
  BY <1>1, PTL

LEMMA BoxDeliverRegionSplit ==
  [](  RecurInv /\ (\E c \in Honest : DeliverRegion(c))
       => (\E c \in Honest : RecurInv /\ DeliverRegion(c))  )
<1>1. RecurInv /\ (\E c \in Honest : DeliverRegion(c))
        => (\E c \in Honest : RecurInv /\ DeliverRegion(c))
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM DeliverRegionBreaks ==
  ASSUME Spec
  PROVE  (RecurInv /\ (\E c \in Honest : DeliverRegion(c))) ~> ~HonestQuiescent
<1>1. \A c \in Honest : []((RecurInv /\ DeliverRegion(c)) => <>~HonestQuiescent)
  <2> SUFFICES ASSUME NEW c \in Honest
               PROVE  []((RecurInv /\ DeliverRegion(c)) => <>~HonestQuiescent)
    OBVIOUS
  <2>1. (RecurInv /\ DeliverRegion(c)) ~> ~HonestQuiescent
    BY DeliverBreaksQuiescenceAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A c \in Honest : ((RecurInv /\ DeliverRegion(c)) => <>~HonestQuiescent))
  BY <1>1, DeliverRegionCommute
<1>3. (\E c \in Honest : RecurInv /\ DeliverRegion(c)) ~> ~HonestQuiescent
  BY <1>2, DeliverRegionBoxFO, PTL
<1>4. [](  RecurInv /\ (\E c \in Honest : DeliverRegion(c))
           => (\E c \in Honest : RecurInv /\ DeliverRegion(c))  )
  BY BoxDeliverRegionSplit
<1> QED
  BY <1>3, <1>4, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* BRANCH C: the clock staircase to a live timer's deadline.               *)
(*                                                                         *)
(*   Tick is gated on the Gossip deadline, so the clock cannot simply be   *)
(*   driven forward. While some correct validator still misses an OLD      *)
(*   message, the gate can be shut. That frontier is what the staircase    *)
(*   alternates with. It cannot GROW while the clock stands still, because *)
(*   a fresh activation carries sentTime = now, and it is therefore not    *)
(*   old. Each fair Deliver empties the share of one validator. Once the   *)
(*   frontier is empty, the gate is open. A pending message that is not    *)
(*   old was activated AT now, and its deadline is at least now + Delta >= *)
(*   now + 2.                                                              *)
(***************************************************************************)

\* c is missing a message that was activated STRICTLY before now.
OldPending(c) == \E m \in sent : m \notin rcvd[c] /\ sentTime[m] < now
OldPendingSet == { c \in Honest : OldPending(c) }
OldCount      == Cardinality(OldPendingSet)

\* Distance to a fixed clock target, in Base's Mreach shape (0 once passed).
TickDeficit(t) == IF now >= t THEN 0 ELSE t - now

\*  The staircase measure. A Tick reduces the distance, but it can restore the
\*  whole frontier. The radix |Honest| + 1 therefore keeps a Tick dominating,
\*  by MulStep. A Deliver reduces the frontier at a standing clock.
ClockWork(t) == (Cardinality(Honest) + 1) * TickDeficit(t) + OldCount

\* Some correct validator has a live timer whose deadline is exactly t.
SomeTimerAt(t) ==
  \E q \in Honest, k \in TimerType : timer[q][k] = t /\ TimerLive(q, k)

TimerReached(t) == SomeTimerAt(t) /\ now >= t
ClockRegion(t)  == HonestQuiescent /\ SomeTimerAt(t) /\ now < t
ClockAt(t, n)   == ClockRegion(t) /\ ClockWork(t) <= n

\* The three exits from the clock region at rank n.
ClockGoal(t, n) == ClockAt(t, n) \/ TimerReached(t) \/ ~HonestQuiescent

\*  The two sub-regions that the drop of the rank is split over. Either the
\*  gate is open, and Tick fires, or some correct validator is behind on an
\*  old message, and Deliver fires.
TickRegion(t, n)     == ClockAt(t, n + 1) /\ OldPendingSet = {}
DrainRegion(t, n, c) == ClockAt(t, n + 1) /\ OldPending(c)

\* ---- Measure typing ------------------------------------------------------
LEMMA OldCountFacts ==
  OldCount \in Nat /\ OldCount <= Cardinality(Honest)
BY FS_CardinalityType, FS_Subset, HonestFinite DEFS OldCount, OldPendingSet

\* Primed sibling: a lemma cannot be applied AT the primed state, and the
\* frontier is a subset of the CONSTANT set Honest in either state.
LEMMA OldCountPrimedFacts ==
  OldCount' \in Nat /\ OldCount' <= Cardinality(Honest)
BY FS_CardinalityType, FS_Subset, HonestFinite DEFS OldCount, OldPendingSet

LEMMA ClockWorkNat ==
  ASSUME TypeOK, NEW t \in Int
  PROVE  ClockWork(t) \in Nat
BY BurstBoundNat, OldCountFacts DEFS ClockWork, TickDeficit, TypeOK

LEMMA ClockWorkPrimedNat ==
  ASSUME TypeOK', NEW t \in Int
  PROVE  ClockWork(t)' \in Nat
BY BurstBoundNat, OldCountPrimedFacts DEFS ClockWork, TickDeficit, TypeOK

\* ---- The frontier only shrinks at a standing clock -----------------------
LEMMA OldSetQuietMono ==
  ASSUME TypeOK, QuietStep, now' = now
  PROVE  OldPendingSet' \subseteq OldPendingSet
BY QuietStepCases, RcvdMonotoneStep
DEFS Deliver, FaultyStep, NetworkStep, OldPending, OldPendingSet, QuietStep, sent, Tick, TypeOK, vars

\*  Only the delivery of c itself takes c out of the frontier. A faulty
\*  activation hands its message to ONE correct validator, and it grows `sent`
\*  by the same message. No quiet step ever un-sends a message, and none
\*  re-stamps one.
LEMMA OldPendingQuietStable ==
  ASSUME TypeOK, NEW c \in Honest, OldPending(c), QuietStep, ~Deliver(c)
  PROVE  OldPending(c)'
BY NowMonotoneStep, NowShape, QuietFreezesSentTime, QuietStepCases, SentMonotoneStep
DEFS Deliver, FaultyStep, NetworkStep, OldPending, QuietStep, sent, Tick, TypeOK, vars

LEMMA OldSetDeliverEmpties ==
  ASSUME TypeOK, SentTimeLeNow, NEW c \in Honest, Deliver(c)
  PROVE  ~ OldPending(c)'
BY DeliverGivesPool DEFS AllTo, Deliver, OldPending

LEMMA OldCountDeliverDrops ==
  ASSUME TypeOK, SentTimeLeNow, QuietStep, NEW c \in Honest, Deliver(c),
         OldPending(c)
  PROVE  OldCount' < OldCount
BY FS_Subset, HonestFinite, OldSetDeliverEmpties, OldSetQuietMono, StrictSubsetCard
DEFS Deliver, OldCount, OldPendingSet

\* ---- The measure per step ------------------------------------------------
LEMMA ClockWorkQuietMono ==
  ASSUME TypeOK, TypeOK', QuietStep, ~Tick, NEW t \in Int
  PROVE  ClockWork(t)' <= ClockWork(t)
BY BurstBoundNat, FS_Subset, HonestFinite, NowStaysUnlessTick, OldCountFacts, OldCountPrimedFacts, OldSetQuietMono
DEFS ClockWork, OldCount, OldPendingSet, QuietStep, TickDeficit, TypeOK

LEMMA ClockWorkTickDrops ==
  ASSUME TypeOK, TypeOK', NEW t \in Int, Tick, now < t
  PROVE  ClockWork(t)' < ClockWork(t)
<1>bn. Cardinality(Honest) \in Nat
  BY BurstBoundNat
<1>now. now' = now + 1
  BY TickIncrements
<1>d. TickDeficit(t) = t - now /\ TickDeficit(t) \in Nat
  BY DEFS TickDeficit, TypeOK
<1>d2. TickDeficit(t)' \in Nat /\ TickDeficit(t)' < TickDeficit(t)
  BY <1>d, <1>now DEFS TickDeficit, TypeOK
<1>o. OldCount' \in Nat /\ OldCount' <= Cardinality(Honest)
  BY OldCountPrimedFacts
<1>o2. OldCount \in Nat
  BY OldCountFacts
<1>1. (Cardinality(Honest) + 1) * TickDeficit(t)' + OldCount'
        < (Cardinality(Honest) + 1) * TickDeficit(t)
  BY <1>bn, <1>d, <1>d2, <1>o, MulStep
<1> QED
  BY <1>1, <1>bn, <1>d, <1>d2, <1>o, <1>o2 DEF ClockWork

\* ---- Tick is enabled once the frontier is empty --------------------------
LEMMA EmptyFrontierDeadlineOk ==
  ASSUME TypeOK, SentTimeLeNow, OldPendingSet = {}, NEW pm \in PendingDeliveries
  PROVE  now + 1 < DeliveryDeadline(pm[2])
BY DeltaType, GSTType DEFS DeliveryDeadline, OldPending, OldPendingSet, PendingDeliveries, sent, SentTimeLeNow, TypeOK

LEMMA TickEnabledInClockRegion ==
  ASSUME TypeOK, SentTimeLeNow, NEW t \in Int, ClockRegion(t), OldPendingSet = {}
  PROVE  ENABLED <<Tick>>_vars
BY EmptyFrontierDeadlineOk, TickEnabledFromGuards
DEFS ClockRegion, HonestQuiescent, OFF, SomeTimerAt, TickUseful, TypeOK

\*  ---- The clock arriving at the deadline breaks quiescence ----------------
\*  TimerLive(q, k) is exactly the step condition of the OnTimeout* action
\*  that the timer k guards. An armed live timer at or below the clock IS
\*  therefore a guard.
LEMMA TimerReachedBreaksQuiescence ==
  ASSUME TypeOK, NEW t \in Nat, TimerReached(t)
  PROVE  ~HonestQuiescent
BY ComputationGuardIsCanCompute
DEFS ComputationGuard, GTimeoutPrecommit, GTimeoutPrevote, GTimeoutPropose, HonestQuiescent, OFF, SomeTimerAt, TimerLive, TimerReached, TimerType

LEMMA BoxTimerReachedBreaks ==
  ASSUME NEW t \in Nat
  PROVE  [](RecurInv /\ TimerReached(t) => ~HonestQuiescent)
<1>1. RecurInv /\ TimerReached(t) => ~HonestQuiescent
  BY TimerReachedBreaksQuiescence DEFS NZCore, RecurInv
<1> QED
  BY <1>1, PTL

LEMMA SomeTimerAtQuietStable ==
  ASSUME TypeOK, NEW t, SomeTimerAt(t), QuietStep
  PROVE  SomeTimerAt(t)'
BY QuietFreezesState DEFS SomeTimerAt, TimerLive, TimerType

\* ---- What each of the two fair steps achieves ----------------------------
LEMMA TickReachesClockGoal ==
  ASSUME TypeOK, TypeOK', SentTimeLeNow, NEW t \in Nat, NEW n \in Nat,
         ClockAt(t, n + 1), Tick, HonestQuiescent'
  PROVE  ClockAt(t, n)' \/ TimerReached(t)'
BY ClockWorkNat, ClockWorkPrimedNat, ClockWorkTickDrops, QuiescentQuietStep, SomeTimerAtQuietStable, TickIncrements
DEFS ClockAt, ClockRegion, Next, Tick, TimerReached, TypeOK

LEMMA DrainReachesClockGoal ==
  ASSUME TypeOK, TypeOK', SentTimeLeNow, NEW t \in Nat, NEW n \in Nat,
         NEW c \in Honest, ClockAt(t, n + 1), OldPending(c), Deliver(c),
         HonestQuiescent'
  PROVE  ClockAt(t, n)'
<1>q. QuietStep
  BY QuiescentQuietStep DEFS ClockAt, ClockRegion, Deliver, HonestNext, Next
<1>now. now' = now
  BY DEF Deliver
<1>1. OldCount' < OldCount
  BY <1>q, OldCountDeliverDrops
<1>2. TickDeficit(t)' = TickDeficit(t)
  BY <1>now DEF TickDeficit
<1>3. OldCount \in Nat /\ OldCount' \in Nat /\ Cardinality(Honest) \in Nat
      /\ TickDeficit(t) \in Nat
  BY BurstBoundNat, OldCountFacts, OldCountPrimedFacts DEFS TickDeficit, TypeOK
<1>w. ClockWork(t)' < ClockWork(t)
  BY <1>1, <1>2, <1>3 DEF ClockWork
<1>wn. ClockWork(t)' \in Nat /\ ClockWork(t) \in Nat
  BY ClockWorkNat, ClockWorkPrimedNat
<1>wle. ClockWork(t)' <= n
  BY <1>w, <1>wn DEF ClockAt
<1>tm. SomeTimerAt(t)'
  BY <1>q, SomeTimerAtQuietStable DEFS ClockAt, ClockRegion
<1> QED
  BY <1>now, <1>tm, <1>wle DEFS ClockAt, ClockRegion

\* ---- WF1 on Tick ---------------------------------------------------------
LEMMA BoxTickActLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat
  PROVE  [](  RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ <<Tick>>_vars
              => ClockGoal(t, n)'  )
<1>1. RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ <<Tick>>_vars
        => ClockGoal(t, n)'
  BY TickReachesClockGoal DEFS ClockGoal, NZCore, RecurInv, TickRegion
<1> QED
  BY <1>1, PTL

LEMMA BoxTickEnabledLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat
  PROVE  [](RecurInv /\ TickRegion(t, n) => ENABLED <<Tick>>_vars)
<1>1. RecurInv /\ TickRegion(t, n) => ENABLED <<Tick>>_vars
  BY TickEnabledInClockRegion DEFS ClockAt, NZCore, RecurInv, TickRegion
<1> QED
  BY <1>1, PTL

LEMMA BoxTickStabLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat
  PROVE  [](  RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ [Next]_vars
              => TickRegion(t, n)' \/ ClockGoal(t, n)'  )
<1>1. RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ [Next]_vars
        => TickRegion(t, n)' \/ ClockGoal(t, n)'
  BY ClockWorkNat, ClockWorkPrimedNat, ClockWorkQuietMono, NowStaysUnlessTick, OldSetQuietMono, QuiescentQuietStep, SomeTimerAtQuietStable, TickReachesClockGoal
  DEFS ClockAt, ClockGoal, ClockRegion, NZCore, QuietStep, RecurInv, TickRegion
<1> QED
  BY <1>1, PTL

THEOREM TickPaysDistance ==
  ASSUME Spec, NEW t \in Nat, NEW n \in Nat
  PROVE  (RecurInv /\ TickRegion(t, n)) ~> ClockGoal(t, n)
<1>inv. []RecurInv
  BY RecurInvThm
<1>both. [](RecurInv /\ RecurInv')
  BY <1>inv, PTL
<1>nx. [][Next]_vars
  BY DEF Spec
<1>wf. WF_vars(Tick)
  BY DEF Spec, Fairness
<1>a. [](  RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ <<Tick>>_vars
           => ClockGoal(t, n)'  )
  BY BoxTickActLeg
<1>e. [](RecurInv /\ TickRegion(t, n) => ENABLED <<Tick>>_vars)
  BY BoxTickEnabledLeg
<1>s. [](  RecurInv /\ RecurInv' /\ TickRegion(t, n) /\ [Next]_vars
           => TickRegion(t, n)' \/ ClockGoal(t, n)'  )
  BY BoxTickStabLeg
<1> QED
  BY <1>a, <1>both, <1>e, <1>nx, <1>s, <1>wf, PTL

\* ---- WF1 on Deliver(c), the frontier drain -------------------------------
LEMMA BoxDrainActLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat, NEW c \in Honest
  PROVE  [](  RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ <<Deliver(c)>>_vars
              => ClockGoal(t, n)'  )
<1>1. RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ <<Deliver(c)>>_vars
        => ClockGoal(t, n)'
  BY DrainReachesClockGoal DEFS ClockGoal, DrainRegion, NZCore, RecurInv
<1> QED
  BY <1>1, PTL

LEMMA BoxDrainEnabledLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat, NEW c \in Honest
  PROVE  [](RecurInv /\ DrainRegion(t, n, c) => ENABLED <<Deliver(c)>>_vars)
<1>1. RecurInv /\ DrainRegion(t, n, c) => ENABLED <<Deliver(c)>>_vars
  BY EnabledDeliver DEFS DrainRegion, NZCore, OldPending, RecurInv, sent
<1> QED
  BY <1>1, PTL

LEMMA BoxDrainStabLeg ==
  ASSUME NEW t \in Nat, NEW n \in Nat, NEW c \in Honest
  PROVE  [](  RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ [Next]_vars
              => DrainRegion(t, n, c)' \/ ClockGoal(t, n)'  )
<1>1. RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ [Next]_vars
        => DrainRegion(t, n, c)' \/ ClockGoal(t, n)'
  BY ClockWorkNat, ClockWorkPrimedNat, ClockWorkQuietMono, DrainReachesClockGoal, NowStaysUnlessTick, OldPendingQuietStable, QuiescentQuietStep, SomeTimerAtQuietStable, TickReachesClockGoal
  DEFS ClockAt, ClockGoal, ClockRegion, DrainRegion, NZCore, QuietStep, RecurInv
<1> QED
  BY <1>1, PTL

THEOREM DrainPaysFrontierAt ==
  ASSUME Spec, NEW t \in Nat, NEW n \in Nat, NEW c \in Honest
  PROVE  (RecurInv /\ DrainRegion(t, n, c)) ~> ClockGoal(t, n)
<1>inv. []RecurInv
  BY RecurInvThm
<1>both. [](RecurInv /\ RecurInv')
  BY <1>inv, PTL
<1>nx. [][Next]_vars
  BY DEF Spec
<1>wf. WF_vars(Deliver(c))
  BY DEF Spec, Fairness
<1>a. [](  RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ <<Deliver(c)>>_vars
           => ClockGoal(t, n)'  )
  BY BoxDrainActLeg
<1>e. [](RecurInv /\ DrainRegion(t, n, c) => ENABLED <<Deliver(c)>>_vars)
  BY BoxDrainEnabledLeg
<1>s. [](  RecurInv /\ RecurInv' /\ DrainRegion(t, n, c) /\ [Next]_vars
           => DrainRegion(t, n, c)' \/ ClockGoal(t, n)'  )
  BY BoxDrainStabLeg
<1> QED
  BY <1>a, <1>both, <1>e, <1>nx, <1>s, <1>wf, PTL

LEMMA DrainRegionCommute ==
  ASSUME NEW t \in Nat, NEW n \in Nat, NEW TEMPORAL D,
         \A c \in Honest : []((RecurInv /\ DrainRegion(t, n, c)) => D)
  PROVE  [](\A c \in Honest : ((RecurInv /\ DrainRegion(t, n, c)) => D))
OBVIOUS

LEMMA DrainRegionBoxFO ==
  ASSUME NEW t \in Nat, NEW n \in Nat
  PROVE  [](  (\A c \in Honest :
                 ((RecurInv /\ DrainRegion(t, n, c)) => <>ClockGoal(t, n)))
              => ((\E c \in Honest : RecurInv /\ DrainRegion(t, n, c))
                    => <>ClockGoal(t, n))  )
<1>1. (\A c \in Honest :
         ((RecurInv /\ DrainRegion(t, n, c)) => <>ClockGoal(t, n)))
       => ((\E c \in Honest : RecurInv /\ DrainRegion(t, n, c))
            => <>ClockGoal(t, n))
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM DrainPaysFrontier ==
  ASSUME Spec, NEW t \in Nat, NEW n \in Nat
  PROVE  (\E c \in Honest : RecurInv /\ DrainRegion(t, n, c)) ~> ClockGoal(t, n)
<1>1. \A c \in Honest :
        []((RecurInv /\ DrainRegion(t, n, c)) => <>ClockGoal(t, n))
  <2> SUFFICES ASSUME NEW c \in Honest
               PROVE  []((RecurInv /\ DrainRegion(t, n, c)) => <>ClockGoal(t, n))
    OBVIOUS
  <2>1. (RecurInv /\ DrainRegion(t, n, c)) ~> ClockGoal(t, n)
    BY DrainPaysFrontierAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A c \in Honest :
           ((RecurInv /\ DrainRegion(t, n, c)) => <>ClockGoal(t, n)))
  BY <1>1, DrainRegionCommute
<1> QED
  BY <1>2, DrainRegionBoxFO, PTL

\* ---- The rank staircase --------------------------------------------------
LEMMA BoxClockRankSplit ==
  ASSUME NEW t \in Nat, NEW n \in Nat
  PROVE  [](  RecurInv /\ ClockAt(t, n + 1)
              => (RecurInv /\ TickRegion(t, n))
                 \/ (\E c \in Honest : RecurInv /\ DrainRegion(t, n, c))  )
<1>1. RecurInv /\ ClockAt(t, n + 1)
        => (RecurInv /\ TickRegion(t, n))
           \/ (\E c \in Honest : RecurInv /\ DrainRegion(t, n, c))
  BY DEFS DrainRegion, OldPendingSet, TickRegion
<1> QED
  BY <1>1, PTL

THEOREM ClockRankProgress ==
  ASSUME Spec, NEW t \in Nat, NEW n \in Nat
  PROVE  (RecurInv /\ ClockAt(t, n + 1)) ~> ClockGoal(t, n)
<1>1. (RecurInv /\ TickRegion(t, n)) ~> ClockGoal(t, n)
  BY TickPaysDistance
<1>2. (\E c \in Honest : RecurInv /\ DrainRegion(t, n, c)) ~> ClockGoal(t, n)
  BY DrainPaysFrontier
<1>3. [](  RecurInv /\ ClockAt(t, n + 1)
           => (RecurInv /\ TickRegion(t, n))
              \/ (\E c \in Honest : RecurInv /\ DrainRegion(t, n, c))  )
  BY BoxClockRankSplit
<1> QED
  BY <1>1, <1>2, <1>3, PTL

\* Rank 0 is unreachable inside the region: the clock is short of t, so the
\* distance alone is worth |Honest| + 1.
LEMMA BoxClockRankZero ==
  ASSUME NEW t \in Nat
  PROVE  [](RecurInv /\ ClockAt(t, 0) => ~HonestQuiescent)
<1>1. RecurInv /\ ClockAt(t, 0) => ~HonestQuiescent
  BY BurstBoundNat, MultMono, OldCountFacts DEFS ClockAt, ClockRegion, ClockWork, NZCore, RecurInv, TickDeficit, TypeOK
<1> QED
  BY <1>1, PTL

THEOREM ClockRegionBreaksAt ==
  ASSUME Spec, NEW t \in Nat
  PROVE  \A n \in Nat : ((RecurInv /\ ClockAt(t, n)) ~> ~HonestQuiescent)
<1>inv. []RecurInv
  BY RecurInvThm
<1>tr. [](RecurInv /\ TimerReached(t) => ~HonestQuiescent)
  BY BoxTimerReachedBreaks
<1> DEFINE R(n) == (RecurInv /\ ClockAt(t, n)) ~> ~HonestQuiescent
<1>0. R(0)
  <2>1. [](RecurInv /\ ClockAt(t, 0) => ~HonestQuiescent)
    BY BoxClockRankZero
  <2> QED
    BY <2>1, PTL DEF R
<1>step. \A n \in Nat : R(n) => R(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME R(n) PROVE R(n + 1)
    OBVIOUS
  <2>1. (RecurInv /\ ClockAt(t, n + 1)) ~> ClockGoal(t, n)
    BY ClockRankProgress
  <2> QED
    BY <1>inv, <1>tr, <2>1, PTL DEFS ClockGoal, R
<1>all. \A n \in Nat : R(n)
  <2> HIDE DEF R
  <2> QED
    BY <1>0, <1>step, NatInduction, IsaM("blast")
<1> QED
  BY <1>all DEF R

\* ---- Existential lifts: over the rank, then over the deadline ------------
LEMMA BoxClockRegionExN ==
  ASSUME NEW t \in Nat
  PROVE  [](  RecurInv /\ ClockRegion(t)
              => (\E n \in Nat : RecurInv /\ ClockAt(t, n))  )
<1>1. RecurInv /\ ClockRegion(t) => (\E n \in Nat : RecurInv /\ ClockAt(t, n))
  BY ClockWorkNat DEFS ClockAt, NZCore, RecurInv
<1> QED
  BY <1>1, PTL

LEMMA ClockAtCommute ==
  ASSUME NEW t \in Nat, NEW TEMPORAL D,
         \A n \in Nat : []((RecurInv /\ ClockAt(t, n)) => D)
  PROVE  [](\A n \in Nat : ((RecurInv /\ ClockAt(t, n)) => D))
OBVIOUS

LEMMA ClockAtBoxFO ==
  ASSUME NEW t \in Nat
  PROVE  [](  (\A n \in Nat :
                 ((RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent))
              => ((\E n \in Nat : RecurInv /\ ClockAt(t, n))
                    => <>~HonestQuiescent)  )
<1>1. (\A n \in Nat : ((RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent))
       => ((\E n \in Nat : RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent)
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM ClockRegionBreaksT ==
  ASSUME Spec, NEW t \in Nat
  PROVE  (RecurInv /\ ClockRegion(t)) ~> ~HonestQuiescent
<1>1. \A n \in Nat : []((RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent)
  <2> SUFFICES ASSUME NEW n \in Nat
               PROVE  []((RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent)
    OBVIOUS
  <2>1. (RecurInv /\ ClockAt(t, n)) ~> ~HonestQuiescent
    BY ClockRegionBreaksAt
  <2> QED
    BY <2>1, PTL
<1>2. [](\A n \in Nat : ((RecurInv /\ ClockAt(t, n)) => <>~HonestQuiescent))
  BY <1>1, ClockAtCommute
<1>3. (\E n \in Nat : RecurInv /\ ClockAt(t, n)) ~> ~HonestQuiescent
  BY <1>2, ClockAtBoxFO, PTL
<1>4. [](  RecurInv /\ ClockRegion(t)
           => (\E n \in Nat : RecurInv /\ ClockAt(t, n))  )
  BY BoxClockRegionExN
<1> QED
  BY <1>3, <1>4, PTL

LEMMA ClockRegionCommute ==
  ASSUME NEW TEMPORAL D,
         \A t \in Nat : []((RecurInv /\ ClockRegion(t)) => D)
  PROVE  [](\A t \in Nat : ((RecurInv /\ ClockRegion(t)) => D))
OBVIOUS

LEMMA ClockRegionBoxFO ==
  [](  (\A t \in Nat : ((RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent))
       => ((\E t \in Nat : RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent)  )
<1>1. (\A t \in Nat : ((RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent))
       => ((\E t \in Nat : RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent)
  OBVIOUS
<1> QED
  BY <1>1, PTL

LEMMA BoxClockRegionSplit ==
  [](  RecurInv /\ (\E t \in Nat : ClockRegion(t))
       => (\E t \in Nat : RecurInv /\ ClockRegion(t))  )
<1>1. RecurInv /\ (\E t \in Nat : ClockRegion(t))
        => (\E t \in Nat : RecurInv /\ ClockRegion(t))
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM ClockRegionBreaks ==
  ASSUME Spec
  PROVE  (RecurInv /\ (\E t \in Nat : ClockRegion(t))) ~> ~HonestQuiescent
<1>1. \A t \in Nat : []((RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent)
  <2> SUFFICES ASSUME NEW t \in Nat
               PROVE  []((RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent)
    OBVIOUS
  <2>1. (RecurInv /\ ClockRegion(t)) ~> ~HonestQuiescent
    BY ClockRegionBreaksT
  <2> QED
    BY <2>1, PTL
<1>2. [](\A t \in Nat : ((RecurInv /\ ClockRegion(t)) => <>~HonestQuiescent))
  BY <1>1, ClockRegionCommute
<1>3. (\E t \in Nat : RecurInv /\ ClockRegion(t)) ~> ~HonestQuiescent
  BY <1>2, ClockRegionBoxFO, PTL
<1>4. [](  RecurInv /\ (\E t \in Nat : ClockRegion(t))
           => (\E t \in Nat : RecurInv /\ ClockRegion(t))  )
  BY BoxClockRegionSplit
<1> QED
  BY <1>3, <1>4, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* THE FRONTIER, ASSEMBLED.                                                *)
(***************************************************************************)

\* Either some correct validator is waiting on a live timer, or nothing is
\* pending for it and Layers 1 and 2 hand a Deliverable validator its
\* certificate. If neither held, the state would be quiescent with
\* ~TickUseful, which QuiescentDeadlockDecides turns into a decision.
LEMMA BoxQuiescentSplit ==
  [](  RecurInv /\ ~SomeCorrectDecided /\ HonestQuiescent
       => (\E t \in Nat : ClockRegion(t))
          \/ (\E c \in Honest : DeliverRegion(c))  )
<1>1. RecurInv /\ ~SomeCorrectDecided /\ HonestQuiescent
        => (\E t \in Nat : ClockRegion(t))
           \/ (\E c \in Honest : DeliverRegion(c))
  BY QuiescentTailWitness, UnstuckCanCompute
  DEFS ClockRegion, DeliverRegion, NoLiveTimer, NZCore, OFF, RecurInv, SomeTimerAt, TypeOK, Unstuck
<1> QED
  BY <1>1, PTL

THEOREM QuiescenceBreaks ==
  ASSUME Spec, []~SomeCorrectDecided
  PROVE  (RecurInv /\ HonestQuiescent) ~> ~HonestQuiescent
<1>inv. []RecurInv
  BY RecurInvThm
<1>nd. []~SomeCorrectDecided
  OBVIOUS
<1>1. (RecurInv /\ (\E t \in Nat : ClockRegion(t))) ~> ~HonestQuiescent
  BY ClockRegionBreaks
<1>2. (RecurInv /\ (\E c \in Honest : DeliverRegion(c))) ~> ~HonestQuiescent
  BY DeliverRegionBreaks
<1>3. [](  RecurInv /\ ~SomeCorrectDecided /\ HonestQuiescent
           => (\E t \in Nat : ClockRegion(t))
              \/ (\E c \in Honest : DeliverRegion(c))  )
  BY BoxQuiescentSplit
<1> QED
  BY <1>1, <1>2, <1>3, <1>inv, <1>nd, PTL

\* While no correct validator has decided, honest steps recur: a live guard
\* fires one (Branch A), and quiescence always breaks (Branches B and C).
THEOREM NoDecisionStepsRecur ==
  ASSUME Spec, []~SomeCorrectDecided
  PROVE  []<><<HonestAct>>_vars
<1>inv. []RecurInv
  BY RecurInvThm
<1>1. (RecurInv /\ ~HonestQuiescent) ~> <<HonestAct>>_vars
  BY GuardedHonestStep
<1>2. (RecurInv /\ HonestQuiescent) ~> ~HonestQuiescent
  BY QuiescenceBreaks
<1>3. (RecurInv /\ HonestQuiescent) ~> (RecurInv /\ ~HonestQuiescent)
  BY <1>2, <1>inv, PTL
<1>4. RecurInv ~> <<HonestAct>>_vars
  BY <1>1, <1>3, PTL
<1> QED
  BY <1>4, <1>inv, PTL

\* ---- The frontier -------------------------------------------------------
\* Only the SomeCorrectDecided conjunct of the caller's []~Won(b) is used:
\* the round bound plays no part in keeping the correct validators moving.
THEOREM HonestStepsRecur ==
  ASSUME Spec, NEW b \in Rounds, []~Won(b)
  PROVE  []<><<HonestAct>>_vars
<1>1. [](Won(b) <=> (SomeCorrectDecided \/ RoundAbove(Bnd(b))))
  BY BoxWonSplit
<1>2. []~SomeCorrectDecided
  BY <1>1, PTL
<1> QED
  BY <1>2, NoDecisionStepsRecur

\* ---- The staircase: bounded work versus recurring honest steps -----------
THEOREM RoundGrowth ==
  ASSUME Spec, NEW b \in Rounds
  PROVE  <>SomeCorrectDecided \/ <>RoundAbovePastGST(b)
<1>reg. []RegOK(b)
  BY BoxRegOK, BurstFactsInv, DecidedStepBox, DecidedStepInv, InvProof, PTL, RoundBelowNowInv DEF Inv
<1>split. [](Won(b) <=> (SomeCorrectDecided \/ RoundAbove(Bnd(b))))
  BY BoxWonSplit
<1>past. [](TypeOK /\ RoundAbove(Bnd(b)) => RoundAbovePastGST(b))
  BY BoxBndAbovePastGST
<1>ty. []TypeOK
  BY InvProof, PTL DEF Inv
<1>3. <>Won(b)
  <2> SUFFICES ASSUME []~Won(b) PROVE FALSE
    BY PTL
  <2>step. [][RegStep(b)]_vars
    BY <1>reg, PTL DEFS RegStep, Spec
  <2>rec. []<><<HonestAct>>_vars
    BY HonestStepsRecur
  <2> DEFINE P(n) == []~WorkLess(b, n)
  <2>0. P(0)
    <3>1. []~WorkLess(b, 0)
      BY <1>reg, BoxWorkNonNeg, PTL
    <3> QED
      BY <3>1 DEF P
  <2>ind. ASSUME NEW n \in Nat, P(n) PROVE P(n + 1)
    <3>n. n \in Int
      OBVIOUS
    <3>1. [](WorkLess(b, n + 1) /\ [RegStep(b)]_vars => (WorkLess(b, n + 1))')
      BY <3>n, BoxWorkNonIncrease
    <3>2. [](  WorkLess(b, n + 1) /\ [RegStep(b)]_vars /\ <<HonestAct>>_vars
               => (WorkLess(b, n))'  )
      BY <3>n, BoxWorkDrop
    <3> QED
      BY <2>ind, <3>1, <3>2, <2>step, <2>rec, PTL DEF P
  <2>all. \A n \in Nat : P(n)
    <3> HIDE DEF P
    <3> QED
      BY <2>0, <2>ind, NatInduction, IsaM("blast")
  <2>now. \A n \in Nat : ~WorkLess(b, n)
    <3> TAKE n \in Nat
    <3>1. []~WorkLess(b, n)
      BY <2>all DEF P
    <3> QED
      BY <3>1, PTL
  <2>wn0. RegOK(b)
    BY <1>reg, PTL
  <2>wn. Work(b) \in Nat
    BY <2>wn0, WorkNat DEF RegOK
  <2> QED
    BY <2>now, <2>wn DEF WorkLess
<1> QED
  BY <1>3, <1>split, <1>past, <1>ty, PTL

\* ---- Layer 0, assembled: ProgressBeyond from round growth ----------------
THEOREM PostGSTRoundProgress == ASSUME Spec PROVE ProgressBeyond
<1> SUFFICES ASSUME Spec, NEW b \in Rounds
             PROVE  <>SomeCorrectDecided \/ <>(now > GST /\ RoundAbove(b))
  BY DEF ProgressBeyond
<1>1. <>SomeCorrectDecided \/ <>RoundAbovePastGST(b)
  BY RoundGrowth
<1>2. [](TypeOK /\ RoundBelowNow)
  BY InvProof, RoundBelowNowInv, PTL DEF Inv
<1>3. [](  TypeOK /\ RoundBelowNow /\ RoundAbovePastGST(b)
           => (now > GST /\ RoundAbove(b))  )
  BY BoxRoundAboveGST
<1> QED
  BY <1>1, <1>2, <1>3, PTL

-----------------------------------------------------------------------------
(***********************************************************************)
(* THE WINDOW LEMMA. Established: LateValueLockWindowInv, no admission.*)
(*                                                                     *)
(*  This section owns the timing ceiling that closes the lock retry. See   *)
(*  ADR 0002. It lives HERE rather than in ...LockRetry because the        *)
(*  argument runs through RoundBacked and needs the clock and timer        *)
(*  apparatus already in this module. ...LockRetry consumes only the       *)
(*  finished statement, together with its own proved                       *)
(*  DisruptionRoundCeiling.                                                *)
(*                                                                     *)
(*   Claim: a correct validator cannot value-precommit at its OWN round lr *)
(*   at an instant when another correct validator has already entered a    *)
(*   round above lr. Two escapes remain. The precommit timeout of round lr *)
(*   fits inside one delivery delay, or round lr itself lies below GST.    *)
(*   Either disjunct is a CONSTANT ceiling on lr. TimeoutPrecommit is      *)
(*   affine, with a strictly positive increment, so the first disjunct     *)
(*   gives lr <= Delta. A constant ceiling is all that the retry needs,    *)
(*   because the disruptive lock rounds strictly increase.                 *)
(*                                                                     *)
(*  THE lr < GST DISJUNCT IS NOT SLACK. Without it the statement is FALSE, *)
(*  and TLC refutes it. The scenario "window-gst" of ...WithinRoundMC,     *)
(*  with ...WithinRoundWindowGst.cfg at GST = 4, Delta = 2 and T0Precommit *)
(*  = 3, reaches a state at now = 5. There h1 has just entered round 1.    *)
(*  Every correct lock round is still -1, so Lemma5Hyp("h1", 1) holds. h3  *)
(*  is still in round 0, and it value-precommits at round 0 in that same   *)
(*  instant, against TimeoutPrecommit(0) = 3 > Delta = 2.                  *)
(*                                                                     *)
(*   The cause is DeliveryDeadline(m), which is max(sentTime[m], GST) +    *)
(*   Delta. A message that is sent BEFORE GST can be withheld until GST +  *)
(*   Delta, whatever its send time. One correct validator can therefore be *)
(*   held short of a quorum for an unbounded stretch. Another validator    *)
(*   that is served at once runs through its timeouts and gets ahead.      *)
(*   Every step below of the form "reaches c within Delta" therefore       *)
(*   carries its own guard >= GST. When that guard fails, the escape is    *)
(*   exactly lr < GST, by the two invariants at the end of this section    *)
(*   that date the votes.                                                  *)
(*                                                                     *)
(*    Shape of the argument. Everything reduces to ONE inequality, t_lock  *)
(*    <= s_x + Delta. Here t_lock = sentTime[Precommit(c, lr, w)] is the   *)
(*    lock instant. And s_x is the send time of the own round-lr precommit *)
(*    of ANY correct validator x, subject to s_x >= GST. Three cases on    *)
(*    how x precommitted at lr, one per emitting action (PrecommitBacked   *)
(*    names them), and all three land on it. (a) x precommitted nil        *)
(*    through OnTimeoutPrevote. Then x armed at arm_x = s_x -              *)
(*    TimeoutPrevote(lr), and it held an ANY-value prevote quorum of 2f+1  *)
(*    at lr. Those prevotes are therefore in `sent` by arm_x. Also arm_x   *)
(*    >= GST, so c holds them by arm_x + Delta. c is armed too, so t_lock  *)
(*    <= arm_c + TimeoutPrevote(lr) <= s_x + Delta. The TimeoutPrevote(lr) *)
(*    terms cancel HERE. (b) x value-precommitted at lr. Then x held a     *)
(*    polka and the proposal, and both are in `sent` by s_x. c therefore   *)
(*    holds them by s_x + Delta, and CanCompute(c) holds. Tick cannot      *)
(*    carry the clock further while c is still in step "prevote". t_lock   *)
(*    <= s_x + Delta directly, with no timeout spent. (c) x precommitted   *)
(*    nil through OnPrevoteQuorumNil. IMPOSSIBLE, not bounded: x held a    *)
(*    2f+1 polka for nil at lr and c a 2f+1 polka for w in Values at lr.   *)
(*    The two share a correct validator, and a correct validator prevotes  *)
(*    at most once per round, so nil would equal w. That inequality is     *)
(*    item F, LateLockDelivery at the end of this section, and everything  *)
(*    composes around it in checked arithmetic, at GapFromDelivery.        *)
(*                                                                     *)
(*  RoundBacked does NOT supply the crossing bound. It is UNTIMED. It puts *)
(*  a quorum for lr in `sent` at the CURRENT state, with no bound on       *)
(*  sentTime. What is needed is the quorum in `sent` a full                *)
(*  TimeoutPrecommit(lr) BEFORE enteredAt[p][r]. That is CrossingBacked,   *)
(*  proved below.                                                          *)
(*                                                                     *)
(*  BUILD ITEMS, all PROVED. (A) GossipDeadline, the Gossip property as an *)
(*  invariant. (B) PrecommitArmedQuorumTimed and (C)                       *)
(*  PrevoteArmedQuorumTimed. While a timer is ARMED, its own VALUE is the  *)
(*  dated arming instant, because timer[q]["precommit"] = arm_q +          *)
(*  TimeoutPrecommit(round[q]). No latch is therefore necessary, and no    *)
(*  new history component is. (D) PrevoteOncePerRound, for case (c). (E)   *)
(*  CrossingBacked, the dated certificate below enteredAt[p][r]. (F)       *)
(*  LateLockDelivery, the three-case bound, resting on LockWindowCore. (G) *)
(*  GapFromDelivery and LateValueLockWindowInv, the composition.           *)
(***********************************************************************)
LateValueLockGap ==
  \A c \in Honest, w \in Values, lr \in Rounds, p \in Honest, r \in Rounds :
    ( /\ lr < r
      /\ enteredAt[p][r] # OFF
      /\ enteredAt[p][r] > GST
      /\ Precommit(c, lr, w) \in sent )
    => \/ sentTime[Precommit(c, lr, w)] + TimeoutPrecommit(lr)
             <= enteredAt[p][r] + Delta
       \/ lr < GST

LateValueLockWindow ==
  \A c \in Honest, w \in Values, lr \in Rounds, p \in Honest, r \in Rounds :
    ( /\ lr < r
      /\ enteredAt[p][r] # OFF
      /\ enteredAt[p][r] > GST
      /\ Precommit(c, lr, w) \in sent
      /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r] )
    => TimeoutPrecommit(lr) <= Delta \/ lr < GST

\*  Build item (1), the UPPER bound. While a correct validator sits in step
\*  "prevote" with its prevote timer armed, the clock cannot have passed that
\*  deadline. now >= timer[c]["prevote"] would enable OnTimeoutPrevote. That
\*  would make CanCompute(c) true, and it would block Tick. TimerLive(c,
\*  "prevote") is exactly the step-"prevote" side condition, so a dead timer
\*  left behind does not block.
\*
\*   ---- The helper the induction needs
\*   -------------------------------------- A validator in step "propose" has
\*   NO armed prevote timer. Without it the three actions from propose to
\*   prevote stay open. They are OnTimeoutPropose, OnProposalNoPOL and
\*   OnProposalWithPOL. Each one moves step INTO "prevote", and it leaves the
\*   prevote timer alone. The conclusion would then be needed at a c whose
\*   PRE-state does not satisfy the hypothesis step[c] = "prevote". The
\*   induction hypothesis says nothing there. With the helper those three
\*   cases are vacuous instead. The helper itself is immediate. The only
\*   writer that arms the prevote timer is ScheduleTimeoutPrevote, and its
\*   guard is step[p] = "prevote". Only two actions enter step "propose",
\*   which are OnTimeoutPrecommit and SkipRound, and both clear the timer
\*   through ResetTimersFor.
ProposeStepPrevoteOff ==
  \A c \in Honest : step[c] = "propose" => timer[c]["prevote"] = OFF

LEMMA ProposeStepPrevoteOffStepL ==
  ASSUME TypeOK, [Next]_vars, ProposeStepPrevoteOff
  PROVE  ProposeStepPrevoteOff'
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
  OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
  OnTimeoutPrevote, OnTimeoutPropose, Propose, ProposeStepPrevoteOff, ResetTimersFor,
  ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TimerType, TypeOK, vars

THEOREM ProposeStepPrevoteOffInv == ASSUME Spec PROVE []ProposeStepPrevoteOff
<1>1. ProposeStepPrevoteOff
  BY DEFS Init, ProposeStepPrevoteOff, Spec, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ProposeStepPrevoteOff => ProposeStepPrevoteOff')
  BY <1>2, ProposeStepPrevoteOffStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- The deadline invariant ----------------------------------------------
PrevoteDeadlineNotPassed ==
  \A c \in Honest :
    (step[c] = "prevote" /\ timer[c]["prevote"] # OFF)
      => now <= timer[c]["prevote"]

LEMMA PrevoteDeadlineNotPassedStepL ==
  ASSUME TypeOK, [Next]_vars, ProposeStepPrevoteOff, PrevoteDeadlineNotPassed
  PROVE  PrevoteDeadlineNotPassed'
BY T0PrevoteType, TDeltaType
DEFS Broadcast, CanCompute, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrevoteDeadlineNotPassed, Propose, ProposeStepPrevoteOff, ResetTimersFor, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TimeoutPrevote, TimerType, TypeOK, vars

THEOREM PrevoteDeadlineNotPassedInv == ASSUME Spec PROVE []PrevoteDeadlineNotPassed
<1>1. PrevoteDeadlineNotPassed
  BY DEFS Init, PrevoteDeadlineNotPassed, Spec
<1>2. [](TypeOK /\ ProposeStepPrevoteOff /\ [Next]_vars)
  BY InvProof, ProposeStepPrevoteOffInv, PTL DEF Spec, Inv
<1>3. [](PrevoteDeadlineNotPassed => PrevoteDeadlineNotPassed')
  BY <1>2, PrevoteDeadlineNotPassedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Item A: the Gossip property as an INVARIANT --------------------------
\* Base's DeliverWithinDelta is a LEADS-TO, which is the wrong shape for a
\* state-predicate argument, so the delivery bound is re-derived here as an
\* ordinary invariant. Tick's own third conjunct IS this predicate at the
\* post-state, so the clock can never reach a pending message's deadline.
\* Consumed as: a post-GST message sits in EVERY correct validator's rcvd once
\* the clock reaches sentTime + Delta.
GossipDeadline ==
  \A pm \in PendingDeliveries : now < DeliveryDeadline(pm[2])

LEMMA GossipDeadlineStepL ==
  ASSUME TypeOK, [Next]_vars, GossipDeadline
  PROVE  GossipDeadline'
BY DeltaType, GSTType, RcvdMonotoneStep, SentTimeStep
DEFS Broadcast, Deliver, DeliveryDeadline, FaultyStep, GossipDeadline, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PendingDeliveries, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

THEOREM GossipDeadlineInv == ASSUME Spec PROVE []GossipDeadline
<1>1. GossipDeadline
  BY DEFS GossipDeadline, Init, OFF, PendingDeliveries, sent, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](GossipDeadline => GossipDeadline')
  BY <1>2, GossipDeadlineStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Item D: one prevote per correct validator per round ------------------
\* Case (c) of the window argument: a nil polka and a value polka at the same
\* round would need 2f+2 correct validators. That counting needs this, and
\* nothing of the shape exists in the tree.
\*
\*  The whole content is the SentInv of ...Base. Its second conjunct says that
\*  a prevote already in `sent`, at the CURRENT round of its correct sender,
\*  forces step[sender] # "propose". All three actions that emit a prevote are
\*  guarded by step = "propose". So the second prevote can never be emitted.
PrevoteOncePerRound ==
  \A c \in Honest, r \in Rounds, v1 \in ValuesOrNil, v2 \in ValuesOrNil :
    (Prevote(c, r, v1) \in sent /\ Prevote(c, r, v2) \in sent) => v1 = v2

\*  Which action can activate a Prevote authored by a CORRECT validator: only
\*  the three step-"propose" exits, and each broadcasts at the sender's OWN
\*  current round. The emitting action has to be named, to reach its guard.
\*  That is the whole difficulty of item D, and a bundled leaf over Next does
\*  not discharge it.
LEMMA FreshHonestPrevoteEmitter ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Prevote", mm.sender \in Honest
  PROVE  step[mm.sender] = "propose" /\ mm.round = round[mm.sender]
BY DEFS Broadcast, Deliver, FaultyStep, Honest, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Precommit, Prevote, Proposal, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

LEMMA PrevoteOncePerRoundStepL ==
  ASSUME TypeOK, SentInv, [Next]_vars, PrevoteOncePerRound
  PROVE  PrevoteOncePerRound'
BY FreshHonestPrevoteEmitter, SentTimeStep
DEFS Honest, HonestSentOK, Message, Prevote, PrevoteMsg, PrevoteOncePerRound, sent, SentInv, TypeOK

THEOREM PrevoteOncePerRoundInv == ASSUME Spec PROVE []PrevoteOncePerRound
<1>1. PrevoteOncePerRound
  BY DEFS Init, OFF, PrevoteOncePerRound, sent, Spec
<1>2. [](TypeOK /\ SentInv /\ [Next]_vars)
  BY InvProof, SentInvInv, PTL DEF Spec, Inv
<1>3. [](PrevoteOncePerRound => PrevoteOncePerRound')
  BY <1>2, PrevoteOncePerRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Canonical form of a vote already in the pool -------------------------
\* Sharper than SentPrecommitCanonical / SentPrevoteCanonical above: an
\* EQUALITY, so it transports the timestamp too and not just membership.
LEMMA SentPrecommitIsCanonical ==
  ASSUME TypeOK, NEW m, m \in sent, m.type = "Precommit"
  PROVE  m = Precommit(m.sender, m.round, m.valueID) /\ m.valueID \in ValuesOrNil
BY DEFS Message, Precommit, PrecommitMsg, PrevoteMsg, ProposalMsg, sent, TypeOK, ValuesOrNil

LEMMA SentPrevoteIsCanonical ==
  ASSUME TypeOK, NEW m, m \in sent, m.type = "Prevote"
  PROVE  m = Prevote(m.sender, m.round, m.valueID) /\ m.valueID \in ValuesOrNil
BY DEFS Message, Prevote, PrecommitMsg, PrevoteMsg, ProposalMsg, sent, TypeOK, ValuesOrNil

\*  ---- Items B and C: the arming instant is readable from the timer
\*  --------- THE POINT OF THE WHOLE ROUTE. While a timer is ARMED its own
\*  VALUE dates the instant it was armed, because the only writer sets it to
\*  now + TimeoutX(round[q]). The quorum that justified the arming can
\*  therefore be dated WITHOUT a history variable.
PrecommitArmedQuorumTimed ==
  \A q \in Honest : timer[q]["precommit"] # OFF =>
    \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
      /\ Precommit(s, round[q], v) \in sent
      /\ sentTime[Precommit(s, round[q], v)]
           <= timer[q]["precommit"] - TimeoutPrecommit(round[q])

PrevoteArmedQuorumTimed ==
  \A q \in Honest : timer[q]["prevote"] # OFF =>
    \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
      /\ Prevote(s, round[q], v) \in sent
      /\ sentTime[Prevote(s, round[q], v)]
           <= timer[q]["prevote"] - TimeoutPrevote(round[q])

\*  An any-value quorum in the OWN view of q is a dated certificate over the
\*  global pool. The vote of each member is in `sent`, with a timestamp at or
\*  below the current clock.
LEMMA ArmedPrecommitCertifiesTimed ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, NEW q \in Honest, NEW rr,
         RExistsAnyPrecommitQuorum(q, rr)
  PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
           /\ Precommit(s, rr, v) \in sent
           /\ sentTime[Precommit(s, rr, v)] <= now
BY SentPrecommitIsCanonical
DEFS OFF, RcvdSubsetSent, RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound, sent, SentTimeLeNow

LEMMA ArmedPrevoteCertifiesTimed ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, NEW q \in Honest, NEW rr,
         RExistsAnyPrevoteQuorum(q, rr)
  PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
           /\ Prevote(s, rr, v) \in sent
           /\ sentTime[Prevote(s, rr, v)] <= now
BY SentPrevoteIsCanonical DEFS OFF, RcvdSubsetSent, RExistsAnyPrevoteQuorum, RSendersOfTypeAtRound, sent, SentTimeLeNow

\* ---- Item B, the step lemma ----------------------------------------------
LEMMA PrecommitArmedQuorumTimedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, [Next]_vars,
         PrecommitArmedQuorumTimed
  PROVE  PrecommitArmedQuorumTimed'
<1> SUFFICES ASSUME NEW q \in Honest, timer'[q]["precommit"] # OFF
             PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                      /\ Precommit(s, round'[q], v) \in sent'
                      /\ sentTime'[Precommit(s, round'[q], v)]
                           <= timer'[q]["precommit"] - TimeoutPrecommit(round'[q])
  BY DEF PrecommitArmedQuorumTimed
<1>fz. SentTimeFrozenPred \/ vars' = vars
  BY SentTimeFrozenStepL
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
\* CARRY. With q's round and precommit deadline frozen, monotone `sent` plus
\* frozen timestamps move the dated certificate to the post-state verbatim.
<1>keep. (round'[q] = round[q] /\ timer'[q]["precommit"] = timer[q]["precommit"])
           => (\E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                 /\ Precommit(s, round'[q], v) \in sent'
                 /\ sentTime'[Precommit(s, round'[q], v)]
                      <= timer'[q]["precommit"] - TimeoutPrecommit(round'[q]))
  BY <1>fz, <1>mono DEFS OFF, PrecommitArmedQuorumTimed, sent, SentTimeFrozenPred, vars
<1>1. CASE \E p \in Honest : ScheduleTimeoutPrecommit(p)
  <2>1. PICK p \in Honest : ScheduleTimeoutPrecommit(p)
    BY <1>1
  <2>2. CASE q = p
    <3>1. /\ RExistsAnyPrecommitQuorum(q, round[q])
          /\ round'[q] = round[q]
          /\ timer'[q]["precommit"] = now + TimeoutPrecommit(round[q])
          /\ sent' = sent /\ sentTime' = sentTime
      BY <2>1, <2>2 DEFS ScheduleTimeoutPrecommit, sent, TimerType, TypeOK
    <3>2. TimeoutPrecommit(round[q]) \in Int /\ now \in Int
      BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit, TypeOK
    <3>3. timer'[q]["precommit"] - TimeoutPrecommit(round'[q]) = now
      BY <3>1, <3>2
    <3> QED
      BY <3>1, <3>3, ArmedPrecommitCertifiesTimed
  <2>3. CASE q # p
    BY <1>keep, <2>1, <2>3 DEFS ScheduleTimeoutPrecommit, TypeOK
  <2> QED
    BY <2>2, <2>3
\* A round change clears the timer through ResetTimersFor, so the antecedent
\* fails at the validator that moved.
<1>2. CASE \E p \in Honest : (OnTimeoutPrecommit(p) \/ \E r \in Rounds : SkipRound(p, r))
  BY <1>2, <1>keep
  DEFS OnTimeoutPrecommit, ResetTimersFor, SkipRound, TimerType, TypeOK
\* Everything else freezes both the round and the precommit slot: the other two
\* timer writes are at the "propose" and "prevote" slots.
<1>3. CASE /\ ~(\E p \in Honest : ScheduleTimeoutPrecommit(p))
           /\ ~(\E p \in Honest : (OnTimeoutPrecommit(p) \/ \E r \in Rounds : SkipRound(p, r)))
  BY <1>3, <1>keep
  DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrevote, Tick, TimerType, TypeOK, vars
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM PrecommitArmedQuorumTimedInv ==
  ASSUME Spec PROVE []PrecommitArmedQuorumTimed
<1>1. PrecommitArmedQuorumTimed
  BY DEFS Init, PrecommitArmedQuorumTimed, Spec, TimerType
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow /\ [Next]_vars)
  BY InvProof, SentInvInv, SentTimeLeNowInv, PTL DEF Spec, Inv
<1>3. [](PrecommitArmedQuorumTimed => PrecommitArmedQuorumTimed')
  BY <1>2, PrecommitArmedQuorumTimedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Item C, the step lemma ----------------------------------------------
\* Same shape as item B, with OnTimeoutPrevote joining the group that clears
\* the slot instead of the group that freezes it.
LEMMA PrevoteArmedQuorumTimedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, [Next]_vars,
         PrevoteArmedQuorumTimed
  PROVE  PrevoteArmedQuorumTimed'
<1> SUFFICES ASSUME NEW q \in Honest, timer'[q]["prevote"] # OFF
             PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                      /\ Prevote(s, round'[q], v) \in sent'
                      /\ sentTime'[Prevote(s, round'[q], v)]
                           <= timer'[q]["prevote"] - TimeoutPrevote(round'[q])
  BY DEF PrevoteArmedQuorumTimed
<1>fz. SentTimeFrozenPred \/ vars' = vars
  BY SentTimeFrozenStepL
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>keep. (round'[q] = round[q] /\ timer'[q]["prevote"] = timer[q]["prevote"])
           => (\E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                 /\ Prevote(s, round'[q], v) \in sent'
                 /\ sentTime'[Prevote(s, round'[q], v)]
                      <= timer'[q]["prevote"] - TimeoutPrevote(round'[q]))
  BY <1>fz, <1>mono DEFS OFF, PrevoteArmedQuorumTimed, sent, SentTimeFrozenPred, vars
<1>1. CASE \E p \in Honest : ScheduleTimeoutPrevote(p)
  <2>1. PICK p \in Honest : ScheduleTimeoutPrevote(p)
    BY <1>1
  <2>2. CASE q = p
    <3>1. /\ RExistsAnyPrevoteQuorum(q, round[q])
          /\ round'[q] = round[q]
          /\ timer'[q]["prevote"] = now + TimeoutPrevote(round[q])
          /\ sent' = sent /\ sentTime' = sentTime
      BY <2>1, <2>2 DEFS ScheduleTimeoutPrevote, sent, TimerType, TypeOK
    <3>2. TimeoutPrevote(round[q]) \in Int /\ now \in Int
      BY T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote, TypeOK
    <3>3. timer'[q]["prevote"] - TimeoutPrevote(round'[q]) = now
      BY <3>1, <3>2
    <3> QED
      BY <3>1, <3>3, ArmedPrevoteCertifiesTimed
  <2>3. CASE q # p
    BY <1>keep, <2>1, <2>3 DEFS ScheduleTimeoutPrevote, TypeOK
  <2> QED
    BY <2>2, <2>3
<1>2. CASE \E p \in Honest : (OnTimeoutPrecommit(p) \/ OnTimeoutPrevote(p)
                                \/ \E r \in Rounds : SkipRound(p, r))
  BY <1>2, <1>keep
  DEFS OnTimeoutPrecommit, OnTimeoutPrevote, ResetTimersFor, SkipRound, TimerType, TypeOK
<1>3. CASE /\ ~(\E p \in Honest : ScheduleTimeoutPrevote(p))
           /\ ~(\E p \in Honest : (OnTimeoutPrecommit(p) \/ OnTimeoutPrevote(p)
                                     \/ \E r \in Rounds : SkipRound(p, r)))
  BY <1>3, <1>keep
  DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, Tick, TimerType, TypeOK, vars
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM PrevoteArmedQuorumTimedInv ==
  ASSUME Spec PROVE []PrevoteArmedQuorumTimed
<1>1. PrevoteArmedQuorumTimed
  BY DEFS Init, PrevoteArmedQuorumTimed, Spec, TimerType
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow /\ [Next]_vars)
  BY InvProof, SentInvInv, SentTimeLeNowInv, PTL DEF Spec, Inv
<1>3. [](PrevoteArmedQuorumTimed => PrevoteArmedQuorumTimed')
  BY <1>2, PrevoteArmedQuorumTimedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- The single writer of the entry history --------------------------------
\* OnTimeoutPrecommit and SkipRound are the ONLY actions that move a round, and
\* both stamp the new round's entry instant in the same step. Factored out
\* because three proofs below need it, and because a bundled leaf over Next does
\* not discharge any of them.
LEMMA RoundEnteredStep ==
  ASSUME TypeOK, [Next]_vars
  PROVE  \/ (round' = round /\ enteredAt' = enteredAt)
         \/ \E q \in Honest : \E rr \in Rounds :
              /\ round' = [round EXCEPT ![q] = rr]
              /\ enteredAt' = [enteredAt EXCEPT ![q][rr] = now]
              /\ ((OnTimeoutPrecommit(q) /\ rr = round[q] + 1) \/ SkipRound(q, rr))
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE \E p \in Honest : HonestNext(p)
  BY <1>2
  DEFS Deliver, HonestNext, HonestStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TypeOK
<1>3. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>3 DEF FaultyStep
<1>4. CASE Tick
  BY <1>4 DEF Tick
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

\* The two-level EXCEPT evaluation, isolated in one small obligation.
LEMMA EnteredAtExcept ==
  ASSUME TypeOK, NEW q \in Honest, NEW rr0 \in Rounds,
         NEW c \in Honest, NEW rr \in Rounds,
         enteredAt' = [enteredAt EXCEPT ![q][rr0] = now]
  PROVE  enteredAt'[c][rr] = now \/ enteredAt'[c][rr] = enteredAt[c][rr]
BY DEF TypeOK

\* ---- Two small facts about the entry history -------------------------------
EnteredAtLeNow ==
  \A c \in Honest, rr \in Rounds : enteredAt[c][rr] # OFF => enteredAt[c][rr] <= now

EnteredCurrentRound == \A c \in Honest : enteredAt[c][round[c]] # OFF

LEMMA EnteredAtLeNowStepL ==
  ASSUME TypeOK, [Next]_vars, EnteredAtLeNow
  PROVE  EnteredAtLeNow'
BY EnteredAtExcept, NowShape, RoundEnteredStep DEFS EnteredAtLeNow, TypeOK

THEOREM EnteredAtLeNowInv == ASSUME Spec PROVE []EnteredAtLeNow
<1>1. EnteredAtLeNow
  BY DEFS EnteredAtLeNow, Init, Rounds, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](EnteredAtLeNow => EnteredAtLeNow')
  BY <1>2, EnteredAtLeNowStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

LEMMA EnteredCurrentRoundStepL ==
  ASSUME TypeOK, [Next]_vars, EnteredCurrentRound
  PROVE  EnteredCurrentRound'
BY NowNotOff, RoundEnteredStep DEFS EnteredCurrentRound, TypeOK

THEOREM EnteredCurrentRoundInv == ASSUME Spec PROVE []EnteredCurrentRound
<1>1. EnteredCurrentRound
  BY DEFS EnteredCurrentRound, Init, OFF, Rounds, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](EnteredCurrentRound => EnteredCurrentRound')
  BY <1>2, EnteredCurrentRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*   ---- Item E: the crossing lemma
\*   ------------------------------------------ NOT the research piece the
\*   work order first feared. The step induction ABSORBS the argument about
\*   the "first correct validator past lr". At the instant when p SKIPS to r,
\*   the skip evidence already puts some correct h at a round >= r, by
\*   SkipEvidenceHonestRound. The invariant already holds AT h. There is
\*   therefore no induction on the round, and no minimum over Honest. This is
\*   an ordinary inductive invariant, and the VALUE of the timer, which is
\*   item B, supplies the date.
CrossingBacked ==
  \A p \in Honest, r \in Rounds, lr \in Rounds :
    (enteredAt[p][r] # OFF /\ lr < r) =>
      \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, lr, v) \in sent
        /\ sentTime[Precommit(s, lr, v)]
             <= enteredAt[p][r] - TimeoutPrecommit(lr)

\* Any correct validator ALREADY above lr carries the certificate, dated at or
\* below the current clock. Top-level, not a step: it is used from two nested
\* branches below, and a step's ASSUME does not reach a nested leaf.
\* Weakening a dated certificate's bound has to happen INSIDE the two
\* quantifiers, so a plain BY cannot do it. Needed at two call sites, hence a
\* lemma rather than an inlined block.
LEMMA DatedCertWeaken ==
  ASSUME TypeOK, NEW lr, NEW t1 \in Int, NEW t2 \in Int, t1 <= t2,
         \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
           /\ Precommit(s, lr, v) \in sent
           /\ sentTime[Precommit(s, lr, v)] <= t1
  PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
           /\ Precommit(s, lr, v) \in sent
           /\ sentTime[Precommit(s, lr, v)] <= t2
BY DEFS OFF, sent, TypeOK

LEMMA CrossingFromEarlierEntry ==
  ASSUME TypeOK, EnteredAtLeNow, EnteredCurrentRound, CrossingBacked,
         NEW lr \in Rounds
  PROVE  (\E h \in Honest : lr < round[h])
           => \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                /\ Precommit(s, lr, v) \in sent
                /\ sentTime[Precommit(s, lr, v)] <= now - TimeoutPrecommit(lr)
\* The witness h does NOT occur in the conclusion, so a bare citation leaves a
\* backend nothing to unify it against. Keeping the \E in the ANTECEDENT means
\* each call site discharges it explicitly instead.
<1> SUFFICES ASSUME \E h \in Honest : lr < round[h]
             PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                      /\ Precommit(s, lr, v) \in sent
                      /\ sentTime[Precommit(s, lr, v)] <= now - TimeoutPrecommit(lr)
  OBVIOUS
<1>h. PICK h \in Honest : lr < round[h]
  OBVIOUS
<1>ar. TimeoutPrecommit(lr) \in Int /\ now \in Int
  BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit, TypeOK
<1>1. enteredAt[h][round[h]] # OFF /\ round[h] \in Rounds
  BY <1>h DEFS EnteredCurrentRound, TypeOK
<1>2. enteredAt[h][round[h]] <= now /\ enteredAt[h][round[h]] \in Nat
  BY <1>1, <1>h DEFS EnteredAtLeNow, TypeOK
<1>3. \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, lr, v) \in sent
        /\ sentTime[Precommit(s, lr, v)]
             <= enteredAt[h][round[h]] - TimeoutPrecommit(lr)
  BY <1>1, <1>h DEF CrossingBacked
<1>4. /\ enteredAt[h][round[h]] - TimeoutPrecommit(lr)
           <= now - TimeoutPrecommit(lr)
      /\ enteredAt[h][round[h]] - TimeoutPrecommit(lr) \in Int
      /\ now - TimeoutPrecommit(lr) \in Int
  BY <1>ar, <1>2
<1> QED
  BY <1>3, <1>4, DatedCertWeaken

LEMMA CrossingBackedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, [Next]_vars,
         PrecommitArmedQuorumTimed, EnteredAtLeNow, EnteredCurrentRound,
         CrossingBacked
  PROVE  CrossingBacked'
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds, NEW lr \in Rounds,
                    enteredAt'[p][r] # OFF, lr < r
             PROVE  \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                      /\ Precommit(s, lr, v) \in sent'
                      /\ sentTime'[Precommit(s, lr, v)]
                           <= enteredAt'[p][r] - TimeoutPrecommit(lr)
  BY DEF CrossingBacked
<1>fz. SentTimeFrozenPred \/ vars' = vars
  BY SentTimeFrozenStepL
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>ar. TimeoutPrecommit(lr) \in Int /\ now \in Int /\ lr \in Nat
  BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit, TypeOK
\* MOVE. A dated certificate at lr transports to the post-state verbatim:
\* `sent` grows and an activated timestamp never changes.
<1>move. \A t : (\E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                   /\ Precommit(s, lr, v) \in sent
                   /\ sentTime[Precommit(s, lr, v)] <= t)
                 => (\E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                       /\ Precommit(s, lr, v) \in sent'
                       /\ sentTime'[Precommit(s, lr, v)] <= t)
  BY <1>fz, <1>mono DEFS OFF, sent, SentTimeFrozenPred, vars
<1>1. CASE enteredAt'[p][r] = enteredAt[p][r]
  BY <1>1, <1>move DEF CrossingBacked
<1>2. CASE enteredAt'[p][r] # enteredAt[p][r]
  <2>1. PICK q \in Honest, rr \in Rounds :
          /\ enteredAt' = [enteredAt EXCEPT ![q][rr] = now]
          /\ ((OnTimeoutPrecommit(q) /\ rr = round[q] + 1) \/ SkipRound(q, rr))
    BY <1>2, RoundEnteredStep
  <2>2. q = p /\ rr = r /\ enteredAt'[p][r] = now
    BY <1>2, <2>1 DEF TypeOK
  <2> SUFFICES \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
                 /\ Precommit(s, lr, v) \in sent
                 /\ sentTime[Precommit(s, lr, v)] <= now - TimeoutPrecommit(lr)
    BY <1>move, <2>2
  <2>3. CASE OnTimeoutPrecommit(p) /\ r = round[p] + 1
    <3>1. now >= timer[p]["precommit"] /\ timer[p]["precommit"] # OFF
      BY <2>3 DEF OnTimeoutPrecommit
    <3>2. lr <= round[p] /\ round[p] \in Nat
      BY <1>ar, <2>3 DEFS Rounds, TypeOK
    <3>3. CASE lr = round[p]
      <4>1. PICK Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
              /\ Precommit(s, round[p], v) \in sent
              /\ sentTime[Precommit(s, round[p], v)]
                   <= timer[p]["precommit"] - TimeoutPrecommit(round[p])
        BY <3>1 DEF PrecommitArmedQuorumTimed
      <4>2. timer[p]["precommit"] \in Int
        BY DEFS TimerType, TypeOK
      <4>3. \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
              /\ Precommit(s, lr, v) \in sent
              /\ sentTime[Precommit(s, lr, v)]
                   <= timer[p]["precommit"] - TimeoutPrecommit(lr)
        BY <3>3, <4>1
      <4>4. /\ timer[p]["precommit"] - TimeoutPrecommit(lr) <= now - TimeoutPrecommit(lr)
            /\ timer[p]["precommit"] - TimeoutPrecommit(lr) \in Int
            /\ now - TimeoutPrecommit(lr) \in Int
        BY <1>ar, <3>1, <4>2
      <4> QED
        BY <4>3, <4>4, DatedCertWeaken
    <3>4. CASE lr < round[p]
      BY <3>4, CrossingFromEarlierEntry
    <3> QED
      BY <3>2, <3>3, <3>4
  <2>4. CASE SkipRound(p, r)
    <3>1. \E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, r)
      BY <2>4 DEF SkipRound
    <3>2. \E h \in Honest : lr < round[h]
      BY <1>ar, <3>1, SkipEvidenceHonestRound DEFS Rounds, TypeOK
    <3> QED
      BY <3>2, CrossingFromEarlierEntry
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1> QED
  BY <1>1, <1>2

THEOREM CrossingBackedInv == ASSUME Spec PROVE []CrossingBacked
<1>1. CrossingBacked
  BY DEFS CrossingBacked, Init, OFF, Rounds, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ PrecommitArmedQuorumTimed /\ EnteredAtLeNow /\ EnteredCurrentRound
           /\ [Next]_vars  )
  BY InvProof, SentInvInv, SentTimeLeNowInv, PrecommitArmedQuorumTimedInv,
     EnteredAtLeNowInv, EnteredCurrentRoundInv, PTL DEF Spec, Inv
<1>3. [](CrossingBacked => CrossingBacked')
  BY <1>2, CrossingBackedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*    ---- Precommit dating: a correct precommit is never dated below its
\*    round. The three actions that emit a precommit all broadcast at the OWN
\*    current round of the sender. RoundBelowNow bounds that round by the
\*    clock at the send instant. This is the lemma that turns the PRE-GST
\*    escape of the window lemma into a bound on the ROUND. A correct round-lr
\*    precommit that is sent before GST forces lr < GST.
PrecommitRoundLeSendTime ==
  \A x \in Honest, k \in Rounds, v \in ValuesOrNil :
    Precommit(x, k, v) \in sent => k <= sentTime[Precommit(x, k, v)]

\* Precommit sibling of FreshHonestPrevoteEmitter. Same shape, and the emitting
\* action has to be named for the same reason: only its guard carries the round
\* equality. The extra conjunct dates the fresh timestamp at `now`.
LEMMA FreshHonestPrecommitEmitter ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Precommit", mm.sender \in Honest
  PROVE  mm.round = round[mm.sender] /\ sentTime'[mm] = now
BY DEFS Broadcast, Deliver, FaultyStep, Honest, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Precommit, Prevote, Proposal, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

LEMMA PrecommitRoundLeSendTimeStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundBelowNow, [Next]_vars,
         PrecommitRoundLeSendTime
  PROVE  PrecommitRoundLeSendTime'
BY FreshHonestPrecommitEmitter, SentTimeFrozenStepL
DEFS Honest, Message, Precommit, PrecommitMsg, PrecommitRoundLeSendTime, RoundBelowNow, Rounds, sent, SentTimeFrozenPred, TypeOK, vars

THEOREM PrecommitRoundLeSendTimeInv == ASSUME Spec PROVE []PrecommitRoundLeSendTime
<1>1. PrecommitRoundLeSendTime
  BY DEFS Init, PrecommitRoundLeSendTime, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundBelowNow /\ [Next]_vars  )
  BY InvProof, SentInvInv, RoundBelowNowInv, PTL DEF Spec, Inv
<1>3. [](PrecommitRoundLeSendTime => PrecommitRoundLeSendTime')
  BY <1>2, PrecommitRoundLeSendTimeStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\*   ---- Dated evidence: the three shapes the argument dates
\*   ------------------- All three read `sent` and `sentTime` ONLY. Each one
\*   therefore transports across a step, by the monotonicity of the pool and
\*   by the freezing of the timestamps. Each one is also monotone in the date
\*   T. Every one of those moves has to happen INSIDE the quorum quantifiers,
\*   and no plain BY reaches there. DatedCertWeaken records that trap for item
\*   E. The small lemmas below therefore do each move once.

\* An ANY-VALUE prevote quorum at round rr, every member dated at or below T.
\* This is what an armed prevote timer certifies (item C), and once delivered it
\* enables both SkipRound and ScheduleTimeoutPrevote.
AnyPrevoteDated(rr, T) ==
  \E Q \in ByzQuorum : \A s \in Q : \E vv \in ValuesOrNil :
    /\ Prevote(s, rr, vv) \in sent
    /\ sentTime[Prevote(s, rr, vv)] <= T

\* A POLKA for the single value vv at round rr, every member dated at or below T.
PolkaDated(rr, vv, T) ==
  \E Q \in ByzQuorum : \A s \in Q :
    /\ Prevote(s, rr, vv) \in sent
    /\ sentTime[Prevote(s, rr, vv)] <= T

\*  The dated evidence that a correct prevote for w \in Values at round rr
\*  rests on. That evidence is the round-rr proposal for w. When the proposal
\*  carries a proof of lock, it also holds the polka at the valid round of the
\*  proposal. This is exactly what CanCompute's third and fourth disjuncts
\*  read, so a correct validator holding it at round rr cannot sit in step
\*  "propose".
Justified(rr, w, T) ==
  \E prop \in Message :
    /\ prop \in sent
    /\ sentTime[prop] <= T
    /\ prop.type = "Proposal"
    /\ prop.sender = Proposer[rr]
    /\ prop.round = rr
    /\ prop.value = w
    /\ \/ prop.validRound = -1
       \/ /\ prop.validRound \in B!Range(0, rr)
          /\ PolkaDated(prop.validRound, w, T)

\* ---- Quorum plumbing ------------------------------------------------------
\* 2f+1 >= f+1, so a Byzantine quorum is skip evidence. Cited where SkipRound's
\* WeakQuorum guard has to be met from a dated ByzQuorum.
LEMMA ByzIsWeak == ASSUME NEW Q \in ByzQuorum PROVE Q \in WeakQuorum
BY FaultBoundType, FS_CardinalityType, FS_Subset, ValidatorsFinite DEFS ByzQuorum, WeakQuorum

\*  One correct member out of a single quorum, by ByzQuorumIntersection at Q1
\*  := Q2. That is the shortest route. QuorumHonestLowerBound gives a
\*  cardinality, and it then needs finiteness to produce an element.
LEMMA ByzHasHonest == ASSUME NEW Q \in ByzQuorum PROVE \E s \in Q : s \in Honest
BY ByzQuorumIntersection

\* A prevote of a quorum member is a genuine message, needed for every
\* timestamp-typing step below.
LEMMA PrevoteInMessage ==
  ASSUME NEW Q \in ByzQuorum, NEW s \in Q, NEW rr \in Rounds, NEW vv \in ValuesOrNil
  PROVE  Prevote(s, rr, vv) \in Message
BY DEFS ByzQuorum, Message, Prevote, PrevoteMsg

\* ---- Weakening the date ---------------------------------------------------
LEMMA PolkaWeaken ==
  ASSUME TypeOK, NEW rr \in Rounds, NEW vv \in ValuesOrNil,
         NEW t1 \in Int, NEW t2 \in Int, t1 <= t2, PolkaDated(rr, vv, t1)
  PROVE  PolkaDated(rr, vv, t2)
BY DEFS OFF, PolkaDated, sent, TypeOK

LEMMA AnyPrevoteWeaken ==
  ASSUME TypeOK, NEW rr \in Rounds, NEW t1 \in Int, NEW t2 \in Int, t1 <= t2,
         AnyPrevoteDated(rr, t1)
  PROVE  AnyPrevoteDated(rr, t2)
BY DEFS AnyPrevoteDated, OFF, sent, TypeOK

LEMMA JustifiedWeaken ==
  ASSUME TypeOK, NEW rr \in Rounds, NEW w \in Values,
         NEW t1 \in Int, NEW t2 \in Int, t1 <= t2, Justified(rr, w, t1)
  PROVE  Justified(rr, w, t2)
<1>1. PICK prop \in Message :
        /\ prop \in sent
        /\ sentTime[prop] <= t1
        /\ prop.type = "Proposal"
        /\ prop.sender = Proposer[rr]
        /\ prop.round = rr
        /\ prop.value = w
        /\ \/ prop.validRound = -1
           \/ /\ prop.validRound \in B!Range(0, rr)
              /\ PolkaDated(prop.validRound, w, t1)
  BY DEF Justified
<1>2. sentTime[prop] <= t2
  BY <1>1 DEFS OFF, sent, TypeOK
<1>3. \/ prop.validRound = -1
      \/ /\ prop.validRound \in B!Range(0, rr)
         /\ PolkaDated(prop.validRound, w, t2)
  BY <1>1, PolkaWeaken DEFS B!Range, Rounds, ValuesOrNil
<1> QED
  BY <1>1, <1>2, <1>3 DEF Justified

\* A polka is in particular an any-value quorum.
LEMMA PolkaIsAnyPrevote ==
  ASSUME NEW rr, NEW vv \in ValuesOrNil, NEW T, PolkaDated(rr, vv, T)
  PROVE  AnyPrevoteDated(rr, T)
BY DEFS AnyPrevoteDated, PolkaDated

\* ---- Transport across a step, forwards ------------------------------------
\* One dated message moves verbatim: the pool only grows and an activated
\* timestamp never changes again.
LEMMA SentByMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW m, m \in sent, NEW t, sentTime[m] <= t
  PROVE  m \in sent' /\ sentTime'[m] <= t
BY SentMonotoneStep, SentTimeFrozenStepL DEFS OFF, sent, SentTimeFrozenPred, vars

LEMMA PolkaMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW rr, NEW vv, NEW t, PolkaDated(rr, vv, t)
  PROVE  PolkaDated(rr, vv, t)'
BY SentByMove DEF PolkaDated

LEMMA AnyPrevoteMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW rr, NEW t, AnyPrevoteDated(rr, t)
  PROVE  AnyPrevoteDated(rr, t)'
BY SentByMove DEF AnyPrevoteDated

LEMMA JustifiedMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         NEW rr, NEW w, NEW t, Justified(rr, w, t)
  PROVE  Justified(rr, w, t)'
BY PolkaMove, SentByMove DEF Justified

\*  ---- Transport across a step, backwards
\*  ----------------------------------- The direction that the induction runs
\*  on. Dated evidence in the POST-state either already held, or the step
\*  itself activated the last member. In the second case the clock is at or
\*  below the date. Both branches give the clock bound, so the step lemmas
\*  below split ONCE on now <= T and never again.
LEMMA SentByBack ==
  ASSUME TypeOK, [Next]_vars, NEW t, NEW m \in Message,
         m \in sent', sentTime'[m] <= t, ~(now <= t)
  PROVE  m \in sent /\ sentTime[m] <= t
BY SentTimeStep DEFS sent, TypeOK

LEMMA PolkaBack ==
  ASSUME TypeOK, [Next]_vars, NEW rr \in Rounds, NEW vv \in ValuesOrNil,
         NEW t, ~(now <= t), PolkaDated(rr, vv, t)'
  PROVE  PolkaDated(rr, vv, t)
BY PrevoteInMessage, SentByBack DEF PolkaDated

LEMMA AnyPrevoteBack ==
  ASSUME TypeOK, [Next]_vars, NEW rr \in Rounds, NEW t, ~(now <= t),
         AnyPrevoteDated(rr, t)'
  PROVE  AnyPrevoteDated(rr, t)
BY PrevoteInMessage, SentByBack DEF AnyPrevoteDated

LEMMA JustifiedBack ==
  ASSUME TypeOK, [Next]_vars, NEW rr \in Rounds, NEW w \in Values, NEW t,
         ~(now <= t), Justified(rr, w, t)'
  PROVE  Justified(rr, w, t)
BY PolkaBack, SentByBack DEFS B!Range, Justified, Rounds, ValuesOrNil

\*  ---- Item A, consumed
\*  ----------------------------------------------------- A message that is
\*  dated at or below a T after GST has reached EVERY correct validator once
\*  the clock is at T + Delta. Its DeliveryDeadline is at most T + Delta.
\*  GossipDeadline keeps the clock strictly below the deadline of anything
\*  that is still pending. This is the one place the >= GST guard is spent.
LEMMA DeliveredByDeadline ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW m \in Message, m \in sent,
         NEW T \in Int, T >= GST, sentTime[m] <= T, now >= T + Delta
  PROVE  m \in rcvd[c]
<1> SUFFICES ASSUME m \notin rcvd[c] PROVE FALSE
  OBVIOUS
<1>ty. sentTime[m] \in Int /\ now \in Nat /\ Delta \in Nat /\ GST \in Nat
  BY DeltaType, GSTType DEFS OFF, sent, TypeOK
<1>1. << c, m >> \in PendingDeliveries
  BY DEF PendingDeliveries
<1>2. now < DeliveryDeadline(m)
  BY <1>1 DEF GossipDeadline
<1>3. DeliveryDeadline(m) <= T + Delta /\ DeliveryDeadline(m) \in Int
  BY <1>ty DEF DeliveryDeadline
<1> QED
  BY <1>ty, <1>2, <1>3

\*  ---- Frame lemmas: who writes step, round and the prevote timer
\*  ------------ The factored forms the work order asks for. A bundled BY DEFS
\*  over all thirteen actions closes the frame EQUALITIES, and nothing else.
\*  The writer of each component is therefore isolated ONCE here. Every clause
\*  proof below then reads its guard off the named action, and it does not run
\*  the case analysis again.

\* Rounds only grow: both writers raise.
LEMMA RoundGrowsStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest
  PROVE  round[c] <= round'[c]
BY RoundEnteredStep DEFS OnTimeoutPrecommit, Rounds, SkipRound, TypeOK

\* Step "decided" is absorbing: the two actions that would move a validator on
\* (OnTimeoutPrecommit, SkipRound) are both guarded by step # "decided".
LEMMA DecidedStays ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, step[c] = "decided"
  PROVE  step'[c] = "decided"
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
  OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
  OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

\* The nine actions that can write step[c]. Propose, the two Schedule*, the late
\* valid update and Deliver all list step in UNCHANGED.
LEMMA StepWriterStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, step'[c] # step[c]
  PROVE  \/ OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
         \/ OnPrevoteQuorumValueFirstTime(c) \/ OnPrevoteQuorumNil(c)
         \/ OnTimeoutPrevote(c) \/ OnPrecommitQuorumValue(c) \/ OnTimeoutPrecommit(c)
         \/ (\E rr \in Rounds : SkipRound(c, rr))
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

\* The eight actions that can write timer[c].
LEMMA TimerWriterStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, timer'[c] # timer[c]
  PROVE  \/ OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
         \/ ScheduleTimeoutPrevote(c) \/ OnTimeoutPrevote(c)
         \/ ScheduleTimeoutPrecommit(c) \/ OnTimeoutPrecommit(c)
         \/ (\E rr \in Rounds : SkipRound(c, rr))
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

\* Entering step "prevote" -- or sitting in it across a round change, which is
\* impossible since both round writers land in "propose". The three
\* propose-to-prevote exits freeze the clock, the round AND the prevote slot,
\* which is what makes ProposeStepPrevoteOff bite at the post-state.
LEMMA PrevoteStepFrame ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, step'[c] = "prevote"
  PROVE  /\ round'[c] = round[c]
         /\ ( step[c] # "prevote" =>
                /\ step[c] = "propose"
                /\ now' = now
                /\ timer'[c]["prevote"] = timer[c]["prevote"] )
BY RoundEnteredStep, StepWriterStep
DEFS OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, SkipRound, TimerType, TypeOK

\*  Entry into step "propose" by a step that is not stuttering. Only the two
\*  raises of a round write it. Both raise strictly, both freeze the clock,
\*  and both are guarded by step # "decided".
LEMMA ProposeEntryFrame ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, step'[c] = "propose",
         ~(step[c] = "propose" /\ round'[c] = round[c])
  PROVE  /\ round[c] < round'[c]
         /\ step[c] # "decided"
         /\ now' = now
BY RoundEnteredStep, StepWriterStep
DEFS OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Rounds, SkipRound, TypeOK

\*  Under step' = "prevote", the only live writer of the prevote timer is the
\*  arming action. Its value dates the arming instant. That is item C, read at
\*  the post-state.
LEMMA PrevoteTimerWriteFrame ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, step'[c] = "prevote",
         timer'[c]["prevote"] # timer[c]["prevote"]
  PROVE  /\ step[c] = "prevote"
         /\ round'[c] = round[c]
         /\ now' = now
         /\ timer[c]["prevote"] = OFF
         /\ timer'[c]["prevote"] = now + TimeoutPrevote(round[c])
BY TimerWriterStep
DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TimerType, TypeOK

\*  ---- Sharpened fresh-vote emitters ---------------------------------------
\*  FreshHonestPrevoteEmitter and FreshHonestPrecommitEmitter give the round
\*  and the timestamp. The backing invariants below need the emitting ACTION
\*  as well, because only its guard carries the proposal and the polka.
LEMMA FreshPrevoteAction ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Prevote", mm.sender \in Honest
  PROVE  /\ mm.round = round[mm.sender]
         /\ sentTime'[mm] = now
         /\ \/ OnTimeoutPropose(mm.sender)
            \/ OnProposalNoPOL(mm.sender)
            \/ OnProposalWithPOL(mm.sender)
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
                  => (mm = m0 /\ sentTime'[mm] = now)
  BY <1>0 DEF TypeOK
<1>1. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>1, <1>pin DEFS FaultyStep, Honest
<1>2. CASE \E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p) \/ OnProposalWithPOL(p))
  BY <1>2, <1>pin DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, Prevote
<1>3. CASE \E p \in Honest : Propose(p)
  BY <1>3, <1>pin DEFS Broadcast, Proposal, Propose
<1>4. CASE \E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                \/ OnTimeoutPrevote(p))
  BY <1>4, <1>pin DEFS Broadcast, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote, Precommit
<1>5. CASE /\ ~(\E p \in Faulty : FaultyStep(p))
           /\ ~(\E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                                     \/ OnProposalWithPOL(p)))
           /\ ~(\E p \in Honest : Propose(p))
           /\ ~(\E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                     \/ OnTimeoutPrevote(p)))
  BY <1>0, <1>5
  DEFS Deliver, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumValueLateUpdate, OnTimeoutPrecommit, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA FreshPrecommitAction ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Precommit", mm.sender \in Honest
  PROVE  /\ mm.round = round[mm.sender]
         /\ sentTime'[mm] = now
         /\ \/ OnPrevoteQuorumValueFirstTime(mm.sender)
            \/ OnPrevoteQuorumNil(mm.sender)
            \/ OnTimeoutPrevote(mm.sender)
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
                  => (mm = m0 /\ sentTime'[mm] = now)
  BY <1>0 DEF TypeOK
<1>1. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>1, <1>pin DEFS FaultyStep, Honest
<1>2. CASE \E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                \/ OnTimeoutPrevote(p))
  BY <1>2, <1>pin DEFS Broadcast, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote, Precommit
<1>3. CASE \E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p) \/ OnProposalWithPOL(p))
  BY <1>3, <1>pin DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, Precommit, Prevote
<1>4. CASE \E p \in Honest : Propose(p)
  BY <1>4, <1>pin DEFS Broadcast, Precommit, Proposal, Propose
<1>5. CASE /\ ~(\E p \in Faulty : FaultyStep(p))
           /\ ~(\E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                     \/ OnTimeoutPrevote(p)))
           /\ ~(\E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                                     \/ OnProposalWithPOL(p)))
           /\ ~(\E p \in Honest : Propose(p))
  BY <1>0, <1>5
  DEFS Deliver, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumValueLateUpdate, OnTimeoutPrecommit, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

\*  ---- Prevote dating: the PRE-GST escape
\*  ----------------------------------- Prevote sibling of
\*  PrecommitRoundLeSendTime, and the lemma the work order named as the
\*  missing piece. The three prevote-emitting actions all broadcast at the
\*  sender's OWN current round, and RoundBelowNow bounds that round by the
\*  clock at the send instant. This is what turns the branch of item F before
\*  GST into the disjunct lr < GST. A correct round-lr prevote that is sent
\*  before GST forces lr < GST, and the arming evidence is exactly such a
\*  prevote.
PrevoteRoundLeSendTime ==
  \A x \in Honest, k \in Rounds, v \in ValuesOrNil :
    Prevote(x, k, v) \in sent => k <= sentTime[Prevote(x, k, v)]

LEMMA PrevoteRoundLeSendTimeStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundBelowNow, [Next]_vars,
         PrevoteRoundLeSendTime
  PROVE  PrevoteRoundLeSendTime'
BY FreshPrevoteAction, SentTimeFrozenStepL
DEFS Honest, Message, Prevote, PrevoteMsg, PrevoteRoundLeSendTime, RoundBelowNow, Rounds, sent, SentTimeFrozenPred, TypeOK, vars

THEOREM PrevoteRoundLeSendTimeInv == ASSUME Spec PROVE []PrevoteRoundLeSendTime
<1>1. PrevoteRoundLeSendTime
  BY DEFS Init, PrevoteRoundLeSendTime, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundBelowNow /\ [Next]_vars  )
  BY InvProof, SentInvInv, RoundBelowNowInv, PTL DEF Spec, Inv
<1>3. [](PrevoteRoundLeSendTime => PrevoteRoundLeSendTime')
  BY <1>2, PrevoteRoundLeSendTimeStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- The armed prevote deadline is never more than one timeout out
\*  --------- Read at the POST-state, in the one branch where the dated
\*  evidence becomes datable only at this very step. The timer can already be
\*  armed there. The value of item C itself is then the only bound available.
\*  A round change cannot break it, because ResetTimersFor clears the prevote
\*  slot on the way.
PrevoteTimerLE ==
  \A c \in Honest :
    timer[c]["prevote"] # OFF => timer[c]["prevote"] <= now + TimeoutPrevote(round[c])

LEMMA PrevoteTimerLEStepL ==
  ASSUME TypeOK, [Next]_vars, PrevoteTimerLE
  PROVE  PrevoteTimerLE'
BY NowShape, RoundEnteredStep, T0PrevoteType, TDeltaType, TimerWriterStep
DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrevoteTimerLE, ResetTimersFor, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TimeoutPrevote, TimerType, TypeOK

THEOREM PrevoteTimerLEInv == ASSUME Spec PROVE []PrevoteTimerLE
<1>1. PrevoteTimerLE
  BY DEFS Init, OFF, PrevoteTimerLE, Spec, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](PrevoteTimerLE => PrevoteTimerLE')
  BY <1>2, PrevoteTimerLEStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- A correct validator's own view is a dated global certificate ----------
LEMMA ViewPolkaDated ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, NEW y \in Honest,
         NEW rr \in Rounds, NEW vv \in ValuesOrNil, RExistsPrevoteQuorum(y, vv, rr)
  PROVE  PolkaDated(rr, vv, now)
BY PrevoteSenderInRcvd DEFS OFF, PolkaDated, RcvdSubsetSent, RExistsPrevoteQuorum, sent, SentTimeLeNow

\*  ---- A correct prevote for a VALUE carries its own justification
\*  ----------- The date is carried as a separate parameter t, and not as
\*  sentTime[Prevote(...)]. To prime the invariant therefore never primes an
\*  ARGUMENT of an operator. The form <= t also does the weakening that the
\*  call sites need.
PrevoteJustified ==
  \A y \in Honest, rr \in Rounds, w \in Values, t \in Nat :
    (Prevote(y, rr, w) \in sent /\ sentTime[Prevote(y, rr, w)] <= t)
      => Justified(rr, w, t)

\*  Only OnProposalNoPOL and OnProposalWithPOL can broadcast a prevote for a
\*  VALUE: OnTimeoutPropose votes nil, and nil is not a Value. Each one reads
\*  the proposal out of its own rcvd. With a proof of lock it also reads the
\*  polka at the valid round of the proposal. RcvdSubsetSent and SentTimeLeNow
\*  therefore date the whole justification at or below the clock.
LEMMA FreshValuePrevoteEvidence ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, [Next]_vars,
         NEW y \in Honest, NEW rr \in Rounds, NEW w \in Values,
         Prevote(y, rr, w) \in sent', Prevote(y, rr, w) \notin sent
  PROVE  Justified(rr, w, now)
<1>m. /\ Prevote(y, rr, w) \in Message
      /\ Prevote(y, rr, w).type = "Prevote"
      /\ Prevote(y, rr, w).sender = y
      /\ Prevote(y, rr, w).round = rr
  BY DEFS Honest, Message, Prevote, PrevoteMsg, ValuesOrNil
<1>0. sentTime[Prevote(y, rr, w)] = OFF /\ sentTime'[Prevote(y, rr, w)] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now] => Prevote(y, rr, w) = m0
  BY <1>0, <1>m DEF TypeOK
<1>rr. rr = round[y]
  BY <1>m, FreshPrevoteAction
<1>act. OnTimeoutPropose(y) \/ OnProposalNoPOL(y) \/ OnProposalWithPOL(y)
  BY <1>m, FreshPrevoteAction
<1>1. CASE OnTimeoutPropose(y)
  BY <1>1, <1>pin, NilNotInValues DEFS Broadcast, OnTimeoutPropose, Prevote
<1>2. CASE OnProposalNoPOL(y)
  BY <1>2, <1>pin, <1>rr, NilNotInValues
  DEFS Broadcast, Justified, OFF, OnProposalNoPOL, Prevote, RcvdSubsetSent, RProposals, RProposalsFromProposerAt, sent, SentTimeLeNow, TypeOK
<1>3. CASE OnProposalWithPOL(y)
  <2>1. PICK prop \in RProposalsFromProposerAt(y, round[y]) :
          /\ RExistsPrevoteQuorum(y, prop.value, prop.validRound)
          /\ prop.validRound \in B!Range(0, round[y])
          /\ sentTime' = [sentTime EXCEPT
                            ![Prevote(y, round[y],
                                      IF Valid(prop.value)
                                           /\ (locked[y].round <= prop.validRound
                                                 \/ locked[y].value = prop.value)
                                      THEN prop.value ELSE nil)] = now]
    BY <1>3, RangeCo DEFS Broadcast, OnProposalWithPOL
  <2>2. w = (IF Valid(prop.value)
                  /\ (locked[y].round <= prop.validRound \/ locked[y].value = prop.value)
             THEN prop.value ELSE nil)
    BY <1>pin, <2>1 DEF Prevote
  <2>3. prop.value = w
    BY <2>2, NilNotInValues
  <2>4. /\ prop \in Message /\ prop \in sent /\ sentTime[prop] <= now
        /\ prop.type = "Proposal" /\ prop.sender = Proposer[rr] /\ prop.round = rr
    BY <1>rr, <2>1 DEFS OFF, RcvdSubsetSent, RProposals, RProposalsFromProposerAt,
      sent, SentTimeLeNow, TypeOK
  <2>5. prop.validRound \in Rounds
    BY <2>1 DEFS B!Range, Rounds
  <2>6. PolkaDated(prop.validRound, w, now)
    BY <2>1, <2>3, <2>5, ViewPolkaDated DEF ValuesOrNil
  <2>7. prop.validRound \in B!Range(0, rr)
    BY <1>rr, <2>1
  <2> QED
    BY <2>3, <2>4, <2>6, <2>7 DEF Justified
<1> QED
  BY <1>1, <1>2, <1>3, <1>act

LEMMA PrevoteJustifiedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, [Next]_vars, PrevoteJustified
  PROVE  PrevoteJustified'
BY FreshPrevoteAction, FreshValuePrevoteEvidence, JustifiedMove, JustifiedWeaken, SentTimeFrozenStepL
DEFS Honest, Message, Prevote, PrevoteJustified, PrevoteMsg, sent, SentTimeFrozenPred, TypeOK, ValuesOrNil, vars

THEOREM PrevoteJustifiedInv == ASSUME Spec PROVE []PrevoteJustified
<1>1. PrevoteJustified
  BY DEFS Init, PrevoteJustified, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow /\ [Next]_vars  )
  BY InvProof, SentInvInv, SentTimeLeNowInv, PTL DEF Spec, Inv
<1>3. [](PrevoteJustified => PrevoteJustified')
  BY <1>2, PrevoteJustifiedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- A correct precommit carries its own dated backing
\*  -------------------- There are three shapes, one for each emitting action.
\*  A value precommit rests on a polka for that value. A nil precommit rests
\*  on a nil polka, through OnPrevoteQuorumNil. It can instead rest, through
\*  OnTimeoutPrevote, on an any-value quorum a full TimeoutPrevote(rr)
\*  EARLIER, because the value of the timer dates its arming. That third shape
\*  is where the TimeoutPrevote terms cancel.
Backing(rr, v, t) ==
  \/ /\ v \in Values
     /\ Valid(v)
     /\ PolkaDated(rr, v, t)
  \/ /\ v = nil
     /\ PolkaDated(rr, nil, t)
  \/ /\ v = nil
     /\ AnyPrevoteDated(rr, t - TimeoutPrevote(rr))

PrecommitBacked ==
  \A x \in Honest, rr \in Rounds, v \in ValuesOrNil, t \in Nat :
    (Precommit(x, rr, v) \in sent /\ sentTime[Precommit(x, rr, v)] <= t)
      => Backing(rr, v, t)

LEMMA BackingWeaken ==
  ASSUME TypeOK, NEW rr \in Rounds, NEW v \in ValuesOrNil,
         NEW t1 \in Int, NEW t2 \in Int, t1 <= t2, Backing(rr, v, t1)
  PROVE  Backing(rr, v, t2)
BY AnyPrevoteWeaken, PolkaWeaken, T0PrevoteType, TDeltaType DEFS Backing, Rounds, TimeoutPrevote, ValuesOrNil

LEMMA BackingMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars, NEW rr, NEW v, NEW t,
         Backing(rr, v, t)
  PROVE  Backing(rr, v, t)'
BY AnyPrevoteMove, PolkaMove DEF Backing

LEMMA FreshPrecommitBacking ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, PrevoteArmedQuorumTimed, [Next]_vars,
         NEW x \in Honest, NEW rr \in Rounds, NEW v \in ValuesOrNil,
         Precommit(x, rr, v) \in sent', Precommit(x, rr, v) \notin sent
  PROVE  Backing(rr, v, now)
<1>m. /\ Precommit(x, rr, v) \in Message
      /\ Precommit(x, rr, v).type = "Precommit"
      /\ Precommit(x, rr, v).sender = x
      /\ Precommit(x, rr, v).round = rr
  BY DEFS Honest, Message, Precommit, PrecommitMsg
<1>0. sentTime[Precommit(x, rr, v)] = OFF /\ sentTime'[Precommit(x, rr, v)] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now] => Precommit(x, rr, v) = m0
  BY <1>0, <1>m DEF TypeOK
<1>rr. rr = round[x]
  BY <1>m, FreshPrecommitAction
<1>act. \/ OnPrevoteQuorumValueFirstTime(x)
        \/ OnPrevoteQuorumNil(x)
        \/ OnTimeoutPrevote(x)
  BY <1>m, FreshPrecommitAction
<1>1. CASE OnPrevoteQuorumValueFirstTime(x)
  BY <1>1, <1>pin, <1>rr, ViewPolkaDated
  DEFS Backing, Broadcast, Message, OnPrevoteQuorumValueFirstTime, Precommit, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, TypeOK, ValuesOrNil
<1>2. CASE OnPrevoteQuorumNil(x)
  BY <1>2, <1>pin, <1>rr, ViewPolkaDated DEFS Backing, Broadcast, OnPrevoteQuorumNil, Precommit, ValuesOrNil
<1>3. CASE OnTimeoutPrevote(x)
  <2>1. /\ timer[x]["prevote"] # OFF
        /\ now >= timer[x]["prevote"]
        /\ sentTime' = [sentTime EXCEPT ![Precommit(x, round[x], nil)] = now]
    BY <1>3 DEFS Broadcast, OnTimeoutPrevote
  <2>2. v = nil
    BY <1>pin, <2>1 DEF Precommit
  <2>3. AnyPrevoteDated(round[x], timer[x]["prevote"] - TimeoutPrevote(round[x]))
    BY <2>1 DEFS AnyPrevoteDated, PrevoteArmedQuorumTimed
  <2>ty. /\ timer[x]["prevote"] - TimeoutPrevote(round[x]) \in Int
         /\ now - TimeoutPrevote(rr) \in Int
         /\ timer[x]["prevote"] - TimeoutPrevote(round[x]) <= now - TimeoutPrevote(rr)
    BY <1>rr, <2>1, T0PrevoteType, TDeltaType
    DEFS Rounds, TimeoutPrevote, TimerType, TypeOK
  <2>4. AnyPrevoteDated(rr, now - TimeoutPrevote(rr))
    BY <1>rr, <2>3, <2>ty, AnyPrevoteWeaken
  <2> QED
    BY <2>2, <2>4 DEF Backing
<1> QED
  BY <1>1, <1>2, <1>3, <1>act

LEMMA PrecommitBackedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, PrevoteArmedQuorumTimed,
         [Next]_vars, PrecommitBacked
  PROVE  PrecommitBacked'
BY BackingMove, BackingWeaken, FreshPrecommitAction, FreshPrecommitBacking, SentTimeFrozenStepL
DEFS Honest, Message, Precommit, PrecommitBacked, PrecommitMsg, sent, SentTimeFrozenPred, TypeOK, vars

THEOREM PrecommitBackedInv == ASSUME Spec PROVE []PrecommitBacked
<1>1. PrecommitBacked
  BY DEFS Init, PrecommitBacked, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ PrevoteArmedQuorumTimed /\ [Next]_vars  )
  BY InvProof, SentInvInv, SentTimeLeNowInv, PrevoteArmedQuorumTimedInv, PTL
  DEF Spec, Inv
<1>3. [](PrecommitBacked => PrecommitBacked')
  BY <1>2, PrecommitBackedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- Item F, the maximal-progress ceiling
\*  ---------------------------------- Delivered dated evidence at round rr
\*  pins the clock. Every state that a correct validator could still be in, at
\*  or below rr, leaves it a computation step. Tick is gated on the absence of
\*  any such step. The four enabling lemmas below are the four states to rule
\*  out, one CanCompute disjunct each.

LEMMA ByzNonEmpty == ASSUME NEW Q \in ByzQuorum PROVE \E s : s \in Q
BY ByzHasHonest

\* Every member of a dated any-value quorum has reached c's view.
LEMMA QuorumDeliveredSenders ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW T \in Int,
         T >= GST, AnyPrevoteDated(rr, T), now >= T + Delta
  PROVE  \E Q \in ByzQuorum : Q \subseteq RSendersOfTypeAtRound(c, "Prevote", rr)
BY DeliveredByDeadline, PrevoteInMessage DEFS AnyPrevoteDated, Prevote, RSendersOfTypeAtRound

\* Same for a dated polka, in the shape the value guards read.
LEMMA PolkaDeliveredSenders ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds,
         NEW vv \in ValuesOrNil, NEW T \in Int, T >= GST, PolkaDated(rr, vv, T),
         now >= T + Delta
  PROVE  RExistsPrevoteQuorum(c, vv, rr)
BY DeliveredByDeadline, PrevoteInMessage DEFS PolkaDated, Prevote, RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor

\* The justification, delivered, in the shape the propose-step guards read.
LEMMA JustifiedDelivered ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW w \in Values,
         NEW T \in Int, T >= GST, Justified(rr, w, T), now >= T + Delta
  PROVE  \E prop \in RProposalsFromProposerAt(c, rr) :
           /\ prop.value = w
           /\ \/ prop.validRound = -1
              \/ /\ prop.validRound \in B!Range(0, rr)
                 /\ RExistsPrevoteQuorum(c, w, prop.validRound)
BY DeliveredByDeadline, PolkaDeliveredSenders
DEFS B!Range, Justified, Rounds, RProposals, RProposalsFromProposerAt, ValuesOrNil

\* Maximal progress, as the one-line contradiction every clause below closes on.
LEMMA TickNeedsQuiet == ASSUME Tick, NEW c \in Honest, CanCompute(c) PROVE FALSE
BY DEF Tick

\* (1) c cannot lag BELOW rr: the delivered quorum is f+1 senders at rr, so
\* SkipRound(c, rr) is enabled (thirteenth disjunct).
LEMMA SkipEnabledFromQuorum ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW T \in Int,
         T >= GST, AnyPrevoteDated(rr, T), now >= T + Delta,
         step[c] # "decided", round[c] < rr
  PROVE  CanCompute(c)
BY ByzIsWeak, QuorumDeliveredSenders DEFS CanCompute, RSendersOfAnyMessageAt

\* (2) c cannot sit at rr in step "prevote" with the prevote timer OFF:
\* ScheduleTimeoutPrevote(c) is enabled (fifth disjunct).
LEMMA ArmEnabledFromQuorum ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW T \in Int,
         T >= GST, AnyPrevoteDated(rr, T), now >= T + Delta,
         round[c] = rr, step[c] = "prevote", timer[c]["prevote"] = OFF
  PROVE  CanCompute(c)
BY QuorumDeliveredSenders DEFS CanCompute, RExistsAnyPrevoteQuorum

\* (3) c cannot sit at rr in step "propose": the delivered justification fires
\* the third disjunct (fresh proposal) or the fourth (proof of lock).
LEMMA ProposeExitEnabled ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW w \in Values,
         NEW T \in Int, T >= GST, Justified(rr, w, T), now >= T + Delta,
         round[c] = rr, step[c] = "propose"
  PROVE  CanCompute(c)
BY JustifiedDelivered, RangeCo DEF CanCompute

\* (4) c cannot sit at rr in step "prevote" with the full value evidence: the
\* sixth disjunct fires, which is the value precommit itself.
LEMMA ValuePrecommitEnabled ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW rr \in Rounds, NEW w \in Values,
         NEW T \in Int, T >= GST, Justified(rr, w, T), PolkaDated(rr, w, T), Valid(w),
         now >= T + Delta, round[c] = rr, step[c] = "prevote"
  PROVE  CanCompute(c)
BY JustifiedDelivered, PolkaDeliveredSenders DEFS CanCompute, ValuesOrNil

\*   ---- The ceiling itself
\*   --------------------------------------------------- There are five
\*   clauses, in one joint induction. The round-below clause feeds the
\*   propose-step clause. That one feeds the timer-off clause, and that one
\*   feeds both the armed-deadline clause and the value-evidence clause. To
\*   split them into separate theorems is not possible. Each entry into a
\*   round, or into a step, lands in the state of the previous clause.
LockWindowCore ==
  \A c \in Honest, rr \in Rounds, w \in Values, T \in Nat :
    ( /\ T >= GST
      /\ AnyPrevoteDated(rr, T)
      /\ Justified(rr, w, T) )
    => /\ (step[c] # "decided" /\ round[c] < rr => now <= T + Delta)
       /\ (round[c] = rr /\ step[c] = "propose" => now <= T + Delta)
       /\ (round[c] = rr /\ step[c] = "prevote" /\ timer[c]["prevote"] = OFF
             => now <= T + Delta)
       /\ (round[c] = rr /\ step[c] = "prevote" /\ timer[c]["prevote"] # OFF
             => timer[c]["prevote"] <= T + Delta + TimeoutPrevote(rr))
       /\ (round[c] = rr /\ step[c] = "prevote" /\ Valid(w) /\ PolkaDated(rr, w, T)
             => now <= T + Delta)

THEOREM PrevoteTimerLEBothStates ==
  ASSUME Spec PROVE [](PrevoteTimerLE /\ PrevoteTimerLE')
BY PrevoteTimerLEInv, PTL

LEMMA LockWindowCoreStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, GossipDeadline,
         ProposeStepPrevoteOff, PrevoteTimerLE', [Next]_vars, LockWindowCore
  PROVE  LockWindowCore'
<1> SUFFICES ASSUME NEW c \in Honest, NEW rr \in Rounds, NEW w \in Values, NEW T \in Nat,
                    T >= GST, AnyPrevoteDated(rr, T)', Justified(rr, w, T)'
             PROVE  /\ (step'[c] # "decided" /\ round'[c] < rr => now' <= T + Delta)
                    /\ (round'[c] = rr /\ step'[c] = "propose" => now' <= T + Delta)
                    /\ (round'[c] = rr /\ step'[c] = "prevote"
                          /\ timer'[c]["prevote"] = OFF => now' <= T + Delta)
                    /\ (round'[c] = rr /\ step'[c] = "prevote"
                          /\ timer'[c]["prevote"] # OFF
                          => timer'[c]["prevote"] <= T + Delta + TimeoutPrevote(rr))
                    /\ (round'[c] = rr /\ step'[c] = "prevote" /\ Valid(w)
                          /\ PolkaDated(rr, w, T)' => now' <= T + Delta)
  BY DEF LockWindowCore
<1>ty. /\ now \in Nat /\ now' \in Nat /\ T \in Nat /\ GST \in Nat
       /\ Delta \in Nat /\ Delta > 1
       /\ round[c] \in Nat /\ round'[c] \in Nat
       /\ timer[c]["prevote"] \in Int /\ timer'[c]["prevote"] \in Int
       /\ TimeoutPrevote(rr) \in Nat
  BY DeltaType, GSTType, T0PrevoteType, TDeltaType
  DEFS Rounds, TimeoutPrevote, TimerType, TypeOK
<1>n. now' = now \/ now' = now + 1
  BY NowShape
\* BRANCH A. The evidence only becomes datable at this step, so the date T is at
\* or above the clock and every bound is slack.
<1>A. CASE now <= T
  BY <1>A, <1>n, <1>ty DEF PrevoteTimerLE
<1>B. CASE ~(now <= T)
  <2>ev. AnyPrevoteDated(rr, T) /\ Justified(rr, w, T)
    BY <1>B, AnyPrevoteBack, JustifiedBack
  <2>1. step[c] # "decided" /\ round[c] < rr => now <= T + Delta
    BY <2>ev DEF LockWindowCore
  <2>2. round[c] = rr /\ step[c] = "propose" => now <= T + Delta
    BY <2>ev DEF LockWindowCore
  <2>3. round[c] = rr /\ step[c] = "prevote" /\ timer[c]["prevote"] = OFF
          => now <= T + Delta
    BY <2>ev DEF LockWindowCore
  <2>4. round[c] = rr /\ step[c] = "prevote" /\ timer[c]["prevote"] # OFF
          => timer[c]["prevote"] <= T + Delta + TimeoutPrevote(rr)
    BY <2>ev DEF LockWindowCore
  <2>5. round[c] = rr /\ step[c] = "prevote" /\ Valid(w) /\ PolkaDated(rr, w, T)
          => now <= T + Delta
    BY <2>ev DEF LockWindowCore
  \*  CLAUSE 1. Round below rr. Rounds only grow, and "decided" is absorbing,
  \*  so the hypothesis held before the step. A Tick at the deadline would
  \*  find SkipRound enabled.
  <2>c1. step'[c] # "decided" /\ round'[c] < rr => now' <= T + Delta
    BY <1>n, <1>ty, <2>1, <2>ev, DecidedStays, NowStaysUnlessTick, RoundGrowsStep, SkipEnabledFromQuorum, TickNeedsQuiet
    DEFS Rounds, TypeOK
  <2>c2. round'[c] = rr /\ step'[c] = "propose" => now' <= T + Delta
    BY <1>n, <1>ty, <2>1, <2>2, <2>ev, NowStaysUnlessTick, ProposeEntryFrame, ProposeExitEnabled, TickNeedsQuiet
  <2>c3. round'[c] = rr /\ step'[c] = "prevote" /\ timer'[c]["prevote"] = OFF
           => now' <= T + Delta
    BY <1>n, <1>ty, <2>2, <2>3, <2>ev, ArmEnabledFromQuorum, NowStaysUnlessTick, PrevoteStepFrame, PrevoteTimerWriteFrame, TickNeedsQuiet
  <2>c4. round'[c] = rr /\ step'[c] = "prevote" /\ timer'[c]["prevote"] # OFF
           => timer'[c]["prevote"] <= T + Delta + TimeoutPrevote(rr)
    BY <1>ty, <2>3, <2>4, PrevoteStepFrame, PrevoteTimerWriteFrame DEF ProposeStepPrevoteOff
  <2>c5. round'[c] = rr /\ step'[c] = "prevote" /\ Valid(w) /\ PolkaDated(rr, w, T)'
           => now' <= T + Delta
    BY <1>B, <1>n, <1>ty, <2>2, <2>5, <2>ev, NowStaysUnlessTick, PolkaBack, PrevoteStepFrame, TickNeedsQuiet, ValuePrecommitEnabled
    DEF ValuesOrNil
  <2> QED
    BY <2>c1, <2>c2, <2>c3, <2>c4, <2>c5
<1> QED
  BY <1>A, <1>B

THEOREM LockWindowCoreInv == ASSUME Spec PROVE []LockWindowCore
\* Init has an empty pool, and no Byzantine quorum is empty, so the dated
\* any-value quorum is already unsatisfiable.
<1>1. LockWindowCore
  BY ByzNonEmpty DEFS AnyPrevoteDated, Init, LockWindowCore, sent, Spec
<1>2. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ GossipDeadline
           /\ ProposeStepPrevoteOff /\ PrevoteTimerLE' /\ [Next]_vars  )
  BY InvProof, TypeOKBothStates, SentInvInv, GossipDeadlineInv,
     ProposeStepPrevoteOffInv, PrevoteTimerLEBothStates, PTL DEF Spec, Inv
<1>3. [](LockWindowCore => LockWindowCore')
  BY <1>2, LockWindowCoreStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- Item F, the three-case bound
\*  ----------------------------------------- A correct value-precommit at
\*  round lr is at most one delivery delay after ANY correct precommit at
\*  round lr, unless lr is below GST. This is the inequality the whole window
\*  lemma reduces to. There are three cases. In case (a), OnTimeoutPrevote,
\*  the TimeoutPrevote(lr) terms cancel. The arming quorum of x reaches c
\*  within Delta, and the own prevote deadline of c adds the same term again.
\*  In case (b), a value precommit, c gets the same polka and the same
\*  proposal within Delta, and it uses no timeout at all. Case (c),
\*  OnPrevoteQuorumNil, is IMPOSSIBLE, by quorum intersection against the own
\*  polka of c for w in Values.
\*
\*   THE >= GST GUARD IS NOT SUFFICIENT ON ITS OWN, which is why the lr < GST
\*   escape is part of the statement. The guard dates the PRECOMMIT of x.
\*   Every step of the form "reaches c within Delta" instead runs on the
\*   ARMING EVIDENCE of x, and that evidence PRECEDES s_x. It precedes it by
\*   TimeoutPrevote(lr) in case (a), and by the polka and the proposal in case
\*   (b). That evidence can be pre-GST while s_x is not, and
\*   DeliveryDeadline(m) is max(sentTime[m], GST) + Delta, so it then reaches
\*   c only by GST + Delta. Case (a) therefore splits on whether the arming
\*   instant is after GST. When it is not, a correct member of the arming
\*   quorum is a round-lr prevote that was sent before GST.
\*   PrevoteRoundLeSendTime turns that into lr < GST.
LateLockDelivery ==
  \A c \in Honest, lr \in Rounds, w \in Values, x \in Honest, v \in ValuesOrNil :
    ( /\ Precommit(c, lr, w) \in sent
      /\ Precommit(x, lr, v) \in sent
      /\ sentTime[Precommit(x, lr, v)] >= GST )
    => \/ sentTime[Precommit(c, lr, w)] <= sentTime[Precommit(x, lr, v)] + Delta
       \/ lr < GST


\*  ---- Quorum intersection: the two facts the three cases turn on
\*  ------------ Two dated polkas at the same round agree: they share a
\*  correct member, and a correct validator prevotes at most once per round
\*  (item D). This is what makes case (c) IMPOSSIBLE, and not merely bounded.
\*  A nil polka at lr would pin the shared member to nil, and nil is not a
\*  Value.
LEMMA TwoPolkasAgree ==
  ASSUME TypeOK, PrevoteOncePerRound, NEW rr \in Rounds,
         NEW v1 \in ValuesOrNil, NEW v2 \in ValuesOrNil, NEW T1, NEW T2,
         PolkaDated(rr, v1, T1), PolkaDated(rr, v2, T2)
  PROVE  v1 = v2
BY ByzQuorumIntersection DEFS PolkaDated, PrevoteOncePerRound

\*  A polka for w and ANY dated quorum at the same round share a correct
\*  member, and item D pins that member's prevote to w. The shared member
\*  therefore supplies a prevote for w that carries the date of the QUORUM.
\*  That is the step which moves the own polka of c back to the arming instant
\*  of x, in case (a).
LEMMA PolkaMeetsQuorum ==
  ASSUME TypeOK, PrevoteOncePerRound, NEW rr \in Rounds, NEW vv \in ValuesOrNil,
         NEW T1, NEW T2, PolkaDated(rr, vv, T1), AnyPrevoteDated(rr, T2)
  PROVE  \E y \in Honest : /\ Prevote(y, rr, vv) \in sent
                           /\ sentTime[Prevote(y, rr, vv)] <= T2
BY ByzQuorumIntersection DEFS AnyPrevoteDated, PolkaDated, PrevoteOncePerRound

\* Item D read at one member: a correct validator's dated prevote for w carries
\* the whole justification at the same date.
LEMMA JustifiedFromOnePrevote ==
  ASSUME PrevoteJustified, NEW rr \in Rounds, NEW w \in Values, NEW T \in Nat,
         NEW y \in Honest, Prevote(y, rr, w) \in sent,
         sentTime[Prevote(y, rr, w)] <= T
  PROVE  Justified(rr, w, T)
BY DEF PrevoteJustified

LEMMA JustifiedFromPolka ==
  ASSUME TypeOK, PrevoteJustified, NEW rr \in Rounds, NEW w \in Values, NEW T \in Nat,
         PolkaDated(rr, w, T)
  PROVE  Justified(rr, w, T)
BY ByzHasHonest, JustifiedFromOnePrevote DEF PolkaDated

\* ---- Item F, the three-case bound -----------------------------------------
LEMMA LateLockDeliveryStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, PrevoteArmedQuorumTimed,
         PrevoteOncePerRound, PrevoteJustified, PrecommitBacked,
         PrevoteRoundLeSendTime, PrevoteDeadlineNotPassed, LockWindowCore,
         [Next]_vars, LateLockDelivery
  PROVE  LateLockDelivery'
<1> SUFFICES ASSUME NEW c \in Honest, NEW lr \in Rounds, NEW w \in Values,
                    NEW x \in Honest, NEW v \in ValuesOrNil,
                    Precommit(c, lr, w) \in sent',
                    Precommit(x, lr, v) \in sent',
                    sentTime'[Precommit(x, lr, v)] >= GST,
                    ~(lr < GST)
             PROVE  sentTime'[Precommit(c, lr, w)]
                      <= sentTime'[Precommit(x, lr, v)] + Delta
  BY DEF LateLockDelivery
<1>mc. /\ Precommit(c, lr, w) \in Message
       /\ Precommit(c, lr, w).type = "Precommit"
       /\ Precommit(c, lr, w).sender = c
       /\ Precommit(c, lr, w).round = lr
  BY DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
<1>mx. /\ Precommit(x, lr, v) \in Message
       /\ Precommit(x, lr, v).type = "Precommit"
       /\ Precommit(x, lr, v).sender = x
       /\ Precommit(x, lr, v).round = lr
  BY DEFS Honest, Message, Precommit, PrecommitMsg
<1>fz. SentTimeFrozenPred \/ vars' = vars
  BY SentTimeFrozenStepL
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ lr \in Nat
       /\ TimeoutPrevote(lr) \in Nat
  BY DeltaType, GSTType, T0PrevoteType, TDeltaType
  DEFS Rounds, TimeoutPrevote, TypeOK
\*  The lock is OLD. Its timestamp is frozen. The timestamp of x is either
\*  frozen too, and the induction hypothesis applies word for word, or it is
\*  fresh. In the second case the precommit of x is the LATER of the two, and
\*  the bound holds directly.
<1>1. CASE Precommit(c, lr, w) \in sent
  BY <1>1, <1>fz, <1>mc, <1>mx, <1>ty, FreshPrecommitAction
  DEFS LateLockDelivery, OFF, sent, SentTimeFrozenPred, SentTimeLeNow, TypeOK, vars
<1>2. CASE Precommit(c, lr, w) \notin sent
  <2>A. sentTime'[Precommit(c, lr, w)] = now /\ round[c] = lr
    BY <1>2, <1>mc, FreshPrecommitAction
  \* All three precommit emitters are guarded by step = "prevote".
  <2>st. step[c] = "prevote"
    BY <1>2, <1>mc, FreshPrecommitAction
    DEFS OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote
  \* w is a Value, so the nil shapes of the backing are out and c holds a polka.
  <2>bk. Backing(lr, w, now)
    BY <1>2, FreshPrecommitBacking DEF ValuesOrNil
  <2>pc. Valid(w) /\ PolkaDated(lr, w, now)
    BY <2>bk, NilNotInValues DEF Backing
  <2>same. CASE Precommit(x, lr, v) = Precommit(c, lr, w)
    BY <1>ty, <2>A, <2>same
  <2>diff. CASE Precommit(x, lr, v) # Precommit(c, lr, w)
    \* Only one message is activated per step, and it is the lock, so x's
    \* precommit was already in the pool with its timestamp frozen.
    <3>sh. sentTime' = sentTime \/ \E m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
      BY SentTimeStep
    <3>1. PICK m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
      BY <1>2, <3>sh DEF sent
    <3>2. m0 = Precommit(c, lr, w)
      BY <1>2, <1>mc, <3>1 DEFS sent, TypeOK
    <3>3. sentTime'[Precommit(x, lr, v)] = sentTime[Precommit(x, lr, v)]
      BY <1>mx, <2>diff, <3>1, <3>2 DEF TypeOK
    <3>4. Precommit(x, lr, v) \in sent
      BY <1>mx, <3>3 DEF sent
    <3>S. /\ sentTime[Precommit(x, lr, v)] \in Nat
          /\ sentTime[Precommit(x, lr, v)] >= GST
      BY <3>3, <3>4 DEFS OFF, sent, TypeOK
    <3>bx. Backing(lr, v, sentTime[Precommit(x, lr, v)])
      BY <3>4, <3>S DEF PrecommitBacked
    <3>b. CASE /\ v \in Values
               /\ Valid(v)
               /\ PolkaDated(lr, v, sentTime[Precommit(x, lr, v)])
      BY <2>A, <2>pc, <2>st, <3>3, <3>b, <3>S, JustifiedFromPolka, PolkaIsAnyPrevote, TwoPolkasAgree
      DEFS LockWindowCore, ValuesOrNil
    <3>c. CASE /\ v = nil
               /\ PolkaDated(lr, nil, sentTime[Precommit(x, lr, v)])
      BY <2>pc, <3>c, NilNotInValues, TwoPolkasAgree DEF ValuesOrNil
    <3>a. CASE /\ v = nil
               /\ AnyPrevoteDated(lr,
                     sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr))
      <4>T. sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr) \in Int
        BY <1>ty, <3>S
      \*  The arming evidence can be from before GST. It is then a round-lr
      \*  prevote that was sent before GST, and that forces lr < GST. The
      \*  hypothesis excludes that case.
      <4>1. CASE sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr) < GST
        BY <1>ty, <3>a, <4>1, <4>T, ByzHasHonest DEFS AnyPrevoteDated, OFF, PrevoteRoundLeSendTime, sent, TypeOK
      <4>2. CASE sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr) >= GST
        <5>T. sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr) \in Nat
          BY <1>ty, <4>2, <4>T
        <5>1. PICK y \in Honest :
                /\ Prevote(y, lr, w) \in sent
                /\ sentTime[Prevote(y, lr, w)]
                     <= sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr)
          BY <2>pc, <3>a, PolkaMeetsQuorum DEF ValuesOrNil
        <5>2. Justified(lr, w, sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr))
          BY <5>1, <5>T, JustifiedFromOnePrevote
        <5>3. CASE timer[c]["prevote"] = OFF
          <6>1. now <= sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr) + Delta
            BY <2>A, <2>st, <3>a, <4>2, <5>2, <5>3, <5>T DEF LockWindowCore
          <6> QED
            BY <1>ty, <2>A, <3>3, <3>S, <6>1
        <5>4. CASE timer[c]["prevote"] # OFF
          <6>1. timer[c]["prevote"]
                  <= sentTime[Precommit(x, lr, v)] - TimeoutPrevote(lr)
                       + Delta + TimeoutPrevote(lr)
            BY <2>A, <2>st, <3>a, <4>2, <5>2, <5>4, <5>T DEF LockWindowCore
          <6>2. now <= timer[c]["prevote"]
            BY <2>st, <5>4 DEF PrevoteDeadlineNotPassed
          <6>3. timer[c]["prevote"] \in Int
            BY DEFS TimerType, TypeOK
          <6> QED
            BY <1>ty, <2>A, <3>3, <3>S, <6>1, <6>2, <6>3
        <5> QED
          BY <5>3, <5>4
      <4> QED
        BY <1>ty, <4>1, <4>2, <4>T
    <3> QED
      BY <3>a, <3>b, <3>bx, <3>c DEF Backing
  <2> QED
    BY <2>diff, <2>same
<1> QED
  BY <1>1, <1>2

THEOREM LateLockDeliveryInv == ASSUME Spec PROVE []LateLockDelivery
<1>1. LateLockDelivery
  BY DEFS Init, LateLockDelivery, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ PrevoteArmedQuorumTimed /\ PrevoteOncePerRound /\ PrevoteJustified
           /\ PrecommitBacked /\ PrevoteRoundLeSendTime /\ PrevoteDeadlineNotPassed
           /\ LockWindowCore /\ [Next]_vars  )
  BY InvProof, SentInvInv, SentTimeLeNowInv, PrevoteArmedQuorumTimedInv,
     PrevoteOncePerRoundInv, PrevoteJustifiedInv, PrecommitBackedInv,
     PrevoteRoundLeSendTimeInv, PrevoteDeadlineNotPassedInv, LockWindowCoreInv, PTL
  DEF Spec, Inv
<1>3. [](LateLockDelivery => LateLockDelivery')
  BY <1>2, LateLockDeliveryStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\*  ---- Item G, the composition
\*  ---------------------------------------------- The whole timing gap is
\*  four lines of arithmetic once the pieces are in hand. Write A for the lock
\*  instant, B for x's round-lr precommit instant, E for enteredAt[p][r] and T
\*  for TimeoutPrecommit(lr). CrossingBacked dates a correct x at B <= E - T.
\*  Either B < GST, and PrecommitRoundLeSendTime gives lr <= B < GST, which is
\*  the second disjunct. Or B >= GST, and item F gives A <= B + Delta, so A +
\*  T <= E + Delta.
\*
\* ByzQuorumIntersection is cited at Q1 := Q2 := Q, the cheapest way to get one
\* correct member out of a Byzantine quorum. QuorumHonestLowerBound gives the
\* cardinality instead, and then needs a finiteness argument to produce an
\* element.
THEOREM GapFromDelivery ==
  ASSUME TypeOK, CrossingBacked, PrecommitRoundLeSendTime, LateLockDelivery
  PROVE  LateValueLockGap
<1> SUFFICES ASSUME NEW c \in Honest, NEW w \in Values, NEW lr \in Rounds,
                    NEW p \in Honest, NEW r \in Rounds,
                    lr < r, enteredAt[p][r] # OFF, enteredAt[p][r] > GST,
                    Precommit(c, lr, w) \in sent
             PROVE  \/ sentTime[Precommit(c, lr, w)] + TimeoutPrecommit(lr)
                         <= enteredAt[p][r] + Delta
                    \/ lr < GST
  BY DEF LateValueLockGap
<1>q. PICK Q \in ByzQuorum : \A s \in Q : \E vv \in ValuesOrNil :
        /\ Precommit(s, lr, vv) \in sent
        /\ sentTime[Precommit(s, lr, vv)] <= enteredAt[p][r] - TimeoutPrecommit(lr)
  BY DEF CrossingBacked
<1>h. PICK x \in Q : x \in Honest
  BY <1>q, ByzQuorumIntersection
<1>x. PICK v \in ValuesOrNil :
        /\ Precommit(x, lr, v) \in sent
        /\ sentTime[Precommit(x, lr, v)] <= enteredAt[p][r] - TimeoutPrecommit(lr)
  BY <1>q, <1>h
<1>mc. Precommit(c, lr, w) \in Message /\ w \in ValuesOrNil
  BY DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
<1>mx. Precommit(x, lr, v) \in Message
  BY <1>h DEFS Honest, Message, Precommit, PrecommitMsg
<1>ty. /\ sentTime[Precommit(c, lr, w)] \in Nat
       /\ sentTime[Precommit(x, lr, v)] \in Nat
       /\ enteredAt[p][r] \in Nat
       /\ TimeoutPrecommit(lr) \in Int
       /\ Delta \in Nat /\ GST \in Nat /\ lr \in Nat
  BY <1>mc, <1>mx, <1>x, DeltaType, GSTType, T0PrecommitType, TDeltaType
  DEFS OFF, Rounds, sent, TimeoutPrecommit, TypeOK
<1>1. CASE sentTime[Precommit(x, lr, v)] < GST
  BY <1>1, <1>h, <1>ty, <1>x DEF PrecommitRoundLeSendTime
<1>2. CASE sentTime[Precommit(x, lr, v)] >= GST
  BY <1>2, <1>h, <1>mc, <1>ty, <1>x DEF LateLockDelivery
<1> QED
  BY <1>1, <1>2, <1>ty

\* Clean, Spec-free necessitation of the composition. Inline boxing FAILS with
\* Spec in scope, so the boxed implication is hoisted here with constant-only
\* assumptions and cited from the theorem below.
LEMMA BoxGapFromDelivery ==
  [](  TypeOK /\ CrossingBacked /\ PrecommitRoundLeSendTime /\ LateLockDelivery
       => LateValueLockGap  )
<1>1. TypeOK /\ CrossingBacked /\ PrecommitRoundLeSendTime /\ LateLockDelivery
        => LateValueLockGap
  BY GapFromDelivery
<1> QED
  BY <1>1, PTL

THEOREM LateValueLockGapFromDelivery ==
  ASSUME Spec, []LateLockDelivery
  PROVE  []LateValueLockGap
BY BoxGapFromDelivery, CrossingBackedInv, InvProof, PrecommitRoundLeSendTimeInv, PTL DEFS Inv, Spec

THEOREM LateValueLockGapInv == ASSUME Spec PROVE []LateValueLockGap
BY LateLockDeliveryInv, LateValueLockGapFromDelivery

\* The old window theorem is the gap's immediate corollary when the correct
\* value precommit is no earlier than the entry.
THEOREM WindowFromGap ==
  ASSUME TypeOK, LateValueLockGap
  PROVE  LateValueLockWindow
<1> SUFFICES ASSUME NEW c \in Honest, NEW w \in Values, NEW lr \in Rounds,
                    NEW p \in Honest, NEW r \in Rounds,
                    lr < r, enteredAt[p][r] # OFF, enteredAt[p][r] > GST,
                    Precommit(c, lr, w) \in sent,
                    sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]
             PROVE  TimeoutPrecommit(lr) <= Delta \/ lr < GST
  BY DEF LateValueLockWindow
<1>1. \/ sentTime[Precommit(c, lr, w)] + TimeoutPrecommit(lr)
             <= enteredAt[p][r] + Delta
       \/ lr < GST
  BY DEF LateValueLockGap
<1>2. CASE sentTime[Precommit(c, lr, w)] + TimeoutPrecommit(lr)
             <= enteredAt[p][r] + Delta
  BY <1>2, DeltaType, T0PrecommitType, TDeltaType
  DEFS OFF, Rounds, sent, TimeoutPrecommit, TypeOK
<1>3. CASE lr < GST
  BY <1>3
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA BoxWindowFromGap ==
  [](TypeOK /\ LateValueLockGap => LateValueLockWindow)
<1>1. TypeOK /\ LateValueLockGap => LateValueLockWindow
  BY WindowFromGap
<1> QED
  BY <1>1, PTL

\* The unconditional form ...LockRetry consumes. Nothing in the chain behind it is
\* admitted: item F is discharged at LateLockDeliveryInv above.
THEOREM LateValueLockWindowInv == ASSUME Spec PROVE []LateValueLockWindow
<1>1. []TypeOK
  BY InvProof DEF Spec, Inv
<1> QED
  BY <1>1, LateValueLockGapInv, BoxWindowFromGap, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)