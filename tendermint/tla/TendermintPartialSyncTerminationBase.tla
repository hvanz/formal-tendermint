--------------------- MODULE TendermintPartialSyncTerminationBase --------------
(***************************************************************************)
(* Shared foundation for the termination proof. It holds the auxiliary     *)
(* definitions and Layers 0 to 2. Those are safety, the facts about the    *)
(* clock and the latches, the invariants about the messages, the decision  *)
(* and the delivery, and HonestFinite. The WithinRound module, which is    *)
(* Layer 3, and the CrossRound module, which is Layer 4, both EXTEND this  *)
(* one. The composition module TendermintPartialSyncTermination assembles     *)
(* them.                                                                   *)
(***************************************************************************)
EXTENDS TendermintPartialSyncRefinement, NaturalsInduction, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* No global assumption about timing is necessary here. The specification  *)
(* exposes the three distinct timeouts of the paper, which are             *)
(* TimeoutPropose, TimeoutPrevote and TimeoutPrecommit. Condition 4 of     *)
(* paper Lemma 5 is therefore carried VERBATIM, as a hypothesis of each    *)
(* theorem. See Lemma5Hyp below. That condition is timeoutPropose(r) >     *)
(* 2*Delta + timeoutPrecommit(r-1), timeoutPrevote(r) > 2*Delta, and       *)
(* timeoutPrecommit(r) > 2*Delta. It is not folded into one global         *)
(* assumption TDelta > 2*Delta. Layer 4d, which is the selection of the    *)
(* good round, discharges it when it picks the deciding round.             *)
(***************************************************************************)

(***************************************************************************)
(* Auxiliary definitions. They belong to the proof module only, and they   *)
(* do not change the specification. The vote predicates read the derived   *)
(* global pool `sent`. The Mono* lemmas bridge the R* views of each        *)
(* validator to these predicates when that is necessary.                   *)
(***************************************************************************)
HasDecided(p)           == decision[p] # nil
VotedPrevote(p, v, r)   == Prevote(p, r, v)   \in sent
VotedPrecommit(p, v, r) == Precommit(p, r, v) \in sent

\* Shared success predicates used by all three termination interfaces.
SomeCorrectDecided ==
  \E c \in Honest : HasDecided(c)

AllCorrectDecided ==
  \A c \in Honest : HasDecided(c)

\* ---- Paper Lemma 5 hypotheses (Section IV), transcribed ------------------
\* The history variable enteredAt records the instant of entry into each
\* round, because the bare state of the algorithm does not retain it. "The
\* first correct process to enter round r at time t" is therefore an ordinary
\* state predicate. It says that t = now, and that p has just entered r. It
\* also says that no correct process is beyond r, and that the entry of p is
\* the earliest among the correct processes.
FirstToEnter(p, r) ==
  /\ enteredAt[p][r] = now
  /\ \A c \in Honest : round[c] <= r
  /\ \A c \in Honest : enteredAt[c][r] = OFF \/ enteredAt[c][r] >= now

\* The four numbered hypotheses of Lemma 5, from Section IV of the paper, word
\* for word. Lemma 5 of the paper has EXACTLY these four. Termination, which
\* is paper Lemma 7, uses only "all correct processes decide".
\*
\*   Two other clauses do NOT belong here. They are a clause decidedRound[c] =
\*   OFF, and a stable cardinality clause about the absence of an earlier
\*   certificate. Neither one is reachable from the branch hypothesis
\*   ~AllDecide of Termination. Under ~AllDecide a value can have between f+1
\*   and 2f correct precommitters and no decision, because the faulty
\*   validators abstain. The cardinality clause "< f+1" is therefore violable
\*   in that branch.
\*
\*  The paper-faithful defense against an early decision is instead the
\*  temporal fact NoDecisionBelow(r). It is threaded through WithinRound and
\*  through the TerminationThm composition, and it is discharged there from
\*  ~AllDecide.
\*
\* The propose clause and the prevote clause both carry the entry spread of
\* the round, which is Delta + TimeoutPrecommit(r - 1), and not Delta.
\* PrevoteTimeoutMargin in TendermintPartialSync derives the prevote clause. A
\* counterexample run refutes the weaker form of the paper. The precommit
\* clause needs no margin.
\* A precommit timeout only raises the round, and OnPrecommitQuorumValue holds
\* no guard on the round. A process that has left r therefore still decides on
\* a quorum of round r.
Lemma5Timeouts(r) ==
  /\ TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

Lemma5Hyp(p, r) ==
  /\ now > GST                                                      \* (1) t > GST
  /\ r > 0                                                          \* (1) r > 0
  /\ FirstToEnter(p, r)                                             \* (1) p first correct into r at t
  /\ Proposer[r] \in Honest                                         \* (2) proposer q of round r is correct
  /\ \A c \in Honest : locked[c].round <= valid[Proposer[r]].round  \* (3) lockedRound_c <= validRound_q
  /\ Lemma5Timeouts(r)                                              \* (4) three timeout inequalities

GoodRoundExists ==
  \E p \in Honest : \E r \in Rounds : Lemma5Hyp(p, r)

\* ---- The durable Lemma-5 conditions ---------------------------------------
\* WRDurable bundles the Lemma-5 conditions that stay true from the round-r
\* entry through the in-round cascade. Every milestone of the cascade carries
\* it, so each stage leaf is sound in isolation. now >= GST is the GSTLatch
\* latch, and the proposer and timeout clauses are constants.
WRDurable(r) ==
  /\ now >= GST
  /\ Proposer[r] \in Honest
  /\ TimeoutPropose(r)   > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r)   > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 0: safety invariants and small clock facts.                       *)
(*                                                                         *)
(* The safety part is inherited word for word from                         *)
(* TendermintPartialSyncRefinement, and there is nothing to prove again.   *)
(* That part is TypeOK, RcvdSubsetSent, IntegrityStep, Agreement and the   *)
(* rest. The new content is the bookkeeping of the clock and of the        *)
(* messages that the liveness layers need. Time never goes backwards, and  *)
(* a message that is sent stays sent, so the Voted* predicates are         *)
(* latches.                                                                *)
(***************************************************************************)

\* now \in Nat # OFF (OFF = -1): the clock value is never the unsent sentinel.
LEMMA NowNotOff == TypeOK => now # OFF
BY DEF TypeOK, OFF

\* Shape of the update of sentTime. Every step either leaves sentTime fixed,
\* or it overwrites exactly one entry with `now`. The honest actions that
\* broadcast, through Broadcast, and FaultyStep are the EXCEPT case. Every
\* other action leaves sentTime unchanged, and that includes Tick, Deliver and
\* stuttering.
LEMMA SentTimeStep ==
  ASSUME [Next]_vars
  PROVE  \/ sentTime' = sentTime
         \/ \E mm : sentTime' = [sentTime EXCEPT ![mm] = now]
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars

\* A message once sent stays sent: the derived pool only grows. Hence the
\* Voted* predicates latch (proved as corollaries under Spec below).
LEMMA SentMonotoneStep ==
  ASSUME TypeOK, [Next]_vars
  PROVE  sent \subseteq sent'
BY NowNotOff, SentTimeStep DEFS sent, TypeOK

\* Step form, as a top-level lemma so PTL boxes it.
LEMMA SentStepL ==
  ASSUME TypeOK, [Next]_vars, NEW m, m \in sent
  PROVE  (m \in sent)'
BY SentMonotoneStep

\* A message once sent stays sent forever. Instantiated at Prevote/Precommit
\* messages, this makes VotedPrevote / VotedPrecommit latches: the Layer-3
\* cascade turns each <>Voted* into the stable <>[]Voted* it needs.
\* Not used.
\* THEOREM SentLatch == Spec => \A m : [](m \in sent => [](m \in sent))
\* <1> SUFFICES ASSUME Spec PROVE \A m : [](m \in sent => [](m \in sent))
\*   OBVIOUS
\* <1>1. [](TypeOK /\ [Next]_vars)
\*   BY InvProof, PTL DEF Spec, Inv
\* <1>2. TAKE m
\* <1>3. [](m \in sent => (m \in sent)')
\*   BY <1>1, SentStepL, PTL
\* <1>. QED
\*   BY <1>3, PTL

\* Received sets only grow. This is the rcvd analogue of SentLatch, used by
\* paper Lemma 6 to keep already delivered lock evidence while another correct
\* receiver is being delivered.
LEMMA RcvdMonotoneStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest
  PROVE  rcvd[c] \subseteq rcvd'[c]
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

\* Not used.
\* LEMMA RcvdStepL ==
\*   ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW m, m \in rcvd[c]
\*   PROVE  (m \in rcvd[c])'
\* BY RcvdMonotoneStep

\* Not used.
\* THEOREM RcvdMsgLatch ==
\*   Spec => \A c \in Honest : \A m \in Message : [](m \in rcvd[c] => [](m \in rcvd[c]))
\* <1> SUFFICES ASSUME Spec
\*              PROVE  \A c \in Honest : \A m \in Message : [](m \in rcvd[c] => [](m \in rcvd[c]))
\*   OBVIOUS
\* <1>1. [](TypeOK /\ [Next]_vars)
\*   BY InvProof, PTL DEF Spec, Inv
\* <1>2. TAKE c \in Honest
\* <1>3. TAKE m \in Message
\* <1>4. [](m \in rcvd[c] => (m \in rcvd[c])')
\*   BY <1>1, RcvdStepL, PTL
\* <1> QED
\*   BY <1>4, PTL

\* Shape of the clock update: every step leaves now fixed (all honest, faulty
\* and delivery actions list now in UNCHANGED) or adds 1 (Tick).
LEMMA NowShape ==
  ASSUME [Next]_vars
  PROVE  now' = now \/ now' = now + 1
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars

\* Time never goes backwards.
LEMMA NowMonotoneStep ==
  ASSUME TypeOK, [Next]_vars
  PROVE  now <= now'
BY NowShape DEF TypeOK

\* The timestamp of a sent message is in the past: sentTime[m] # OFF =>
\* sentTime[m] <= now. At a broadcast, sentTime[m] := now. In every other case
\* sentTime[m] is unchanged, while now only grows. This makes a sent message
\* deliverable, because now >= sentTime[m]. With sentTime frozen it also pins
\* the DeliveryDeadline of the message. DeliverWithinDelta uses it.
SentTimeLeNow == \A mm \in Message : sentTime[mm] # OFF => sentTime[mm] <= now

LEMMA SentTimeLeNowStep ==
  ASSUME TypeOK, [Next]_vars, SentTimeLeNow
  PROVE  SentTimeLeNow'
BY NowMonotoneStep, NowShape, SentTimeStep DEFS OFF, SentTimeLeNow, TypeOK

THEOREM SentTimeLeNowInv == Spec => []SentTimeLeNow
<1> SUFFICES ASSUME Spec PROVE []SentTimeLeNow
  OBVIOUS
<1>1. SentTimeLeNow
  BY DEF Spec, Init, SentTimeLeNow, OFF
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](SentTimeLeNow => SentTimeLeNow')
  BY <1>2, SentTimeLeNowStep, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* ---- Placed here for the cascade of paper Lemma 5 ------------------------
\* ...CascadeInvariants is the head of the cascade chain. It extends
\* ...WithinRound and ...RoundProgress, which are SIBLINGS below this module.
\* No link of the chain therefore sees ...CrossRound or ...Dominator. The
\* three facts below belong here, because each proof needs only what this
\* module supplies. CrossRoundMonotoneStep keeps its name, because
\* ...CrossRound and ...Dominator cite it and read it from here.

LEMMA NatLeReflexive ==
  ASSUME NEW a \in Nat
  PROVE  a <= a
BY SMT

LEMMA CrossRoundMonotoneStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest
  PROVE  round'[c] \in Nat /\ round[c] <= round'[c]
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

ValidBelowRound == \A c \in Honest : valid[c].round <= round[c]

LEMMA ValidBelowRoundStepL ==
  ASSUME TypeOK, [Next]_vars, ValidBelowRound
  PROVE  ValidBelowRound'
BY CrossRoundMonotoneStep
DEFS Deliver, FaultyStep, HonestNext, HonestStep, LockState, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, ValidBelowRound, vars

THEOREM ValidBelowRoundInv == ASSUME Spec PROVE []ValidBelowRound
<1>1. ValidBelowRound
  BY DEF Init, Spec, ValidBelowRound
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ValidBelowRound => ValidBelowRound')
  BY <1>2, ValidBelowRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* A correct process installs locked and valid together. Later valid-only
\* updates raise valid, so the lock round never exceeds its valid round.
LockedLeValid == \A c \in Honest : locked[c].round <= valid[c].round

LEMMA LockedLeValidStepL ==
  ASSUME TypeOK, [Next]_vars, LockedLeValid
  PROVE  LockedLeValid'
<1> SUFFICES ASSUME NEW c \in Honest
             PROVE  locked'[c].round <= valid'[c].round
  BY DEF LockedLeValid
<1>ty. locked[c].round \in Int /\ valid[c].round \in Int
         /\ round[c] \in Nat
  BY DEF TypeOK, LockState, Rounds
<1>ih. locked[c].round <= valid[c].round
  BY DEF LockedLeValid
<1>fn. locked \in [Honest -> LockState] /\ valid \in [Honest -> LockState]
  BY DEF TypeOK
<1>1. CASE \E p \in Honest : OnPrevoteQuorumValueFirstTime(p)
  <2>1. PICK p \in Honest : OnPrevoteQuorumValueFirstTime(p)
    BY <1>1
  <2>2. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
          /\ locked' =
               [locked EXCEPT ![p] =
                 [value |-> prop.value, round |-> round[p]]]
          /\ valid' =
               [valid EXCEPT ![p] =
                 [value |-> prop.value, round |-> round[p]]]
    BY <2>1 DEF OnPrevoteQuorumValueFirstTime
  <2>3. CASE p = c
    <3>1. locked'[c] = valid'[c] /\ locked'[c].round = round[p]
      BY <2>2, <2>3, <1>fn
    <3> QED
      BY ONLY <3>1, <2>3, <1>ty, NatLeReflexive
  <2>4. CASE p # c
    <3>1. locked'[c] = locked[c] /\ valid'[c] = valid[c]
      BY <2>2, <2>4, <1>fn
    <3> QED
      BY <3>1, <1>ih
  <2> QED
    BY <2>3, <2>4
<1>2. CASE \E p \in Honest : OnPrevoteQuorumValueLateUpdate(p)
  BY <1>2, <1>ih, <1>ty
  DEF OnPrevoteQuorumValueLateUpdate, TypeOK, LockState
<1>3. CASE /\ ~(\E p \in Honest : OnPrevoteQuorumValueFirstTime(p))
           /\ ~(\E p \in Honest : OnPrevoteQuorumValueLateUpdate(p))
  BY <1>3, <1>ih
  DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next,
    OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnProposalNoPOL,
    OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
    OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit,
    ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM LockedLeValidInv == ASSUME Spec PROVE []LockedLeValid
<1>1. LockedLeValid
  BY DEF Init, LockedLeValid, Spec
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](LockedLeValid => LockedLeValid')
  BY <1>2, LockedLeValidStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 1: clock reachability, Spec => <>(now >= GST) branch.             *)
(*                                                                         *)
(* now >= GST must be EARNED from the clock. It is not a free latch        *)
(* variable. The latch half is [](now >= GST => [](now >= GST)). It        *)
(* follows from NowMonotone, and GSTLatch discharges it here. The          *)
(* reachability half is <>(now >= GST), which is the core of the non-Zeno  *)
(* and round-progress argument. It is NOT proved standalone here.          *)
(* ...NonZeno proves the burst core, and ...RoundProgress derives          *)
(* PostGSTRoundProgress from it. This layer holds the reusable ingredients *)
(* about the clock that those two modules consume, below.                  *)
(***************************************************************************)

\* Step form of the GST latch (top-level so PTL boxes it). now' >= now >=
\* GST.
LEMMA NowStepL ==
  ASSUME TypeOK, [Next]_vars, now >= GST
  PROVE  (now >= GST)'
BY GSTType, NowShape DEF TypeOK

\* The latch half of Layer 1: once the clock has passed GST, it stays past
\* it.
THEOREM GSTLatch == Spec => [](now >= GST => [](now >= GST))
BY InvProof, NowStepL, PTL DEFS Inv, Spec

LEMMA NowGeStepL ==
  ASSUME TypeOK, [Next]_vars, NEW t0 \in Nat, now >= t0
  PROVE  (now >= t0)'
BY NowMonotoneStep, NowShape, SMT DEF TypeOK

THEOREM NowGeLatch ==
  ASSUME Spec PROVE \A t0 \in Nat : [](now >= t0 => [](now >= t0))
<1>1. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>2. TAKE t0 \in Nat
<1>3. [](now >= t0 => (now >= t0)')
  BY <1>1, NowGeStepL, PTL
<1> QED
  BY <1>3, PTL

\* Strict form of the GST latch: once the clock has STRICTLY passed GST it stays
\* strictly past it (now is monotone). Cloned verbatim from NowStepL / GSTLatch with
\* > for >=. Used by Layer 4 (<4>S) to lift the reachability <>(now > GST) to the
\* eventually-always <>[](now > GST) needed by the Lemma-7 selected round.
LEMMA NowStepStrictL ==
  ASSUME TypeOK, [Next]_vars, now > GST
  PROVE  (now > GST)'
BY GSTType, NowShape DEF TypeOK

THEOREM GSTLatchStrict == Spec => [](now > GST => [](now > GST))
BY InvProof, NowStepStrictL, PTL DEFS Inv, Spec

\* ---- Layer 1 non-temporal support for the non-Zeno clock argument -------
\*
\* Tick strictly increments now.
LEMMA TickIncrements ==
  ASSUME Tick
  PROVE  now' = now + 1
BY DEF Tick

\* Pre-GST the delivery-deadline constraint never blocks Tick: for any
\* pending pm, DeliveryDeadline(pm[2]) >= GST + Delta >= GST >= now + 1.
LEMMA PreGSTDeadlineOk ==
  ASSUME TypeOK, now < GST,
         NEW pm \in PendingDeliveries
  PROVE  now + 1 < DeliveryDeadline(pm[2])
BY DeltaType, GSTType DEFS DeliveryDeadline, OFF, PendingDeliveries, sent, TypeOK

\* Timestamp-aware form of the same strict pre-GST fact.
LEMMA DeadlineOkThroughGST ==
  ASSUME TypeOK, SentTimeLeNow, now < GST,
         NEW pm \in PendingDeliveries
  PROVE  now + 1 < DeliveryDeadline(pm[2])
BY DeltaType, GSTType DEFS DeliveryDeadline, OFF, PendingDeliveries, sent, SentTimeLeNow, TypeOK

\* ---- ENABLED <<Tick>>_vars reduces to its three unprimed guards ----------
\* Tick advances the clock (now' = now+1) and leaves every other component of
\* `vars` fixed, so the stuttering-excluding <<.>>_vars conjunct is free: now
\* \in Nat gives now+1 # now, hence vars' # vars. ExpandENABLED then
\* witnesses the primed state (now' := now+1, everything else UNCHANGED) from
\* the three unprimed guards, which are carried verbatim as hypotheses.
\* Mirrors EnabledDecide / EnabledDeliver: the residual content of ENABLED
\* <<Tick>>_vars is exactly TickUseful /\ maximal-progress /\ deadlines.
LEMMA TickEnabledFromGuards ==
  ASSUME TypeOK,
         TickUseful,
         ~ \E p \in Honest : CanCompute(p),
         \A pm \in PendingDeliveries : now + 1 < DeliveryDeadline(pm[2])
  PROVE  ENABLED <<Tick>>_vars
BY ExpandENABLED DEFS Tick, TypeOK, vars

\* Tick is ENABLED from FULL quiescence, given a live timer, which is
\* TickUseful. Full quiescence means that everything is delivered, so
\* PendingDeliveries = {}, and that no honest computation is possible. With
\* PendingDeliveries empty the delivery-deadline guard is VACUOUS. This lemma
\* therefore needs no relation to GST at all, and it holds before GST and
\* after it alike. This is the reusable enabling ingredient of the non-Zeno
\* argument after GST, which ...NonZeno proves. That argument reaches full
\* quiescence, by the well-founded measure of burst termination. It also needs
\* WF1 stability under the finitely many detours of a faulty send or of a
\* delivery.
LEMMA TickEnabledFromFullQuiescence ==
  ASSUME TypeOK,
         PendingDeliveries = {},
         ~ \E p \in Honest : CanCompute(p),
         TickUseful
  PROVE  ENABLED <<Tick>>_vars
BY TickEnabledFromGuards

\* ==== Two inductive invariants for the non-Zeno clock argument ============
\* (1) ProposeTimerArmedOp: an honest validator in step "propose" has its
\* propose timer armed. (2) DecidedStepOp: decision = nil and step # "decided"
\* move together, because only OnPrecommitQuorumValue sets step = "decided",
\* and it does so with a real value. Both are reusable []-facts for the
\* reachability argument of the non-Zeno proof in ...NonZeno. They are stated
\* with NAMED OPERATORS, so that the inductive PTL lift sees an atomic primed
\* invariant. They are then bridged to the forms that the clock lemmas
\* consume.
ProposeTimerArmedOp == \A q \in Honest : step[q] = "propose" => timer[q]["propose"] # OFF
DecidedStepOp       == \A q \in Honest : decision[q] = nil   => step[q] # "decided"

\* nil is not an application value (Russell set RR = {x \in Values : x \notin x}
\* witnesses \E v : v \notin Values, so the CHOOSE in `nil` lands outside Values).
\* Mirrors TendermintVotingProofs!NilNotInValues (above this module in the chain,
\* not in scope here). Shows a decided/proposed value is non-nil. (Placed here so the
\* decide-step invariant below can use it.)
LEMMA NilNotInValues == nil \notin Values
<1> DEFINE RR == { x \in Values : x \notin x }
<1>1. RR \notin Values
  BY DEF RR
<1>2. QED
  BY <1>1 DEF nil

\* ---- (1) ProposeTimerArmed -----------------------------------------------
\* The inductive step. Only two kinds of successor have step'[c] = "propose".
\* Case A is a step that leaves both the step of c and its propose timer
\* untouched. Case B is an entry into a round, by OnTimeoutPrecommit or by
\* SkipRound, which re-arms the timer with ResetTimersFor to now +
\* TimeoutPropose(_). That value is a Nat, so it is not OFF. Actions that move
\* c off "propose" are vacuous. The proof is decomposed action by action,
\* because the bundled disjunction is beyond Zenon and SMT.
LEMMA ProposeTimerArmedStepL ==
  ASSUME TypeOK, [Next]_vars, ProposeTimerArmedOp
  PROVE  ProposeTimerArmedOp'
BY T0ProposeType, TDeltaType
DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OFF, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ProposeTimerArmedOp, ResetTimersFor, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TimeoutPropose, TimerType, TypeOK, vars

LEMMA ProposeTimerArmedBox ==
  [](ProposeTimerArmedOp <=> (\A q \in Honest : step[q] = "propose" => timer[q]["propose"] # OFF))
BY PTL DEF ProposeTimerArmedOp

THEOREM ProposeTimerArmedInv ==
  Spec => [](\A q \in Honest : step[q] = "propose" => timer[q]["propose"] # OFF)
<1> SUFFICES ASSUME Spec
             PROVE  [](\A q \in Honest : step[q] = "propose" => timer[q]["propose"] # OFF)
  OBVIOUS
<1>1. ProposeTimerArmedOp
  BY T0ProposeType, TDeltaType
     DEF Spec, Init, ProposeTimerArmedOp, TimeoutPropose, OFF, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ProposeTimerArmedOp => ProposeTimerArmedOp')
  BY <1>2, ProposeTimerArmedStepL, PTL
<1>4. []ProposeTimerArmedOp
  BY <1>1, <1>3, PTL
<1>. QED
  BY <1>4, ProposeTimerArmedBox, PTL

\* ---- (2) DecidedStep -------------------------------------------------------
\* Inductive step. Only OnPrecommitQuorumValue moves decision off nil (and sets
\* step = "decided" with a real Value). For any other action: decision is
\* unchanged, and step'[c] = "decided" forces step[c] = "decided" (no other action
\* creates "decided"). Decomposed action-by-action.
LEMMA DecidedStepStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, DecidedStepOp
  PROVE  DecidedStepOp'
BY NilNotInValues
DEFS DecidedStepOp, Deliver, FaultyStep, HonestNext, HonestStep, Message, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrecommitMsg, PrevoteMsg, ProposalMsg, Propose, RcvdSubsetSent, RProposals, RProposalsFromProposerAt, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

LEMMA DecidedStepBox ==
  [](DecidedStepOp <=> (\A q \in Honest : decision[q] = nil => step[q] # "decided"))
BY PTL DEF DecidedStepOp

THEOREM DecidedStepInv ==
  Spec => [](\A q \in Honest : decision[q] = nil => step[q] # "decided")
<1> SUFFICES ASSUME Spec
             PROVE  [](\A q \in Honest : decision[q] = nil => step[q] # "decided")
  OBVIOUS
<1>1. DecidedStepOp
  BY DEF Spec, Init, DecidedStepOp
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](DecidedStepOp => DecidedStepOp')
  BY <1>2, DecidedStepStepL, PTL
<1>4. []DecidedStepOp
  BY <1>1, <1>3, PTL
<1>. QED
  BY <1>4, DecidedStepBox, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 2: decision latch (inherited). Once an honest validator decides,  *)
(* it stays decided, so proving <>HasDecided(p) is enough and it is        *)
(* stable. Rests purely on the discharged IntegrityInv.           *)
(***************************************************************************)
\* The single-step decision-stability fact, as a top-level lemma so PTL boxes
\* it (a numbered in-context implication would NOT be lifted to []). decision
\* keeps its non-nil value by IntegrityStep, so HasDecided is preserved.
LEMMA DecStepL ==
  ASSUME NEW p \in Honest, IntegrityStep, HasDecided(p)
  PROVE  HasDecided(p)'
BY DEF IntegrityStep, HasDecided

THEOREM DecLatch ==
  Spec => \A p \in Honest : [](HasDecided(p) => []HasDecided(p))
<1> SUFFICES ASSUME Spec
             PROVE  \A p \in Honest : [](HasDecided(p) => []HasDecided(p))
  OBVIOUS
<1>1. []IntegrityStep
  BY IntegrityInv
<1>2. TAKE p \in Honest
<1>3. [](HasDecided(p) => HasDecided(p)')
  BY <1>1, DecStepL, PTL
<1>. QED
  BY <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 3 support: set / counting lemmas (non-temporal).                  *)
(*                                                                         *)
(* If every honest validator has voted v at r, then the quorum predicate   *)
(* over the global pool holds. The witness is the all-honest quorum of     *)
(* 2f+1 that QuorumAvailable supplies. It lies inside Honest, and          *)
(* therefore inside the set of the senders of v at r. These are the        *)
(* cascade stages c and e of the Layer-3 table of the ADR. They are kept   *)
(* non-temporal, so that the WF1 staircase only has to chain them.         *)
(***************************************************************************)
LEMMA AllHonestPrevoteQuorum ==
  ASSUME NEW v \in ValuesOrNil, NEW r \in Rounds,
         \A p \in Honest : VotedPrevote(p, v, r)
  PROVE  B!ExistsPrevoteQuorum(v, r)
BY QuorumAvailable DEFS B!ExistsPrevoteQuorum, B!PrevotesAt, B!PrevoteSendersFor, B!SentPrevotes, Prevote, VotedPrevote

LEMMA AllHonestPrecommitQuorum ==
  ASSUME NEW v \in ValuesOrNil, NEW r \in Rounds,
         \A p \in Honest : VotedPrecommit(p, v, r)
  PROVE  B!ExistsPrecommitQuorum(v, r)
BY QuorumAvailable DEFS B!ExistsPrecommitQuorum, B!PrecommitsAt, B!PrecommitSendersFor, B!SentPrecommits, Precommit, VotedPrecommit

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 3 support: round-pinning counting lemmas (non-temporal).          *)
(*                                                                         *)
(* The quantitative core that the symbolic chain above never needed. Every *)
(* Byzantine quorum of 2f+1 holds f+1 honest validators or more, by the    *)
(* pigeonhole principle on |Validators| = 3f+1 and |Faulty| <= f. This is  *)
(* what converts one clause of WRDurable into another. One clause says     *)
(* "fewer than f+1 honest validators precommitted any value at r2 < r". It *)
(* becomes "no precommit QUORUM can exist at r2 < r in the rcvd of any     *)
(* honest validator". That is the fact that pins a deciding validator to   *)
(* round r, and not to an earlier round. It closes the family of           *)
(* early-decision counterexamples at the level of the PROOF, and not only  *)
(* at the level of the statement. These facts feed Stage F, which is the   *)
(* decide stage.                                                           *)
(***************************************************************************)

\* Every Byzantine quorum holds at least f+1 honest members. A quorum has 2f+1
\* of the 3f+1 validators or more, so |Q \cap Honest| = |Q| - |Q \cap Faulty|
\* >= (2f+1) - f.
LEMMA QuorumHonestLowerBound ==
  ASSUME NEW Q \in ByzQuorum
  PROVE  Cardinality(Q \cap Honest) >= f + 1
BY FaultBoundType, FaultyCardinality, FaultyType, FS_CardinalityType, FS_Difference, FS_Intersection, FS_Subset, ValidatorsFinite
DEFS ByzQuorum, Honest

\* A precommit RECEIVED by an honest validator is a genuine Precommit message
\* in the global pool: rcvd[c] \subseteq sent + the PrecommitMsg record shape.
LEMMA PrecommitSenderVoted ==
  ASSUME TypeOK, NEW c \in Honest, rcvd[c] \subseteq sent,
         NEW rr \in Rounds, NEW vv \in ValuesOrNil, NEW s,
         s \in RPrecommitSendersFor(c, vv, rr)
  PROVE  Precommit(s, rr, vv) \in sent
BY DEFS Message, Precommit, PrecommitMsg, PrevoteMsg, ProposalMsg, RPrecommits, RPrecommitSendersFor, sent

LEMMA PrevoteSenderInRcvd ==
  ASSUME TypeOK, NEW c \in Honest,
         NEW rr \in Rounds, NEW vv \in ValuesOrNil, NEW s,
         s \in RPrevoteSendersFor(c, vv, rr)
  PROVE  Prevote(s, rr, vv) \in rcvd[c]
BY DEFS Message, PrecommitMsg, Prevote, PrevoteMsg, ProposalMsg, RPrevotes, RPrevoteSendersFor, TypeOK

\* No precommit quorum of an earlier round is visible to an honest validator.
\* Suppose that fewer than f+1 honest validators precommitted the value vv at
\* round rr. Any quorum of 2f+1 needs f+1 honest precommitters or more. c can
\* therefore not hold a precommit quorum for vv at rr in rcvd[c]. This is
\* applied with the clause of WRDurable at every r2 < r.
LEMMA NoEarlyQuorumInRcvd ==
  ASSUME TypeOK, NEW c \in Honest, rcvd[c] \subseteq sent,
         NEW rr \in Rounds, NEW vv \in Values,
         Cardinality({cc \in Honest : VotedPrecommit(cc, vv, rr)}) < f + 1
  PROVE  ~ RExistsPrecommitQuorum(c, vv, rr)
BY FaultBoundType, FS_CardinalityType, FS_Intersection, FS_Subset, PrecommitSenderVoted, QuorumHonestLowerBound, ValidatorsFinite
DEFS ByzQuorum, Honest, RExistsPrecommitQuorum, ValuesOrNil, VotedPrecommit

-----------------------------------------------------------------------------
(***************************************************************************)
(* HISTORICAL PAPER LEMMA 5 SCAFFOLD.                                      *)
(*                                                                         *)
(* The published statement, which mentions only a decision, is false in    *)
(* this operational model. A Byzantine message can reach a correct process *)
(* for the first time after the hypothesis, and it can create a new        *)
(* correct lock below r. The active interface in                           *)
(* TendermintPartialSyncTerminationWithinRound is Lemma5OrPriorLock.          *)
(*                                                                         *)
(* This is a BOUNDED-RESPONSE property: the leads-to target conjoins the   *)
(* clock predicate now <= enteredAt[p][r] + 4*Delta + timeoutPrecommit     *)
(* (r-1). enteredAt[p][r] latches t and decidedRound latches, so the       *)
(* conjunction holds at exactly one instant (the decision instant); the    *)
(* ~> therefore holds iff every correct decides by the paper's deadline.   *)
(*                                                                         *)
(* PROOF SKETCH, from page 11 of the paper. This is the intended           *)
(* mechanization.                                                          *)
(*                                                                         *)
(* By hypothesis (1), p ran OnTimeoutPrecommit at r-1, so it held a        *)
(* precommit quorum of 2f+1 at r-1 by t. Gossip delivers that quorum to    *)
(* every correct process before t+Delta, because the DeliveryDeadline      *)
(* invariant bounds the delay after GST by Delta. They reach r-1, by       *)
(* SkipRound, and they arm timeoutPrecommit(r-1). ALL correct processes    *)
(* therefore enter r by t + Delta + timeoutPrecommit(r-1). Call that       *)
(* instant (i).                                                            *)
(*                                                                         *)
(* The correct proposer q of hypothesis (2) broadcasts its value by (i).   *)
(* Condition (4) gives timeoutPropose(r) > 2*Delta +                       *)
(* timeoutPrecommit(r-1), which keeps every propose timer live until the   *)
(* proposal arrives, before t + 2*Delta + timeoutPrecommit(r-1). By        *)
(* hypothesis (3), and by lines 22 and 28, all correct processes PREVOTE   *)
(* the value of q. Lines 36 and 40 then make all of them PRECOMMIT by t +  *)
(* 3*Delta + timeoutPrecommit(r-1). Line 49 makes all of them DECIDE by t  *)
(* + 4*Delta + timeoutPrecommit(r-1). The conditions timeoutPrevote(r) >   *)
(*   2*Delta and timeoutPrecommit(r) > 2*Delta of (4) stop the prevote     *)
(*   timer and the precommit timer from preempting the cascade.            *)
(*                                                                         *)
(* MECHANIZATION. The chain TendermintPartialSyncTerminationCascade           *)
(* discharges the content that is bounded in time. It does so in two legs, *)
(* and the legs meet at the decide evidence. The Case A leg is Lemma5Hyp   *)
(* ~> ProposalMilestone ~> DecideEvidence ~> SomeCorrectDecided. The Case  *)
(* B leg is Lemma5Hyp ~> EarlyPolka ~> DecideEvidence. Each leg is a       *)
(* pinned ceiling together with an unbounded clock, and it is not a WF1.   *)
(* CascadeCore carries the quantitative content as a region invariant, and *)
(* the last stage is the only WF1. Every milestone carries WRDurable,      *)
(* which holds the stable conditions of Lemma 5, so each leaf is sound in  *)
(* isolation.                                                              *)
(*                                                                         *)
(* SOUNDNESS NOTE. The antecedent is the exact set of hypotheses of the    *)
(* paper. It is NOT the co-location of all honest validators at "propose". *)
(* The decisive clause that excludes the early-decision counterexample is  *)
(* the STABLE precondition of Lemma 7:                                     *)
(*   \A r2 < r, v :                                                        *)
(*     Cardinality({c \in Honest : VotedPrecommit(c,v,r2)}) < f+1          *)
(* That clause says that fewer than f+1 correct processes precommitted any *)
(* value below r. A clause decidedRound[c] = OFF alone is INSUFFICIENT. It *)
(* blocks a decision before t, but a precommit quorum for one value can    *)
(* form before GST and reach a correct process only after GST. That        *)
(* process can then decide at r2 < r, strictly AFTER t, because the        *)
(* deciding round in OnPrecommitQuorumValue is \E r2 \in Rounds, and it is *)
(* not tied to round[p]. Every quorum of 2f+1 needs f+1 correct            *)
(* precommitters or more. The clause on the count therefore makes a        *)
(* certificate at any r2 < r impossible to complete, even for f faulty     *)
(* validators. No correct process can then decide before r, and every      *)
(* decision latches decidedRound = r.                                      *)
(***************************************************************************)

\* decidedRound and decision move in lockstep: a correct validator has latched a
\* deciding round iff it has decided. Both are written ONLY by
\* OnPrecommitQuorumValue (guarded decision[c]=nil), so the biconditional is
\* inductive (and TLC-enumerable). Yields the decidedRound[c]=rr latch.
DecidedRoundConsistent ==
  \A c \in Honest : (decidedRound[c] = OFF) <=> (decision[c] = nil)

\* The step: the biconditional is preserved. Either decision[c] and
\* decidedRound[c] are BOTH unchanged, which every action except
\* OnPrecommitQuorumValue(c) does, or OnPrecommitQuorumValue(c) sets BOTH. It
\* sets decision[c] to a real Value, by NilNotInValues, and it sets
\* decidedRound[c] to a round that is not OFF. The two sides therefore flip
\* together.
LEMMA DecRoundConsistentStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, DecidedRoundConsistent
  PROVE  DecidedRoundConsistent'
BY NilNotInValues
DEFS DecidedRoundConsistent, Deliver, FaultyStep, HonestNext, HonestStep, Message, Next, OFF, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrecommitMsg, PrevoteMsg, ProposalMsg, Propose, RcvdSubsetSent, Rounds, RProposals, RProposalsFromProposerAt, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

THEOREM DecidedRoundConsistentInv == Spec => []DecidedRoundConsistent
<1> SUFFICES ASSUME Spec PROVE []DecidedRoundConsistent
  OBVIOUS
<1>1. DecidedRoundConsistent
  BY DEF Spec, Init, DecidedRoundConsistent, OFF
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](DecidedRoundConsistent => DecidedRoundConsistent')
  BY <1>2, DecRoundConsistentStepL, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* DecidedBackedByQuorum: a correct validator that has latched a deciding
\* round holds a precommit quorum for its decision at that round, in its OWN
\* rcvd. The guard of the deciding action establishes it, because
\* OnPrecommitQuorumValue needs RExistsPrecommitQuorum and keeps rcvd
\* UNCHANGED. It is preserved because decision and decidedRound latch, with
\* OnPrecommitQuorumValue as their only writer, and because rcvd only grows,
\* so the quorum persists. This is the fact that step <1>und of
\* EvidenceStability consumes: an honest decision is backed by a precommit
\* quorum at its decidedRound.
DecidedBackedByQuorum ==
  \A c \in Honest : decidedRound[c] # OFF =>
    RExistsPrecommitQuorum(c, decision[c], decidedRound[c])

\* The step: the backing quorum is preserved. rcvd[c] only grows, so a
\* precommit quorum in rcvd[c] persists, because RExistsPrecommitQuorum is
\* monotone in rcvd. The deciding action OnPrecommitQuorumValue(c) installs
\* the quorum from its own guard. Every other action leaves the pair
\* (decision[c], decidedRound[c]) fixed, so the induction hypothesis carries
\* over.
LEMMA DecBackedByQuorumStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, DecidedBackedByQuorum
  PROVE  DecidedBackedByQuorum'
<1> SUFFICES ASSUME NEW c \in Honest, decidedRound'[c] # OFF
             PROVE  RExistsPrecommitQuorum(c, decision[c], decidedRound[c])'
  BY DEF DecidedBackedByQuorum
\* rcvd is non-decreasing at every honest index. FaultyStep adds the first
\* correct receipt of one Byzantine message at one index.
<1>mono. rcvd[c] \subseteq rcvd'[c]
  BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
    OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL,
    OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
    ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars
\* a precommit quorum in rcvd[c] is monotone: it survives rcvd growth.
<1>persist. \A v \in ValuesOrNil, rr \in Rounds :
              RExistsPrecommitQuorum(c, v, rr) => RExistsPrecommitQuorum(c, v, rr)'
  BY <1>mono DEFS RExistsPrecommitQuorum, RPrecommits, RPrecommitSendersFor
<1>1. CASE \E p \in Honest : OnPrecommitQuorumValue(p)
  BY <1>1, <1>persist
  DEFS DecidedBackedByQuorum, Message, OFF, OnPrecommitQuorumValue, PrecommitMsg, PrevoteMsg,
    ProposalMsg, RcvdSubsetSent, RExistsPrecommitQuorum, RPrecommits, RPrecommitSendersFor, RProposals,
    RProposalsFromProposerAt, sent, TypeOK, ValuesOrNil
<1>2. CASE ~(\E p \in Honest : OnPrecommitQuorumValue(p))
  <2>1. decidedRound' = decidedRound /\ decision' = decision
    BY <1>2 DEF Next, HonestNext, HonestStep, Propose, OnTimeoutPropose,
               OnProposalNoPOL, OnProposalWithPOL, ScheduleTimeoutPrevote,
               OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
               OnPrevoteQuorumNil, OnTimeoutPrevote, ScheduleTimeoutPrecommit,
               OnTimeoutPrecommit, SkipRound, Deliver, FaultyStep, Tick, vars
  <2>2. decidedRound[c] # OFF /\ decidedRound[c] \in Rounds /\ decision[c] \in ValuesOrNil
    BY <2>1 DEF TypeOK, OFF
  <2>3. RExistsPrecommitQuorum(c, decision[c], decidedRound[c])
    BY <2>2 DEF DecidedBackedByQuorum
  <2> QED
    BY <2>1, <2>2, <2>3, <1>persist
    DEF RExistsPrecommitQuorum, RPrecommitSendersFor, RPrecommits, ValuesOrNil
<1> QED
  BY <1>1, <1>2

THEOREM DecidedBackedByQuorumInv == Spec => []DecidedBackedByQuorum
<1> SUFFICES ASSUME Spec PROVE []DecidedBackedByQuorum
  OBVIOUS
<1>1. DecidedBackedByQuorum
  BY DEF Spec, Init, DecidedBackedByQuorum, OFF
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](DecidedBackedByQuorum => DecidedBackedByQuorum')
  BY <1>2, DecBackedByQuorumStepL, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* Step for the latch: once decidedRound[c] = rr (a real round, # OFF), it is
\* fixed. By DecidedRoundConsistent, decidedRound[c] # OFF => decision[c] # nil,
\* so OnPrecommitQuorumValue(c) (guarded decision[c]=nil) is disabled; it is the
\* sole writer of decidedRound[c], so the value cannot change.
LEMMA DecRoundRStepL ==
  ASSUME TypeOK, [Next]_vars, DecidedRoundConsistent,
         NEW c \in Honest, NEW rr \in Rounds, decidedRound[c] = rr
  PROVE  (decidedRound[c] = rr)'
BY DEFS DecidedRoundConsistent, Deliver, FaultyStep, HonestNext, HonestStep, Next, OFF, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

\* The latch: once a correct validator has decided in round rr, decidedRound[c] =
\* rr forever. Turns each per-honest <>(decidedRound[c]=rr) into the
\* <>[](decidedRound[c]=rr) the finite-set lift consumes.
THEOREM DecidedRoundRLatch ==
  ASSUME NEW rr \in Rounds
  PROVE  Spec => \A c \in Honest :
                   [](decidedRound[c] = rr => [](decidedRound[c] = rr))
<1> SUFFICES ASSUME Spec
             PROVE  \A c \in Honest :
                      [](decidedRound[c] = rr => [](decidedRound[c] = rr))
  OBVIOUS
<1>1. [](TypeOK /\ [Next]_vars /\ DecidedRoundConsistent)
  BY InvProof, DecidedRoundConsistentInv, PTL DEF Spec, Inv
<1>2. TAKE c \in Honest
<1>3. [](decidedRound[c] = rr => (decidedRound[c] = rr)')
  BY <1>1, DecRoundRStepL, PTL
<1>. QED
  BY <1>3, PTL

(***************************************************************************)
(* The bounded-delivery lemma DeliverWithinDelta, which is Route B. It is  *)
(* the reusable spine of step <2>1 of stage F, and of the analogous        *)
(* delivery sub-stages of the other cascade stages. It is built as one WF1 *)
(* on the fair action Deliver(c). The pending region DelivPending is       *)
(* stable. Deliver(c) delivers m, and the delivery-deadline gate stops     *)
(* Tick from pushing `now` past the DeliveryDeadline of m. That deadline   *)
(* is at most t0+Delta. Deliver(c) is continuously enabled while m is      *)
(* pending, so WF forces the delivery by the deadline.                     *)
(***************************************************************************)

\* Only Tick advances `now`. Any step that is not a Tick leaves the clock
\* fixed, because every honest action, every faulty action and Deliver list
\* now in UNCHANGED.
LEMMA NowStaysUnlessTick ==
  ASSUME [Next]_vars, ~Tick
  PROVE  now' = now
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, vars

\* Per-message send discipline (only constrains honest senders).
HonestSentOK(m) ==
  m.sender \in Honest =>
    /\ m.round <= round[m.sender]
    /\ (m.type = "Prevote"   /\ m.round = round[m.sender] => step[m.sender] # "propose")
    /\ (m.type = "Precommit" /\ m.round = round[m.sender] => step[m.sender] \in {"precommit", "decided"})

SentInv == \A m \in sent : HonestSentOK(m)

\* ---- SentInv is preserved by each action shape (helpers) -----------------

\* Actions leaving sentTime / round / step all fixed (Schedule*, the late
\* valid update, Deliver, Tick, stuttering): SentInv references only these.
LEMMA UnchangedPreservesSentInv ==
  ASSUME SentInv, sentTime' = sentTime, round' = round, step' = step
  PROVE  SentInv'
BY DEFS HonestSentOK, sent, SentInv

\* A proposer's Propose adds a Proposal at round[p]; step/round unchanged. The
\* new message is a Proposal, so the prevote/precommit clauses are vacuous.
LEMMA ProposePreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Honest,
         NEW v \in Values, NEW vr \in Rounds \cup {-1},
         sentTime' = [sentTime EXCEPT ![Proposal(p, round[p], v, vr)] = now],
         round' = round, step' = step
  PROVE  SentInv'
BY HonestSubValidators, MsgProposal, SentExtend DEFS HonestSentOK, Proposal, Rounds, SentInv, TypeOK

\* A prevote broadcast (OnTimeoutPropose / OnProposal{NoPOL,WithPOL}): guarded
\* step[p]="propose", emits a Prevote at round[p], moves step to "prevote".
LEMMA PrevoteBroadcastPreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Honest, NEW vid \in ValuesOrNil,
         step[p] = "propose",
         sentTime' = [sentTime EXCEPT ![Prevote(p, round[p], vid)] = now],
         round' = round, step' = [step EXCEPT ![p] = "prevote"]
  PROVE  SentInv'
BY HonestSubValidators, MsgPrevote, SentExtend DEFS HonestSentOK, Prevote, Rounds, SentInv, TypeOK

\* A broadcast of a precommit, by OnPrevoteQuorumValueFirstTime, by
\* OnPrevoteQuorumNil or by OnTimeoutPrevote. It is guarded by step[p] =
\* "prevote". It emits a Precommit at round[p], and it moves step to
\* "precommit". That satisfies BOTH clauses, so there is nothing to exclude
\* for the messages that p already has.
LEMMA PrecommitBroadcastPreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Honest, NEW vid \in ValuesOrNil,
         sentTime' = [sentTime EXCEPT ![Precommit(p, round[p], vid)] = now],
         round' = round, step' = [step EXCEPT ![p] = "precommit"]
  PROVE  SentInv'
BY HonestSubValidators, MsgPrecommit, SentExtend DEFS HonestSentOK, Precommit, Rounds, SentInv, TypeOK

\* Decide (OnPrecommitQuorumValue): step[p] -> "decided", sent/round fixed.
\* "decided" satisfies both clauses for all of p's messages.
LEMMA DecidePreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Honest,
         sentTime' = sentTime, round' = round, step' = [step EXCEPT ![p] = "decided"]
  PROVE  SentInv'
BY DEFS HonestSentOK, sent, SentInv, TypeOK

\* Round advance (OnTimeoutPrecommit / SkipRound): round[p] -> r2 > round[p],
\* step[p] -> "propose", sent fixed. p's messages all sit below r2 (SentInv's
\* round clause), so the current-round step clauses are vacuous at r2.
LEMMA RoundAdvancePreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Honest, NEW r2 \in Rounds, r2 > round[p],
         sentTime' = sentTime,
         round' = [round EXCEPT ![p] = r2], step' = [step EXCEPT ![p] = "propose"]
  PROVE  SentInv'
BY DEFS HonestSentOK, Message, PrecommitMsg, PrevoteMsg, ProposalMsg, Rounds, sent, SentInv, TypeOK

\* A faulty send. The sender of the new message is faulty, and therefore not
\* in Honest. The honest-only clauses of SentInv are vacuous for it, and round
\* and step are fixed.
LEMMA FaultyPreservesSentInv ==
  ASSUME TypeOK, SentInv, NEW p \in Faulty, NEW m0 \in Message, m0.sender = p,
         sentTime' = [sentTime EXCEPT ![m0] = now], round' = round, step' = step
  PROVE  SentInv'
BY SentExtend DEFS Honest, HonestSentOK, SentInv

\* The inductive step: dispatch each action to the matching helper.
LEMMA SentInvStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, SentInv
  PROVE  SentInv'
<1>1. CASE \E p \in Honest : HonestNext(p)
  <2> SUFFICES ASSUME NEW p \in Honest, HonestNext(p) PROVE SentInv'
    BY <1>1
  <2>sub. rcvd[p] \subseteq sent
    BY DEF RcvdSubsetSent
  <2>1. CASE Propose(p)
    BY <2>1, ProposePreservesSentInv DEFS Broadcast, getValue, LockState, Propose, TypeOK, ValuesOrNil
  <2>2. CASE OnTimeoutPropose(p)
    BY <2>2, PrevoteBroadcastPreservesSentInv DEFS Broadcast, OnTimeoutPropose, ValuesOrNil
  <2>3. CASE OnProposalNoPOL(p)
    BY <2>3, <2>sub, PrevoteBroadcastPreservesSentInv
    DEFS Broadcast, Message, OnProposalNoPOL, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>4. CASE OnProposalWithPOL(p)
    BY <2>4, <2>sub, PrevoteBroadcastPreservesSentInv
    DEFS Broadcast, Message, OnProposalWithPOL, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>5. CASE ScheduleTimeoutPrevote(p)
    BY <2>5, UnchangedPreservesSentInv DEF ScheduleTimeoutPrevote
  <2>6. CASE OnPrevoteQuorumValueFirstTime(p)
    BY <2>6, <2>sub, PrecommitBroadcastPreservesSentInv
    DEFS Broadcast, Message, OnPrevoteQuorumValueFirstTime, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>7. CASE OnPrevoteQuorumValueLateUpdate(p)
    BY <2>7, UnchangedPreservesSentInv DEF OnPrevoteQuorumValueLateUpdate
  <2>8. CASE OnPrevoteQuorumNil(p)
    BY <2>8, PrecommitBroadcastPreservesSentInv DEFS Broadcast, OnPrevoteQuorumNil, ValuesOrNil
  <2>9. CASE OnTimeoutPrevote(p)
    BY <2>9, PrecommitBroadcastPreservesSentInv DEFS Broadcast, OnTimeoutPrevote, ValuesOrNil
  <2>10. CASE ScheduleTimeoutPrecommit(p)
    BY <2>10, UnchangedPreservesSentInv DEF ScheduleTimeoutPrecommit
  <2>11. CASE OnPrecommitQuorumValue(p)
    BY <2>11, DecidePreservesSentInv DEFS OnPrecommitQuorumValue, sent
  <2>12. CASE OnTimeoutPrecommit(p)
    BY <2>12, RoundAdvancePreservesSentInv DEFS OnTimeoutPrecommit, Rounds, TypeOK
  <2>13. CASE \E r \in Rounds : SkipRound(p, r)
    BY <2>13, RoundAdvancePreservesSentInv DEF SkipRound
  <2>14. CASE Deliver(p)
    BY <2>14, UnchangedPreservesSentInv DEF Deliver
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
       <2>11, <2>12, <2>13, <2>14 DEF HonestNext, HonestStep
<1>2. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>2, FaultyPreservesSentInv DEF FaultyStep
<1>3. CASE Tick
  BY <1>3, UnchangedPreservesSentInv DEF Tick
<1>4. CASE UNCHANGED vars
  BY <1>4, UnchangedPreservesSentInv DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM SentInvInv == Spec => []SentInv
<1> SUFFICES ASSUME Spec PROVE []SentInv
  OBVIOUS
<1>1. SentInv
  BY DEF Spec, Init, SentInv, HonestSentOK, sent, OFF
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](SentInv => SentInv')
  BY <1>2, SentInvStepL, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* No rebroadcast: a timestamp is frozen once it is set. Each honest broadcast
\* reaches a FRESH slot, where sentTime[msg] = OFF. The send discipline of
\* SentInv, together with the phase guard of the action, contradicts a copy
\* that was already sent at the current round. Propose is guarded directly
\* against a second proposal. The guard sentTime[m] = OFF of FaultyStep blocks
\* a faulty re-send. This is necessary so that the DeliveryDeadline of a
\* pending message stays at or below t0+Delta across the ticks. A rebroadcast
\* would reset sentTime[m] := now, and it would push the deadline out.
\* DeliverWithinDelta rests on this.
SentTimeFrozenPred ==
  \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]

\* If a step overwrites only a slot that was OFF, every already-set timestamp is
\* frozen: the overwritten slot is distinct from any set slot.
LEMMA FreshKeepsFrozen ==
  ASSUME TypeOK, NEW msg \in Message, sentTime[msg] = OFF,
         sentTime' = [sentTime EXCEPT ![msg] = now]
  PROVE  SentTimeFrozenPred
BY DEFS SentTimeFrozenPred, TypeOK

\* A prevote slot at the current round is unsent while the sender is at "propose"
\* (SentInv: a prevote at round[p] would force step[p] # "propose").
LEMMA PrevoteFresh ==
  ASSUME SentInv, NEW p \in Honest, NEW vid \in ValuesOrNil, step[p] = "propose"
  PROVE  Prevote(p, round[p], vid) \notin sent
BY DEFS HonestSentOK, Prevote, SentInv

\* A precommit slot at the current round is unsent while the sender is at
\* "prevote" (SentInv: a precommit at round[p] would force step[p] in
\* {precommit,decided}).
LEMMA PrecommitFresh ==
  ASSUME SentInv, NEW p \in Honest, NEW vid \in ValuesOrNil, step[p] = "prevote"
  PROVE  Precommit(p, round[p], vid) \notin sent
BY DEFS HonestSentOK, Precommit, SentInv

\* The inductive step: every action either leaves sentTime fixed, which
\* freezes it trivially, or it broadcasts a FRESH message. Propose is fresh by
\* its guard. A prevote is fresh by PrevoteFresh, and a precommit by
\* PrecommitFresh. A faulty message is fresh by the guard sentTime = OFF.
LEMMA SentTimeFrozenStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars
  PROVE  [SentTimeFrozenPred]_vars
<1>1. CASE \E p \in Honest : HonestNext(p)
  <2> SUFFICES ASSUME NEW p \in Honest, HonestNext(p) PROVE SentTimeFrozenPred
    BY <1>1
  <2>sub. rcvd[p] \subseteq sent
    BY DEF RcvdSubsetSent
  <2>v. p \in Validators /\ round[p] \in Rounds
    BY HonestSubValidators DEF TypeOK
  <2>1. CASE Propose(p)
    BY <2>1, <2>v, FreshKeepsFrozen, MsgProposal
    DEFS Broadcast, getValue, LockState, Proposal, Propose, sent, TypeOK, ValuesOrNil
  <2>2. CASE OnTimeoutPropose(p)
    BY <2>2, <2>v, FreshKeepsFrozen, MsgPrevote, PrevoteFresh DEFS Broadcast, OnTimeoutPropose, sent, ValuesOrNil
  <2>3. CASE OnProposalNoPOL(p)
    BY <2>3, <2>sub, <2>v, FreshKeepsFrozen, MsgPrevote, PrevoteFresh
    DEFS Broadcast, Message, OnProposalNoPOL, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>4. CASE OnProposalWithPOL(p)
    BY <2>4, <2>sub, <2>v, FreshKeepsFrozen, MsgPrevote, PrevoteFresh
    DEFS Broadcast, Message, OnProposalWithPOL, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>5. CASE ScheduleTimeoutPrevote(p)
    BY <2>5 DEF ScheduleTimeoutPrevote, SentTimeFrozenPred
  <2>6. CASE OnPrevoteQuorumValueFirstTime(p)
    BY <2>6, <2>sub, <2>v, FreshKeepsFrozen, MsgPrecommit, PrecommitFresh
    DEFS Broadcast, Message, OnPrevoteQuorumValueFirstTime, PrecommitMsg, PrevoteMsg, ProposalMsg, RProposals, RProposalsFromProposerAt, sent, ValuesOrNil
  <2>7. CASE OnPrevoteQuorumValueLateUpdate(p)
    BY <2>7 DEF OnPrevoteQuorumValueLateUpdate, SentTimeFrozenPred
  <2>8. CASE OnPrevoteQuorumNil(p)
    BY <2>8, <2>v, FreshKeepsFrozen, MsgPrecommit, PrecommitFresh DEFS Broadcast, OnPrevoteQuorumNil, sent, ValuesOrNil
  <2>9. CASE OnTimeoutPrevote(p)
    BY <2>9, <2>v, FreshKeepsFrozen, MsgPrecommit, PrecommitFresh DEFS Broadcast, OnTimeoutPrevote, sent, ValuesOrNil
  <2>10. CASE ScheduleTimeoutPrecommit(p)
    BY <2>10 DEF ScheduleTimeoutPrecommit, SentTimeFrozenPred
  <2>11. CASE OnPrecommitQuorumValue(p)
    BY <2>11 DEF OnPrecommitQuorumValue, SentTimeFrozenPred
  <2>12. CASE OnTimeoutPrecommit(p)
    BY <2>12 DEF OnTimeoutPrecommit, SentTimeFrozenPred
  <2>13. CASE \E r \in Rounds : SkipRound(p, r)
    BY <2>13 DEF SkipRound, SentTimeFrozenPred
  <2>14. CASE Deliver(p)
    BY <2>14 DEF Deliver, SentTimeFrozenPred
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
       <2>11, <2>12, <2>13, <2>14 DEF HonestNext, HonestStep
<1>2. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>2, FreshKeepsFrozen DEF FaultyStep
<1>3. CASE Tick
  BY <1>3 DEF Tick, SentTimeFrozenPred
<1>4. CASE UNCHANGED vars
  BY <1>4
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM SentTimeFrozenInv == ASSUME Spec PROVE [][SentTimeFrozenPred]_vars
BY InvProof, PTL, SentInvInv, SentTimeFrozenStepL DEFS Inv, Spec

\* The WF1 region: m is sent, not yet received by c, its timestamp is <= t0, and
\* the clock sits in the post-GST window [GST, t0+Delta). (t0 >= GST is the rigid
\* start condition, carried as a constant.)
DelivPending(c, m, t0) ==
  /\ m \in sent
  /\ m \notin rcvd[c]
  /\ sentTime[m] <= t0
  /\ t0 >= GST
  /\ now >= GST
  /\ now < t0 + Delta
DelivDone(c, m, t0) ==
  /\ m \in rcvd[c]
  /\ now < t0 + Delta

\* Deliver(c) is enabled while m is pending: m is available (sent, unreceived,
\* and now >= sentTime[m] by SentTimeLeNow), so Available(c) # {}, and delivering
\* it changes rcvd[c]. ExpandENABLED with that change fact (cf. EnabledDecide).
LEMMA EnabledDeliver ==
  ASSUME TypeOK, SentTimeLeNow, NEW c \in Honest, NEW m \in Message,
         m \in sent, m \notin rcvd[c]
  PROVE  ENABLED <<Deliver(c)>>_vars
BY ExpandENABLED DEFS Available, Deliver, sent, SentTimeLeNow, TypeOK, vars

\* Action leg: when Deliver(c) fires from the pending region, m is delivered and
\* the clock is unchanged, so DelivDone holds next.
LEMMA DeliverDelivers ==
  ASSUME TypeOK, SentTimeLeNow, NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat,
         DelivPending(c, m, t0), Deliver(c)
  PROVE  DelivDone(c, m, t0)'
BY DEFS Available, DelivDone, Deliver, DelivPending, sent, SentTimeLeNow, TypeOK

\* The stability leg: every step from the pending region either keeps it
\* pending or reaches DelivDone. The clock bound now' < t0+Delta is preserved,
\* because the delivery-deadline gate of Tick forbids reaching
\* DeliveryDeadline(m) <= t0+Delta while <c,m> is pending. A step that is not
\* a Tick leaves `now` fixed, by NowStaysUnlessTick. Timestamps stay at or
\* below t0, by SentTimeFrozenPred, and `sent` only grows.
LEMMA DeliverStability ==
  ASSUME TypeOK, SentTimeLeNow, NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat,
         DelivPending(c, m, t0), [Next]_vars, SentTimeFrozenPred
  PROVE  DelivPending(c, m, t0)' \/ DelivDone(c, m, t0)'
<1> USE DEF DelivPending, DelivDone
<1>a. m \in sent /\ m \notin rcvd[c] /\ sentTime[m] <= t0 /\ t0 >= GST
       /\ now >= GST /\ now < t0 + Delta
  OBVIOUS
<1>b. m \in sent'
  BY <1>a, SentMonotoneStep
<1>c. sentTime'[m] <= t0
  BY <1>a DEF sent, SentTimeFrozenPred
<1>e. now \in Nat /\ now' \in Nat /\ now <= now' /\ GST \in Nat /\ Delta \in Nat
       /\ sentTime[m] \in Nat
  BY <1>a, NowShape, NowMonotoneStep, GSTType, DeltaType DEF TypeOK, sent, OFF
<1>f. now' < t0 + Delta
  <2>1. CASE Tick
    <3>1. <<c, m>> \in PendingDeliveries
      BY <1>a DEF PendingDeliveries
    <3>2. now + 1 < DeliveryDeadline(m)
      BY <2>1, <3>1 DEF Tick
    <3>3. DeliveryDeadline(m) \in Nat /\ DeliveryDeadline(m) <= t0 + Delta
      BY <1>a, <1>e DEF DeliveryDeadline
    <3>4. now' = now + 1
      BY <2>1 DEF Tick
    <3>. QED
      BY <3>2, <3>3, <3>4, <1>e
  <2>2. CASE ~Tick
    BY <1>a, <2>2, NowStaysUnlessTick
  <2>. QED
    BY <2>1, <2>2
<1>g. now' >= GST
  BY <1>e, <1>a
<1>1. CASE m \in rcvd'[c]
  BY <1>1, <1>f
<1>2. CASE m \notin rcvd'[c]
  BY <1>b, <1>c, <1>a, <1>f, <1>g, <1>2
<1>. QED
  BY <1>1, <1>2

\* The bundle of invariants, and the "next" action of the WF1, as MODULE-LEVEL
\* operators, and not as local DEFINEs. An instantiation of RuleWF1 with a
\* primed local DEFINE action trips the anonymizer. To prime a real operator,
\* as in DInv', is fine. DStep bundles the invariant before the step and after
\* it, together with the freeze against a rebroadcast. The stability leg of
\* the WF1 therefore has TypeOK and SentTimeLeNow available on both sides of
\* the step.
DInv  == TypeOK /\ SentTimeLeNow
DStep == DInv /\ Next /\ DInv' /\ SentTimeFrozenPred

\* Boxed start condition: in any state, if the (always-true) invariant holds and
\* the precondition holds, then the pending region or the goal holds. A clean
\* top-level lemma (no Spec in context) so the OBVIOUS-then-PTL boxing of this
\* concrete state implication goes through (boxing it inline under Spec fails).
LEMMA DelivStartBox ==
  ASSUME NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat
  PROVE  []( (TypeOK /\ SentTimeLeNow /\ now >= GST /\ m \in sent /\ now = t0)
               => (DelivPending(c, m, t0) \/ DelivDone(c, m, t0)) )
<1>1. (TypeOK /\ SentTimeLeNow /\ now >= GST /\ m \in sent /\ now = t0)
        => (DelivPending(c, m, t0) \/ DelivDone(c, m, t0))
  BY DeltaType DEFS DelivDone, DelivPending, sent, SentTimeLeNow
<1>. QED
  BY <1>1, PTL

\* The three legs of the WF1, BOXED in clean top-level lemmas. The PTL rule
\* for WF1 needs them as [] facts. To box them inline under Spec fails,
\* because the Init conjunct pollutes the PTL abstraction. Each one boxes a
\* validity on a state, or on an action, that follows from the discharged legs
\* EnabledDeliver, DeliverDelivers and DeliverStability.
LEMMA BoxActLeg ==
  ASSUME NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat
  PROVE  [](  DInv /\ DelivPending(c, m, t0) /\ <<Deliver(c)>>_vars => DelivDone(c, m, t0)'  )
BY DeliverDelivers, PTL DEF DInv

LEMMA BoxEnabledLeg ==
  ASSUME NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat
  PROVE  [](DInv /\ DelivPending(c, m, t0) => ENABLED <<Deliver(c)>>_vars)
BY EnabledDeliver, PTL DEFS DelivPending, DInv

LEMMA BoxStabLeg ==
  ASSUME NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat
  PROVE  [](  DInv /\ DelivPending(c, m, t0) /\ [DStep]_vars
                => ( (DInv /\ DelivPending(c, m, t0))' \/ DelivDone(c, m, t0)' )  )
<1>1. DInv /\ DelivPending(c, m, t0) /\ [DStep]_vars
        => ( (DInv /\ DelivPending(c, m, t0))' \/ DelivDone(c, m, t0)' )
  BY DeliverStability DEFS DelivDone, DelivPending, DInv, DStep, sent, SentTimeLeNow, TypeOK, vars
<1>. QED
  BY <1>1, PTL

\* (TEMPORAL) The reusable bounded-delivery leads-to, which is Route B. After
\* GST, a message that is already in `sent` and pending for the correct
\* process c is received before Delta. Deliver(c) is WF-fair, and it absorbs
\* ALL the messages that are currently available. Tick cannot reach the
\* DeliveryDeadline of the message, which is at most t0 + Delta after GST,
\* because sentTime[m] <= t0. c therefore receives m before t0 + Delta. The
\* bound on now, with the rigid start t0, is the bounded-response form that
\* the later stages use. The proof is a WF1 on Deliver(c), with the legs
\* EnabledDeliver, DeliverDelivers and DeliverStability. It is threaded
\* through the invariant bundle GI = TypeOK /\ SentTimeLeNow, and through
\* SentTimeFrozenPred.
THEOREM DeliverWithinDelta ==
  ASSUME NEW c \in Honest, NEW m \in Message, NEW t0 \in Nat
  PROVE  Spec =>
           ( (now >= GST /\ m \in sent /\ now = t0)
               ~> (m \in rcvd[c] /\ now < t0 + Delta) )
<1> SUFFICES ASSUME Spec
             PROVE  (now >= GST /\ m \in sent /\ now = t0)
                      ~> (m \in rcvd[c] /\ now < t0 + Delta)
  OBVIOUS
<1> DEFINE Pp  == DInv /\ DelivPending(c, m, t0)
<1> DEFINE Qq  == DelivDone(c, m, t0)
<1> DEFINE Pre == now >= GST /\ m \in sent /\ now = t0
\* Rephrase the goal with the DEFINEs so the final PTL glue's atoms match.
<1>goal. SUFFICES Pre ~> Qq
  BY PTL DEF Pre, Qq, DelivDone
<1>g. []DInv
  BY InvProof, SentTimeLeNowInv, PTL DEF DInv, Inv
\* WF1 on Deliver(c): the pending region leads to delivery. The three legs are
\* boxed (BoxActLeg / BoxEnabledLeg / BoxStabLeg); WF and the boxed next-action
\* [][DStep]_vars are temporal; PTL applies the WF1 rule.
<1>1. [](Pp /\ <<Deliver(c)>>_vars => Qq')
  BY BoxActLeg DEF Pp, Qq
<1>2. [](Pp => ENABLED <<Deliver(c)>>_vars)
  BY BoxEnabledLeg DEF Pp
<1>3. WF_vars(Deliver(c))
  BY DEF Spec, Fairness
<1>4. [](Pp /\ [DStep]_vars => (Pp' \/ Qq'))
  BY BoxStabLeg DEF Pp, Qq
<1>5. [][DStep]_vars
  BY <1>g, PTL, SentTimeFrozenInv DEFS DStep, Spec
<1>6. Pp ~> Qq
  BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL
\* Glue the precondition: under []DInv, Pre implies the pending region or the goal.
<1>7. [](Pre => (Pp \/ Qq))
  BY <1>g, DelivStartBox, PTL DEF Pp, DInv, Qq, Pre
<1>. QED
  BY <1>6, <1>7, PTL


\* Honest is finite (a subset of the finite validator set).
LEMMA HonestFinite == IsFiniteSet(Honest)
BY HonestSubValidators, ValidatorsFinite, FS_Subset

(***************************************************************************)
(* Phase 1: clock reachability past GST (burst-termination core).          *)
(*                                                                         *)
(* The Layer-1 reachability half of the selected round of Lemma 7, which   *)
(* is step <1>2 of TerminationThm. It earns <>[](now > GST) from the gated *)
(* concrete Tick, with a well-founded measure on the burst. This block is  *)
(* self-contained in the termination modules.                              *)
(***************************************************************************)

\* ---- Task 1.1: finiteness of the pending-delivery frontier ---------------
\* Message is infinite, because Rounds = Nat. The finiteness of sent is
\* therefore NOT a consequence of TypeOK, and it is a genuine inductive
\* invariant. sent starts empty, because Init sets every entry of sentTime to
\* OFF. Each step overwrites at most one entry with `now`, by SentTimeStep, so
\* sent grows by at most one element at each step.
\*
\* The step: one step keeps sent finite. Either sentTime is unchanged, so
\* sent' = sent, or exactly one entry is overwritten, which gives sent'
\* \subseteq sent \cup {mm}. Both cases preserve finiteness. The inclusion
\* holds even when mm is outside Message, because an EXCEPT at an index
\* outside the domain does nothing. No obligation mm \in Message is therefore
\* incurred. The predicate on the state is named, so that the inductive PTL
\* lift sees an atomic primed invariant. PTL treats IsFiniteSet(sent)' and
\* IsFiniteSet(sent') as UNRELATED atoms. To fold them into SentFinite gives
\* the matching atoms SentFinite and SentFinite' for the box induction. This
\* is the DecidedBackedByProposal idiom.
SentFinite == IsFiniteSet(sent)

\* LEMMA SentFiniteStepL ==
\*   ASSUME TypeOK, SentFinite, [Next]_vars
\*   PROVE  SentFinite'
\* <1> SUFFICES IsFiniteSet(sent')
\*   BY DEF SentFinite
\* <1>h. IsFiniteSet(sent)
\*   BY DEF SentFinite
\* <1>1. CASE sentTime' = sentTime
\*   BY <1>1, <1>h DEF sent
\* <1>2. CASE \E mm : sentTime' = [sentTime EXCEPT ![mm] = now]
\*   <2>1. PICK mm : sentTime' = [sentTime EXCEPT ![mm] = now]
\*     BY <1>2
\*   <2>2. sent' \subseteq sent \cup {mm}
\*     BY <2>1 DEFS sent, TypeOK
\*   <2>3. IsFiniteSet(sent \cup {mm})
\*     BY <1>h, FS_Singleton, FS_Union
\*   <2>. QED
\*     BY <2>2, <2>3, FS_Subset
\* <1>. QED
\*   BY <1>1, <1>2, SentTimeStep

\* sent is finite at every reachable state.
\* THEOREM SentFiniteInv == Spec => []SentFinite
\* <1> SUFFICES ASSUME Spec PROVE []SentFinite
\*   OBVIOUS
\* <1>1. SentFinite
\*   BY FS_EmptySet DEFS Init, OFF, sent, SentFinite, Spec
\* <1>2. [](TypeOK /\ [Next]_vars)
\*   BY InvProof, PTL DEF Spec, Inv
\* <1>3. [](SentFinite => SentFinite')
\*   BY <1>2, SentFiniteStepL, PTL
\* <1>. QED
\*   BY <1>1, <1>3, PTL

\* PendingDeliveries is finite, because it is a subset of the finite product
\* Honest \X sent. The plan states this from TypeOK alone. It also needs the
\* finiteness of sent, which SentFiniteInv supplies under Spec.
LEMMA PendingDeliveriesFinite ==
  ASSUME TypeOK, SentFinite
  PROVE  IsFiniteSet(PendingDeliveries) /\ Cardinality(PendingDeliveries) \in Nat
BY FS_CardinalityType, FS_Product, FS_Subset, HonestFinite DEFS PendingDeliveries, SentFinite

\* Boxed corollary consumed by the burst measure (Task 1.2 onward).
\* THEOREM PendingDeliveriesFiniteInv == Spec => [](IsFiniteSet(PendingDeliveries))
\* BY InvProof, PendingDeliveriesFinite, PTL, SentFiniteInv DEFS Inv, Spec

\* ---- Task 1.3: Tick becomes enabled at the bottom of a burst
\* -------------- Honest quiescence: no honest validator has an enabled
\* computation step. This is the SOUND quiescence milestone (Tick's
\* maximal-progress gate is ~(\E p \in Honest : CanCompute(p)); it does NOT
\* require a drained network). A faulty validator need never stop sending, so
\* PendingDeliveries need never drain, whereas the HONEST computation burst
\* IS finite (the burst measure).
HonestQuiescent == ~ \E p \in Honest : CanCompute(p)

\* At the bottom of a burst before GST, Tick is enabled. The burst is
\* honest-quiescent, and the clock is still useful. Maximal progress holds, by
\* HonestQuiescent, and the delivery-deadline guard costs nothing before GST,
\* by PreGSTDeadlineOk. PendingDeliveries = {} is not necessary, because the
\* frontier that the faulty validators feed can be non-empty.
LEMMA BurstBottomEnablesTick ==
  ASSUME TypeOK, now < GST, HonestQuiescent, TickUseful
  PROVE  ENABLED <<Tick>>_vars
BY PreGSTDeadlineOk, TickEnabledFromGuards DEF HonestQuiescent

\* Timestamp-aware strict pre-GST variant.
LEMMA BurstBottomEnablesTickThroughGST ==
  ASSUME TypeOK, SentTimeLeNow, now < GST, HonestQuiescent, TickUseful
  PROVE  ENABLED <<Tick>>_vars
BY DeadlineOkThroughGST, TickEnabledFromGuards DEF HonestQuiescent

\* ===========================================================================
\* SELF-VOTE EVIDENCE. An honest validator in step "prevote", or in step
\* "precommit", has its OWN vote of that kind in rcvd, at its current round.
\* Broadcast self-delivers instantly, so it adds the message to rcvd[p]. The
\* round is frozen while the validator is in the step, and rcvd is monotone.
\* This closes the "residual" case that LiveTimerWhenQuiescent below would
\* otherwise meet. Take a validator in prevote, or in precommit, whose OWN
\* timer for that step is OFF. It still has its self-vote in rcvd, so it
\* CanCompute. For prevote that is through ScheduleTimeoutPrevote,
\* OnPrevoteQuorumNil or OnTimeoutPrevote. For precommit it is through
\* ScheduleTimeoutPrecommit. That contradicts quiescence. The frontier is
\* therefore unreachable, and this is not a global fact about the distribution
\* of the votes.
\* ===========================================================================
SelfVoteEvidenceOp ==
  /\ \A q \in Honest : step[q] = "prevote" =>
       \E m \in rcvd[q] : m.type = "Prevote" /\ m.sender = q /\ m.round = round[q]
  /\ \A q \in Honest : step[q] = "precommit" =>
       \E m \in rcvd[q] : m.type = "Precommit" /\ m.sender = q /\ m.round = round[q]

LEMMA SelfVoteEvidenceStepL ==
  ASSUME TypeOK, [Next]_vars, SelfVoteEvidenceOp
  PROVE  SelfVoteEvidenceOp'
\* ---- prevote conjunct
\* ------------------------------------------------------
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Precommit, Prevote, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SelfVoteEvidenceOp, SkipRound, Tick, TypeOK, vars

THEOREM SelfVoteEvidenceInv == Spec => []SelfVoteEvidenceOp
<1> SUFFICES ASSUME Spec PROVE []SelfVoteEvidenceOp
  OBVIOUS
<1>1. SelfVoteEvidenceOp
  BY DEF Spec, Init, SelfVoteEvidenceOp
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](SelfVoteEvidenceOp => SelfVoteEvidenceOp')
  BY <1>2, SelfVoteEvidenceStepL, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* ---- Round bound: an honest round never exceeds the clock, round[c] <= now
\* This is what bounds a burst at a frozen clock. With the rounds bounded by
\* the frozen clock, only finitely many advances of a round happen before Tick
\* must fire. RoundBelowNow and the lower bound on the precommit timer are
\* JOINTLY inductive.
\* - The jump of SkipRound to r is bounded. The weak quorum of f+1 holds an
\*   honest sender whose message of round r gives r <= round[sender] <= now.
\*   That uses SentInv and RoundBelowNow.
\* - The increment of OnTimeoutPrecommit by one is bounded, because the
\*   precommit timer that fired was armed at now + TimeoutPrecommit(round) >=
\*   round + 1, by PrecommitTimerLB. That arming in turn needs round <= now,
\*   by RoundBelowNow.
RoundBelowNow    == \A c \in Honest : round[c] <= now
PrecommitTimerLB == \A c \in Honest :
                      timer[c]["precommit"] # OFF => round[c] + 1 <= timer[c]["precommit"]
RoundClockInv    == RoundBelowNow /\ PrecommitTimerLB

LEMMA RoundClockInvStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars, RoundClockInv
  PROVE  RoundClockInv'
<1> USE DEF RoundClockInv
<1>now. now \in Nat /\ now' \in Nat /\ now <= now'
  BY NowShape, NowMonotoneStep DEF TypeOK
\* ---- Conjunct 1: RoundBelowNow' ------------------------------------------
<1>rn. RoundBelowNow'
  <2> SUFFICES ASSUME NEW c \in Honest PROVE round'[c] <= now'
    BY DEF RoundBelowNow
  <2>rc. round[c] \in Nat /\ round[c] <= now
    BY DEF TypeOK, Rounds, RoundBelowNow
  <2>d. \/ round' = round
        \/ \E p \in Honest : OnTimeoutPrecommit(p)
        \/ \E p \in Honest : \E r \in Rounds : SkipRound(p, r)
    BY DEF Next, HonestNext, HonestStep, Propose, OnTimeoutPropose, OnProposalNoPOL,
       OnProposalWithPOL, ScheduleTimeoutPrevote, OnPrevoteQuorumValueFirstTime,
       OnPrevoteQuorumValueLateUpdate, OnPrevoteQuorumNil, OnTimeoutPrevote,
       ScheduleTimeoutPrecommit, OnPrecommitQuorumValue, Deliver, FaultyStep, Tick, vars
  <2>1. CASE round'[c] = round[c]
    BY <2>1, <2>rc, <1>now
  <2>2. CASE round'[c] # round[c]
    <3>a. OnTimeoutPrecommit(c) \/ (\E r \in Rounds : SkipRound(c, r))
      BY <2>2, <2>d DEFS OnTimeoutPrecommit, SkipRound, TypeOK
    <3>b. CASE OnTimeoutPrecommit(c)
      BY <1>now, <2>rc, <3>b DEFS OnTimeoutPrecommit, PrecommitTimerLB, TimerType, TypeOK
    <3>c. CASE \E r \in Rounds : SkipRound(c, r)
      BY <1>now, <3>c, WeakQuorumHasHonest
      DEFS HonestSentOK, RcvdSubsetSent, RoundBelowNow, Rounds, RSendersOfAnyMessageAt, RSendersOfTypeAtRound, SentInv, SkipRound, TypeOK
    <3>. QED
      BY <3>a, <3>b, <3>c
  <2>. QED
    BY <2>1, <2>2
\* ---- Conjunct 2: PrecommitTimerLB' ---------------------------------------
<1>tb. PrecommitTimerLB'
  BY <1>now, T0PrecommitType, TDeltaType
  DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, PrecommitTimerLB, Propose, ResetTimersFor, RoundBelowNow, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TimeoutPrecommit, TimerType, TypeOK, vars
<1>. QED
  BY <1>rn, <1>tb DEF RoundClockInv

\* Round bound + precommit-timer bound hold at every reachable state.
THEOREM RoundClockInvThm == Spec => []RoundClockInv
<1> SUFFICES ASSUME Spec PROVE []RoundClockInv
  OBVIOUS
<1>1. RoundClockInv
  BY DEFS Init, OFF, PrecommitTimerLB, RoundBelowNow, RoundClockInv, Spec, TimerType
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ [Next]_vars)
  BY InvProof, SentInvInv, PTL DEF Spec, Inv
<1>3. [](RoundClockInv => RoundClockInv')
  BY <1>2, RoundClockInvStepL, PTL
<1>. QED
  BY <1>1, <1>3, PTL

\* The reusable round bound (consumed by the burst measure and Phase 3).
LEMMA RoundClockImpliesBelow == RoundClockInv => RoundBelowNow
BY DEF RoundClockInv

THEOREM RoundBelowNowInv == Spec => []RoundBelowNow
BY PTL, RoundClockImpliesBelow, RoundClockInvThm


-----------------------------------------------------------------------------
(***************************************************************************)
(* Task 1.2: the well-founded burst measure ComputeWork.                   *)
(*                                                                         *)
(* A burst of honest computation at a frozen clock is finite. Each honest  *)
(* compute step strictly decreases a lexicographic triple << RoundGap,     *)
(* StepWork, ProposeOwed + OffLiveTimers + ValidStale >>, while Deliver    *)
(* and FaultyStep leave every component fixed. The measure is              *)
(* faulty-INDEPENDENT, because it never mentions the network frontier that *)
(* a faulty validator can grow without bound. The triple is collapsed into *)
(* one bounded Nat, BurstScalar, with a Horner radix of BurstBound + 1.    *)
(* The WF1 chain for burst termination, which is Task 1.4, therefore       *)
(* inducts with one NaturalsInduction over a single distance metric.       *)
(*                                                                         *)
(* The shape is << RoundGap, StepWork, ProposeOwed + OffLiveTimers >>. The *)
(* concrete TendermintPartialSync specification forces two changes.           *)
(* (a) roundCeiling is not a history variable here. It is the concrete     *)
(* RoundCeiling == (now+1)*(|Honest|+1). It is frozen exactly when now is  *)
(* frozen, because no honest step, no faulty step and no deliver step      *)
(* touches now. RoundBelowNowInv gives round[c] <= now < RoundCeiling, so  *)
(* a raise of a round strictly shrinks RoundGap.                           *)
(* (b) A ValidStale component charges OnPrevoteQuorumValueLateUpdate,      *)
(* which is an action that the abstract clock specification does not have. *)
(* A DECIDED validator contributes 0 to StepWork, and it can still hold    *)
(* valid[p].round < round[p] with a value quorum. That keeps CanCompute    *)
(* true, so BurstScalar = 0 would not imply quiescence without this term.  *)
(* ValidStale drops only on the actions that refresh valid, and RoundGap   *)
(* dominates it on a raise of a round. It therefore does not disturb the   *)
(* lexicographic order.                                                    *)
(*                                                                         *)
(* BurstBound = 4*|Honest|, and not the 3*|Honest| of the clock. The       *)
(* bottom component reaches ProposeOwed (<=|H|) + OffLiveTimers (<=2|H|) + *)
(* ValidStale (<=|H|) = 4|H|. The Horner collapse preserves the            *)
(* lexicographic order only while both lower components are <= BurstBound. *)
(***************************************************************************)

RoundCeiling == (now + 1) * (Cardinality(Honest) + 1)

StepBudget(p) ==
  CASE step[p] = "propose"   -> 3
    [] step[p] = "prevote"   -> 2
    [] step[p] = "precommit" -> 1
    [] OTHER                 -> 0

RoundGap  == Cardinality({ pj \in Honest \X (1 .. RoundCeiling) : pj[2] + round[pj[1]] <= RoundCeiling })
StepWork  == Cardinality({ pj \in Honest \X (1 .. 3) : pj[2] <= StepBudget(pj[1]) })
\* The negation of the \E is the Propose guard, which is disjunct 1 of
\* CanCompute. It is written inline, and not with a named operator, so that
\* ProposeOwed' never primes an application of an operator. That would hit the
\* crash of the anon pass of tlapm, which ProposeOwedDropsPropose works
\* around.
ProposeOwed ==
  Cardinality({ p \in Honest :
    step[p] = "propose"
    /\ ~(\E m \in sent : m.type = "Proposal" /\ m.round = round[p] /\ m.sender = p) })
OffLiveTimers ==
    Cardinality({ p \in Honest : step[p] = "prevote" /\ timer[p]["prevote"]   = OFF })
  + Cardinality({ p \in Honest : step[p] # "decided" /\ timer[p]["precommit"] = OFF })
ValidStale == Cardinality({ p \in Honest : valid[p].round < round[p] })

BurstBottom == ProposeOwed + OffLiveTimers + ValidStale
BurstBound  == 4 * Cardinality(Honest)
BurstScalar == (BurstBound + 1) * ((BurstBound + 1) * RoundGap + StepWork) + BurstBottom
ComputeWork == BurstScalar

\* ---- Arithmetic helpers (pure Nat, no dependency on the specification) ---
LEMMA MultMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b
  PROVE  c * a <= c * b
BY SMT

LEMMA MultDistribOne ==
  ASSUME NEW a \in Nat, NEW c \in Nat
  PROVE  c * (a + 1) = c * a + c
BY SMT

\* x < y (Nat) and t <= B  =>  (B+1)*x + t < (B+1)*y.
LEMMA MulStep ==
  ASSUME NEW B \in Nat, NEW x \in Nat, NEW y \in Nat, NEW t \in Nat,
         x < y, t <= B
  PROVE  (B+1) * x + t < (B+1) * y
<1> DEFINE D == B + 1
<1>d. D \in Nat /\ x + 1 <= y
  BY SMT
<1>1. D * (x + 1) <= D * y
  BY <1>d, MultMono
<1>2. D * (x + 1) = D * x + D
  BY <1>d, MultDistribOne
<1>3. D * x + D <= D * y
  BY <1>1, <1>2, SMT
<1> QED
  BY <1>3, SMT

\* Generic lex-to-scalar collapse: a 3-level lex decrease with the lower two
\* components bounded by B becomes a strict decrease of (B+1)*((B+1)*r + s) + w.
LEMMA Collapse3 ==
  ASSUME NEW B \in Nat,
         NEW r1 \in Nat, NEW s1 \in Nat, NEW w1 \in Nat,
         NEW r2 \in Nat, NEW s2 \in Nat, NEW w2 \in Nat,
         s1 <= B, w1 <= B,
         \/ r1 < r2
         \/ (r1 = r2 /\ s1 < s2)
         \/ (r1 = r2 /\ s1 = s2 /\ w1 < w2)
  PROVE  (B+1)*((B+1)*r1 + s1) + w1 < (B+1)*((B+1)*r2 + s2) + w2
<1> DEFINE D == B + 1
<1>0a. (D * r1 + s1) \in Nat /\ (D * r2 + s2) \in Nat
  OBVIOUS
<1>0. (D*r1 + s1 < D*r2 + s2) \/ (D*r1 + s1 = D*r2 + s2 /\ w1 < w2)
  BY MulStep, SMT
<1>1. CASE D*r1 + s1 < D*r2 + s2
  BY <1>1, <1>0a, MulStep, SMT
<1>2. CASE D*r1 + s1 = D*r2 + s2 /\ w1 < w2
  BY <1>2, SMT
<1> QED BY <1>0, <1>1, <1>2

\* ---- Ported finiteness / cardinality helpers -----------------------------
LEMMA HonestSubsetFinite ==
  ASSUME NEW S, S \subseteq Honest
  PROVE  IsFiniteSet(S) /\ Cardinality(S) \in Nat
BY HonestFinite, FS_Subset, FS_CardinalityType

\* A strict finite subset has strictly smaller cardinality (the reusable crux).
LEMMA StrictSubsetCard ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S1), S2 \subseteq S1,
         NEW x, x \in S1, x \notin S2
  PROVE  Cardinality(S2) < Cardinality(S1)
BY FS_CardinalityType, FS_RemoveElement, FS_Subset, Isa, SMT

\* Cardinality of any subset of Honest x (1..3) is at most 3|Honest|.
LEMMA CardHonestProd3 ==
  ASSUME NEW S, S \subseteq (Honest \X (1 .. 3))
  PROVE  Cardinality(S) <= 3 * Cardinality(Honest)
<1>hf. IsFiniteSet(Honest)
  BY HonestFinite
<1>1. IsFiniteSet(1 .. 3) /\ Cardinality(1 .. 3) = 3
  BY FS_Interval
<1>2. IsFiniteSet(Honest \X (1 .. 3))
  BY <1>hf, FS_Product, <1>1
<1>3. Cardinality(Honest \X (1 .. 3)) = Cardinality(Honest) * Cardinality(1 .. 3)
  BY <1>hf, FS_Product, <1>1
<1>4. Cardinality(Honest \X (1 .. 3)) = Cardinality(Honest) * 3
  BY <1>1, <1>3
<1>5. Cardinality(S) <= Cardinality(Honest \X (1 .. 3))
  BY <1>2, FS_Subset
<1>6. Cardinality(Honest) \in Nat
  BY <1>hf, FS_CardinalityType
<1> QED BY <1>4, <1>5, <1>6, SMT

\* ---- Nat typing of each measure component --------------------------------
LEMMA RoundGapNat ==
  ASSUME TypeOK PROVE RoundGap \in Nat
<1>hf. IsFiniteSet(Honest) /\ Cardinality(Honest) \in Nat
  BY HonestFinite, FS_CardinalityType
<1>rc. RoundCeiling \in Nat
  BY <1>hf DEF RoundCeiling, TypeOK
<1>1. IsFiniteSet(Honest \X (1 .. RoundCeiling))
  BY <1>hf, <1>rc, FS_Interval, FS_Product
<1>2. {pj \in Honest \X (1 .. RoundCeiling) : pj[2] + round[pj[1]] <= RoundCeiling}
        \subseteq Honest \X (1 .. RoundCeiling)
  OBVIOUS
<1> QED BY <1>1, <1>2, FS_Subset, FS_CardinalityType DEF RoundGap

LEMMA StepWorkNat ==
  ASSUME TypeOK PROVE StepWork \in Nat
BY FS_CardinalityType, FS_Interval, FS_Product, FS_Subset, HonestFinite DEF StepWork

LEMMA OwedTimersNat ==
  ASSUME TypeOK
  PROVE  ProposeOwed \in Nat /\ OffLiveTimers \in Nat /\ ValidStale \in Nat
BY HonestSubsetFinite DEFS OffLiveTimers, ProposeOwed, ValidStale

\* ---- Higher-component invariance: an action that fixes a component's state
\* ---- inputs leaves that component fixed (used by the lexicographic assembly).
LEMMA RoundGapUnchanged ==
  ASSUME round' = round, now' = now
  PROVE  RoundGap' = RoundGap
BY DEFS RoundCeiling, RoundGap

LEMMA StepWorkUnchanged ==
  ASSUME step' = step
  PROVE  StepWork' = StepWork
BY DEF StepWork, StepBudget

LEMMA OffLiveTimersUnchanged ==
  ASSUME step' = step, timer' = timer
  PROVE  OffLiveTimers' = OffLiveTimers
BY DEF OffLiveTimers

LEMMA ValidStaleUnchanged ==
  ASSUME valid' = valid, round' = round
  PROVE  ValidStale' = ValidStale
BY DEF ValidStale

\* ProposeOwed reads only step, round and sent. If all three are fixed, it is
\* fixed.
LEMMA ProposeOwedUnchanged ==
  ASSUME step' = step, round' = round, sentTime' = sentTime
  PROVE  ProposeOwed' = ProposeOwed
BY DEFS ProposeOwed, sent

\* ---- RoundGap strictly drops on a round-raising honest action -----------
\* RoundCeiling is frozen because now is frozen (now' = now), and round[p] <
\* RoundCeiling comes from the caller (RoundBelowNowInv). The raised process's
\* witness pair << p, RoundCeiling - round[p] >> leaves the gap set, so its
\* cardinality drops.
LEMMA RoundGapDecreaseRaise ==
  ASSUME TypeOK, NEW p \in Honest, round[p] < RoundCeiling,
         round' \in [Honest -> Nat],
         round'[p] > round[p],
         \A q \in Honest : q # p => round'[q] = round[q],
         now' = now
  PROVE  RoundGap' < RoundGap
<1> DEFINE S1 == { pj \in Honest \X (1 .. RoundCeiling) : pj[2] + round[pj[1]]  <= RoundCeiling }
<1> DEFINE S2 == { pj \in Honest \X (1 .. RoundCeiling) : pj[2] + round'[pj[1]] <= RoundCeiling }
<1> DEFINE x  == << p, RoundCeiling - round[p] >>
<1>hf. Cardinality(Honest) \in Nat
  BY HonestFinite, FS_CardinalityType
<1>rcn. RoundCeiling \in Nat
  BY <1>hf DEF RoundCeiling, TypeOK
<1>rcc. RoundCeiling' = RoundCeiling
  BY DEF RoundCeiling
<1>0. p \in Honest /\ round[p] \in Nat /\ RoundCeiling \in Nat /\ round[p] < RoundCeiling
  BY <1>rcn DEF TypeOK, Rounds
<1>typ. round \in [Honest -> Nat] /\ round'[p] \in Nat
  BY DEF TypeOK, Rounds
<1>gt. round'[p] > round[p]
  OBVIOUS
<1>rc1. RoundGap = Cardinality(S1)
  BY DEF RoundGap
<1>rc2. RoundGap' = Cardinality(S2)
  BY <1>rcc DEF RoundGap
<1>rc. RoundGap = Cardinality(S1) /\ RoundGap' = Cardinality(S2)
  BY <1>rc1, <1>rc2
<1>xc. x[1] = p /\ x[2] = RoundCeiling - round[p]
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
<1> QED BY <1>card, <1>rc

\* ---- StepWork strictly drops when p moves to a lower-budget step ---------
LEMMA StepWorkDecreaseStep ==
  ASSUME TypeOK, NEW p \in Honest,
         step' \in [Honest -> Step],
         \A q \in Honest : q # p => step'[q] = step[q],
         StepBudget(p)' < StepBudget(p)
  PROVE  StepWork' < StepWork
<1> DEFINE S1 == { pj \in Honest \X (1 .. 3) : pj[2] <= StepBudget(pj[1])  }
<1> DEFINE S2 == { pj \in Honest \X (1 .. 3) : pj[2] <= StepBudget(pj[1])' }
<1> DEFINE x  == << p, StepBudget(p) >>
<1>sp. step \in [Honest -> Step]
  BY DEF TypeOK
<1>0. StepBudget(p) \in 0 .. 3 /\ StepBudget(p)' \in 0 .. 3 /\ StepBudget(p)' < StepBudget(p)
  BY <1>sp DEF StepBudget, Step
<1>b1. StepBudget(p) \in 1 .. 3
  BY ONLY <1>0, SMT
<1>rc. StepWork = Cardinality(S1) /\ StepWork' = Cardinality(S2)
  BY DEF StepWork
<1>ptr. \A q \in Honest : q # p => StepBudget(q)' = StepBudget(q)
  BY DEF StepBudget
<1>xc. x[1] = p /\ x[2] = StepBudget(p)
  OBVIOUS
<1>fin. IsFiniteSet(S1)
  BY FS_Interval, FS_Product, FS_Subset, HonestFinite
<1>sub. S2 \subseteq S1
  BY <1>0, <1>ptr, <1>sp, SMT DEFS Step, StepBudget
<1>xin. x \in S1
  BY <1>b1, <1>xc, SMT
<1>xout. x \notin S2
  <2>1. ~ (x[2] <= StepBudget(x[1])')
    BY ONLY <1>0, <1>xc, SMT
  <2> QED BY <2>1
<1> QED BY <1>rc, <1>fin, <1>sub, <1>xin, <1>xout, StrictSubsetCard

\* ---- Propose drops ProposeOwed by at least one --------------------------
\* p (the proposer) broadcasts its round proposal m, so the inline "has proposed"
\* predicate flips to true and p leaves the ProposeOwed set. The primed predicate
\* is written out as PropP (priming the operator application crashes tlapm's anon
\* pass).
LEMMA ProposeOwedDropsPropose ==
  ASSUME TypeOK, NEW p \in Honest, Propose(p)
  PROVE  ProposeOwed \in Nat /\ ProposeOwed' \in Nat /\ ProposeOwed' + 1 <= ProposeOwed
<1> DEFINE Prop(q)  == \E mm \in sent  : mm.type = "Proposal" /\ mm.round = round[q]  /\ mm.sender = q
<1> DEFINE PropP(q) == \E mm \in sent' : mm.type = "Proposal" /\ mm.round = round'[q] /\ mm.sender = q
<1> DEFINE POs  == {q \in Honest : step[q]  = "propose" /\ ~Prop(q)}
<1> DEFINE POs2 == {q \in Honest : step'[q] = "propose" /\ ~PropP(q)}
<1>r. /\ round[p] \in Nat
      /\ valid[p].round \in Rounds \cup {-1}
      /\ valid[p].value \in ValuesOrNil
  BY DEF TypeOK, Rounds, LockState
<1>act. round' = round /\ step' = step
  BY DEF Propose
<1>v. PICK v \in (IF valid[p].value # nil THEN {valid[p].value} ELSE getValue) :
        Broadcast(p, Proposal(p, round[p], v, valid[p].round))
  BY DEF Propose
<1> DEFINE m == Proposal(p, round[p], v, valid[p].round)
<1>vval. v \in Values
  BY <1>r, <1>v DEFS getValue, ValuesOrNil
<1>mty. m \in Message
  BY <1>r, <1>vval, HonestSubValidators DEF Proposal, ProposalMsg, Message, Rounds
<1>mflds. m.type = "Proposal" /\ m.round = round[p] /\ m.sender = p
  BY DEF Proposal
<1>bc. sentTime' = [sentTime EXCEPT ![m] = now]
  BY <1>v DEF Broadcast
<1>nn. now # OFF
  BY NowNotOff
<1>se. sent \subseteq sent' /\ m \in sent'
  BY <1>bc, <1>mty, <1>nn DEFS sent, TypeOK
<1>g. step[p] = "propose" /\ ~Prop(p)
  BY DEF Propose
<1>monoSent. \A q \in Honest : Prop(q) => PropP(q)
  BY <1>act, <1>se
<1>posub. POs2 \subseteq POs /\ p \in POs /\ p \notin POs2
  BY <1>act, <1>g, <1>mflds, <1>monoSent, <1>se
<1>pofin. IsFiniteSet(POs)
  BY HonestSubsetFinite
<1>polt. Cardinality(POs2) < Cardinality(POs)
  BY ONLY <1>posub, <1>pofin, StrictSubsetCard
<1>podef1. ProposeOwed = Cardinality(POs)
  BY DEF ProposeOwed
<1>podef2. ProposeOwed' = Cardinality(POs2)
  BY ONLY DEF ProposeOwed
<1>potyp. Cardinality(POs) \in Nat /\ Cardinality(POs2) \in Nat
  BY HonestSubsetFinite
<1> QED
  BY ONLY <1>polt, <1>podef1, <1>podef2, <1>potyp

\* ---- Timer-arming actions drop OffLiveTimers by at least one ------------
\* ScheduleTimeoutPrevote arms the prevote timer of p, from OFF to now +
\* TimeoutPrevote. p therefore leaves the set "prevote step, prevote timer
\* OFF". The precommit set is untouched, because the nested EXCEPT changes
\* only timer[p]["prevote"].
LEMMA OffLiveTimersDropsArmPrevote ==
  ASSUME TypeOK, NEW p \in Honest, ScheduleTimeoutPrevote(p)
  PROVE  OffLiveTimers \in Nat /\ OffLiveTimers' \in Nat /\ OffLiveTimers' + 1 <= OffLiveTimers
<1> DEFINE PV  == {q \in Honest : step[q]  = "prevote" /\ timer[q]["prevote"]    = OFF}
<1> DEFINE PC  == {q \in Honest : step[q]  # "decided" /\ timer[q]["precommit"]  = OFF}
<1> DEFINE PV2 == {q \in Honest : step'[q] = "prevote" /\ timer'[q]["prevote"]   = OFF}
<1> DEFINE PC2 == {q \in Honest : step'[q] # "decided" /\ timer'[q]["precommit"] = OFF}
<1>ty. timer \in [Honest -> [TimerType -> Int]] /\ step \in [Honest -> Step]
  BY DEF TypeOK
<1>act. step' = step
        /\ timer' = [timer EXCEPT ![p]["prevote"] = now + TimeoutPrevote(round[p])]
        /\ step[p] = "prevote" /\ timer[p]["prevote"] = OFF
  BY DEF ScheduleTimeoutPrevote
<1>arm. now + TimeoutPrevote(round[p]) # OFF
  BY T0PrevoteType, TDeltaType DEFS OFF, Rounds, TimeoutPrevote, TypeOK
<1>tp. \A q \in Honest : timer'[q]["prevote"] = IF q = p THEN now + TimeoutPrevote(round[p]) ELSE timer[q]["prevote"]
  BY <1>act, <1>ty DEF TypeOK, TimerType
<1>tc. \A q \in Honest : timer'[q]["precommit"] = timer[q]["precommit"]
  BY <1>act, <1>ty DEF TypeOK, TimerType
\* precommit set unchanged.
<1>pceq. PC2 = PC
  BY <1>act, <1>tc
<1>pcfin. IsFiniteSet(PC) /\ Cardinality(PC) \in Nat
  BY HonestSubsetFinite
\* prevote set: p leaves it, others stay.
<1>pvsub. PV2 \subseteq PV /\ p \in PV /\ p \notin PV2
  BY <1>act, <1>arm, <1>tp
<1>pvfin. IsFiniteSet(PV)
  BY HonestSubsetFinite
<1>pvlt. Cardinality(PV2) < Cardinality(PV)
  BY ONLY <1>pvsub, <1>pvfin, StrictSubsetCard
<1>pvn. Cardinality(PV) \in Nat /\ Cardinality(PV2) \in Nat
  BY HonestSubsetFinite
<1>def1. OffLiveTimers = Cardinality(PV) + Cardinality(PC)
  BY DEF OffLiveTimers
<1>def2. OffLiveTimers' = Cardinality(PV2) + Cardinality(PC2)
  BY DEF OffLiveTimers
<1> QED
  BY <1>def1, <1>def2, <1>pceq, <1>pvlt, <1>pvn, <1>pcfin

\* ScheduleTimeoutPrecommit arms the precommit timer of p. The case is
\* symmetric to the prevote case. It drops the precommit set, and it leaves
\* the prevote set untouched.
LEMMA OffLiveTimersDropsArmPrecommit ==
  ASSUME TypeOK, NEW p \in Honest, ScheduleTimeoutPrecommit(p)
  PROVE  OffLiveTimers \in Nat /\ OffLiveTimers' \in Nat /\ OffLiveTimers' + 1 <= OffLiveTimers
<1> DEFINE PV  == {q \in Honest : step[q]  = "prevote" /\ timer[q]["prevote"]    = OFF}
<1> DEFINE PC  == {q \in Honest : step[q]  # "decided" /\ timer[q]["precommit"]  = OFF}
<1> DEFINE PV2 == {q \in Honest : step'[q] = "prevote" /\ timer'[q]["prevote"]   = OFF}
<1> DEFINE PC2 == {q \in Honest : step'[q] # "decided" /\ timer'[q]["precommit"] = OFF}
<1>ty. timer \in [Honest -> [TimerType -> Int]] /\ step \in [Honest -> Step]
  BY DEF TypeOK
<1>act. step' = step
        /\ timer' = [timer EXCEPT ![p]["precommit"] = now + TimeoutPrecommit(round[p])]
        /\ step[p] # "decided" /\ timer[p]["precommit"] = OFF
  BY DEF ScheduleTimeoutPrecommit
<1>arm. now + TimeoutPrecommit(round[p]) # OFF
  BY T0PrecommitType, TDeltaType DEFS OFF, Rounds, TimeoutPrecommit, TypeOK
<1>tc. \A q \in Honest : timer'[q]["precommit"] = IF q = p THEN now + TimeoutPrecommit(round[p]) ELSE timer[q]["precommit"]
  BY <1>act, <1>ty DEF TypeOK, TimerType
<1>tp. \A q \in Honest : timer'[q]["prevote"] = timer[q]["prevote"]
  BY <1>act, <1>ty DEF TypeOK, TimerType
<1>pveq. PV2 = PV
  BY <1>act, <1>tp
<1>pvfin. IsFiniteSet(PV) /\ Cardinality(PV) \in Nat
  BY HonestSubsetFinite
<1>pcsub. PC2 \subseteq PC /\ p \in PC /\ p \notin PC2
  BY <1>act, <1>arm, <1>tc
<1>pcfin. IsFiniteSet(PC)
  BY HonestSubsetFinite
<1>pclt. Cardinality(PC2) < Cardinality(PC)
  BY ONLY <1>pcsub, <1>pcfin, StrictSubsetCard
<1>pcn. Cardinality(PC) \in Nat /\ Cardinality(PC2) \in Nat
  BY HonestSubsetFinite
<1>def1. OffLiveTimers = Cardinality(PV) + Cardinality(PC)
  BY DEF OffLiveTimers
<1>def2. OffLiveTimers' = Cardinality(PV2) + Cardinality(PC2)
  BY DEF OffLiveTimers
<1> QED
  BY <1>def1, <1>def2, <1>pveq, <1>pclt, <1>pcn, <1>pvfin

\* ---- LateUpdate drops ValidStale by at least one ------------------------
\* OnPrevoteQuorumValueLateUpdate sets valid[p].round := round[p]. The stale
\* condition valid[p].round < round[p] therefore flips to false, and p leaves
\* ValidStale. round is untouched, and so is the valid record of every other
\* validator.
LEMMA ValidStaleDropsLateUpdate ==
  ASSUME TypeOK, NEW p \in Honest, OnPrevoteQuorumValueLateUpdate(p)
  PROVE  ValidStale \in Nat /\ ValidStale' \in Nat /\ ValidStale' + 1 <= ValidStale
<1> DEFINE VS  == {q \in Honest : valid[q].round  < round[q]}
<1> DEFINE VS2 == {q \in Honest : valid'[q].round < round'[q]}
<1>ty. valid \in [Honest -> LockState] /\ round \in [Honest -> Nat]
  BY DEF TypeOK, Rounds
<1>g. valid[p].round < round[p]
  BY DEF OnPrevoteQuorumValueLateUpdate
<1>act. round' = round
        /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
             valid' = [valid EXCEPT ![p] = [value |-> prop.value, round |-> round[p]]]
  BY DEF OnPrevoteQuorumValueLateUpdate
<1>vp. valid'[p].round = round[p]
  BY <1>act, <1>ty DEF TypeOK
<1>vq. \A q \in Honest : q # p => valid'[q] = valid[q]
  BY <1>act, <1>ty DEF TypeOK
<1>sub. VS2 \subseteq VS /\ p \in VS /\ p \notin VS2
  BY <1>act, <1>g, <1>ty, <1>vp, <1>vq
<1>fin. IsFiniteSet(VS)
  BY HonestSubsetFinite
<1>lt. Cardinality(VS2) < Cardinality(VS)
  BY ONLY <1>sub, <1>fin, StrictSubsetCard
<1>n. Cardinality(VS) \in Nat /\ Cardinality(VS2) \in Nat
  BY HonestSubsetFinite
<1>def1. ValidStale = Cardinality(VS)
  BY DEF ValidStale
<1>def2. ValidStale' = Cardinality(VS2)
  BY DEF ValidStale
<1> QED
  BY <1>lt, <1>n, <1>def1, <1>def2

\* ---- The honest compute burst strictly decreases the lexicographic triple
\*      << RoundGap, StepWork, BurstBottom >> ------------------------------
\* The proof is a case split over the thirteen disjuncts of HonestStep. A
\* raise of a round drops the top component, which is RoundGap, and the frozen
\* RoundCeiling bounds it. An advance of a step drops the middle component,
\* which is StepWork. Propose, a timer arming and a late update of valid drop
\* the bottom component, which is ProposeOwed, OffLiveTimers and ValidStale.
\* RoundBelowNow supplies round[p] < RoundCeiling for the cases that raise a
\* round. DecidedStepOp excludes a decide from a step that is already
\* "decided". OnPrecommitQuorumValue has no guard on the step, and only the
\* guard decision[p] = nil. That is the one place where a decide would not
\* drop StepWork.
LEMMA ComputeWorkDecreasesCompute ==
  ASSUME TypeOK, NEW p \in Honest,
         \A c \in Honest : round[c] <= now,
         \A c \in Honest : decision[c] = nil => step[c] # "decided",
         HonestStep(p)
  PROVE  \/ RoundGap' < RoundGap
         \/ (RoundGap' = RoundGap /\ StepWork' < StepWork)
         \/ (RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' < BurstBottom)
<1>ty. step \in [Honest -> Step] /\ round \in [Honest -> Nat] /\ valid \in [Honest -> LockState]
       /\ timer \in [Honest -> [TimerType -> Int]] /\ now \in Nat
  BY DEF TypeOK, Rounds
<1>hn. Cardinality(Honest) \in Nat
  BY HonestFinite, FS_CardinalityType
<1>rlt. round[p] < RoundCeiling
  BY <1>hn, <1>ty, MultMono DEF RoundCeiling
<1>bn. ProposeOwed \in Nat /\ OffLiveTimers \in Nat /\ ValidStale \in Nat
  BY OwedTimersNat
\* ===== Top component: round-raising actions =====
<1>1. CASE OnTimeoutPrecommit(p)
  BY <1>1, <1>rlt, <1>ty, RoundGapDecreaseRaise DEF OnTimeoutPrecommit
<1>2. CASE \E r \in Rounds : SkipRound(p, r)
  BY <1>2, <1>rlt, <1>ty, RoundGapDecreaseRaise DEFS Rounds, SkipRound
<1>3. CASE OnTimeoutPropose(p)
  BY <1>3, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnTimeoutPropose, Step, StepBudget, TypeOK
<1>4. CASE OnProposalNoPOL(p)
  BY <1>4, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnProposalNoPOL, Step, StepBudget, TypeOK
<1>5. CASE OnProposalWithPOL(p)
  BY <1>5, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnProposalWithPOL, Step, StepBudget, TypeOK
<1>6. CASE OnPrevoteQuorumValueFirstTime(p)
  BY <1>6, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnPrevoteQuorumValueFirstTime, Step, StepBudget, TypeOK
<1>7. CASE OnPrevoteQuorumNil(p)
  BY <1>7, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnPrevoteQuorumNil, Step, StepBudget, TypeOK
<1>8. CASE OnTimeoutPrevote(p)
  BY <1>8, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnTimeoutPrevote, Step, StepBudget, TypeOK
<1>9. CASE OnPrecommitQuorumValue(p)
  BY <1>9, <1>ty, RoundGapUnchanged, StepWorkDecreaseStep DEFS OnPrecommitQuorumValue, Step, StepBudget, TypeOK
<1>10. CASE Propose(p)
  BY <1>10, <1>bn, OffLiveTimersUnchanged, ProposeOwedDropsPropose, RoundGapUnchanged, StepWorkUnchanged, ValidStaleUnchanged
  DEFS BurstBottom, Propose
<1>11. CASE ScheduleTimeoutPrevote(p)
  BY <1>11, <1>bn, OffLiveTimersDropsArmPrevote, ProposeOwedUnchanged, RoundGapUnchanged, StepWorkUnchanged, ValidStaleUnchanged
  DEFS BurstBottom, ScheduleTimeoutPrevote
<1>12. CASE ScheduleTimeoutPrecommit(p)
  BY <1>12, <1>bn, OffLiveTimersDropsArmPrecommit, ProposeOwedUnchanged, RoundGapUnchanged, StepWorkUnchanged, ValidStaleUnchanged
  DEFS BurstBottom, ScheduleTimeoutPrecommit
<1>13. CASE OnPrevoteQuorumValueLateUpdate(p)
  BY <1>13, <1>bn, OffLiveTimersUnchanged, ProposeOwedUnchanged, RoundGapUnchanged, StepWorkUnchanged, ValidStaleDropsLateUpdate
  DEFS BurstBottom, OnPrevoteQuorumValueLateUpdate
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13
     DEF HonestStep

\* ---- Deliver and FaultyStep leave the whole triple fixed -----------------
\* This is the half about independence from the faulty validators. Deliver
\* changes only rcvd. FaultyStep grows sent with a message whose sender is
\* FAULTY, and such a message cannot witness the honest predicate "has
\* proposed". ProposeOwed is therefore fixed, and so is every other component.
LEMMA ComputeWorkUnchangedDeliver ==
  ASSUME TypeOK, NEW p \in Honest, Deliver(p)
  PROVE  RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' = BurstBottom
<1>u. round' = round /\ now' = now /\ step' = step /\ timer' = timer
      /\ sentTime' = sentTime /\ valid' = valid
  BY DEF Deliver
<1>1. RoundGap' = RoundGap
  BY <1>u, RoundGapUnchanged
<1>2. StepWork' = StepWork
  BY <1>u, StepWorkUnchanged
<1>3. OffLiveTimers' = OffLiveTimers
  BY <1>u, OffLiveTimersUnchanged
<1>4. ProposeOwed' = ProposeOwed
  BY <1>u, ProposeOwedUnchanged
<1>5. ValidStale' = ValidStale
  BY <1>u, ValidStaleUnchanged
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF BurstBottom

LEMMA ComputeWorkUnchangedFaulty ==
  ASSUME TypeOK, NEW p \in Faulty, FaultyStep(p)
  PROVE  RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' = BurstBottom
<1>u. round' = round /\ now' = now /\ step' = step /\ timer' = timer /\ valid' = valid
  BY DEF FaultyStep
<1>1. RoundGap' = RoundGap
  BY <1>u, RoundGapUnchanged
<1>2. StepWork' = StepWork
  BY <1>u, StepWorkUnchanged
<1>3. OffLiveTimers' = OffLiveTimers
  BY <1>u, OffLiveTimersUnchanged
<1>5. ValidStale' = ValidStale
  BY <1>u, ValidStaleUnchanged
<1>4. ProposeOwed' = ProposeOwed
  <2>1. PICK m \in Message : m.sender = p /\ sentTime' = [sentTime EXCEPT ![m] = now]
    BY DEF FaultyStep
  <2>2. m.sender \notin Honest
    BY <2>1 DEF Honest
  <2>st. step' = step /\ round' = round
    BY <1>u
  <2>ex. \A mm \in Message : sentTime'[mm] = (IF mm = m THEN now ELSE sentTime[mm])
    BY <2>1 DEF TypeOK
  <2>iff. \A q \in Honest :
            (\E msg \in sent'  : msg.type = "Proposal" /\ msg.round = round[q] /\ msg.sender = q)
              <=> (\E msg \in sent : msg.type = "Proposal" /\ msg.round = round[q] /\ msg.sender = q)
    BY <2>2, <2>ex DEF sent
  <2>seteq. {q \in Honest : step'[q] = "propose"
              /\ ~(\E msg \in sent' : msg.type = "Proposal" /\ msg.round = round'[q] /\ msg.sender = q)}
          = {q \in Honest : step[q] = "propose"
              /\ ~(\E msg \in sent : msg.type = "Proposal" /\ msg.round = round[q] /\ msg.sender = q)}
    BY <2>st, <2>iff
  <2>po. ProposeOwed = Cardinality({q \in Honest : step[q] = "propose"
              /\ ~(\E msg \in sent : msg.type = "Proposal" /\ msg.round = round[q] /\ msg.sender = q)})
    BY DEF ProposeOwed
  <2>po2. ProposeOwed' = Cardinality({q \in Honest : step'[q] = "propose"
              /\ ~(\E msg \in sent' : msg.type = "Proposal" /\ msg.round = round'[q] /\ msg.sender = q)})
    BY DEF ProposeOwed
  <2> QED BY <2>seteq, <2>po, <2>po2
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF BurstBottom

\* ---- Collapse the lexicographic triple to the single Nat BurstScalar -----
LEMMA BurstBoundNat == Cardinality(Honest) \in Nat /\ BurstBound \in Nat
BY HonestFinite, FS_CardinalityType DEF BurstBound

\* Typing + boundedness of the two lower components (both <= BurstBound), the
\* facts the Horner collapse (Collapse3) consumes in each state.
BurstFactsOp ==
  /\ RoundGap \in Nat /\ StepWork \in Nat /\ BurstBottom \in Nat
  /\ StepWork <= BurstBound
  /\ BurstBottom <= BurstBound

LEMMA BurstFactsFromType ==
  ASSUME TypeOK
  PROVE  BurstFactsOp
<1>hf. Cardinality(Honest) \in Nat
  BY HonestFinite, FS_CardinalityType
<1>rgn. RoundGap \in Nat
  BY RoundGapNat
<1>swn. StepWork \in Nat
  BY StepWorkNat
<1>bbn. BurstBottom \in Nat
  BY OwedTimersNat DEF BurstBottom
<1>swb. StepWork <= BurstBound
  BY <1>hf, <1>swn, CardHonestProd3, SMT DEFS BurstBound, StepWork
<1>bob. BurstBottom <= BurstBound
  BY <1>hf, FS_Subset, HonestFinite, HonestSubsetFinite, OwedTimersNat, SMT
  DEFS BurstBottom, BurstBound, OffLiveTimers, ProposeOwed, ValidStale
<1> QED BY <1>rgn, <1>swn, <1>bbn, <1>swb, <1>bob DEF BurstFactsOp

THEOREM BurstFactsInv == Spec => []BurstFactsOp
<1> SUFFICES ASSUME Spec PROVE []BurstFactsOp
  OBVIOUS
<1>1. []TypeOK
  BY InvProof, PTL DEF Spec, Inv
<1>2. []BurstFactsOp
  BY <1>1, BurstFactsFromType, PTL
<1> QED BY <1>2

LEMMA BurstScalarNat ==
  ASSUME BurstFactsOp PROVE BurstScalar \in Nat
BY BurstBoundNat DEFS BurstFactsOp, BurstScalar

\* ===========================================================================
\* Task 1.2 deliverables. ComputeWork is a Nat. It equals 0 only at honest
\* quiescence, and it strictly decreases on every honest compute step. Deliver
\* and FaultyStep leave it fixed. These are what the WF1 chain for burst
\* termination of Task 1.4 consumes.
\* ===========================================================================

\* (a) ComputeWork \in Nat.
LEMMA ComputeWorkType ==
  ASSUME TypeOK PROVE ComputeWork \in Nat
BY BurstFactsFromType, BurstScalarNat DEF ComputeWork

\* (b) ComputeWork strictly decreases on an honest compute step. The
\* both-state BurstFactsOp are supplied by the caller from []BurstFactsOp.
LEMMA ComputeWorkDecreasesStep ==
  ASSUME TypeOK, NEW p \in Honest,
         \A c \in Honest : round[c] <= now,
         \A c \in Honest : decision[c] = nil => step[c] # "decided",
         HonestStep(p), BurstFactsOp, BurstFactsOp'
  PROVE  ComputeWork' < ComputeWork
<1>lex. \/ RoundGap' < RoundGap
        \/ (RoundGap' = RoundGap /\ StepWork' < StepWork)
        \/ (RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' < BurstBottom)
  BY ComputeWorkDecreasesCompute
<1>bn. BurstBound \in Nat
  BY BurstBoundNat
<1>bb. BurstBound' = BurstBound
  BY DEF BurstBound
<1>n1. /\ RoundGap \in Nat /\ StepWork \in Nat /\ BurstBottom \in Nat
       /\ RoundGap' \in Nat /\ StepWork' \in Nat /\ BurstBottom' \in Nat
       /\ StepWork' <= BurstBound /\ BurstBottom' <= BurstBound
  BY <1>bb DEF BurstFactsOp
<1>col. (BurstBound + 1) * ((BurstBound + 1) * RoundGap' + StepWork') + BurstBottom'
          < (BurstBound + 1) * ((BurstBound + 1) * RoundGap + StepWork) + BurstBottom
  BY <1>lex, <1>bn, <1>n1, Collapse3
<1>defp. BurstScalar' = (BurstBound + 1) * ((BurstBound + 1) * RoundGap' + StepWork') + BurstBottom'
  BY <1>bb DEF BurstScalar
<1> QED BY <1>col, <1>defp DEF ComputeWork, BurstScalar

LEMMA ComputeWorkUnchangedDeliverStep ==
  ASSUME TypeOK, NEW p \in Honest, Deliver(p)
  PROVE  ComputeWork' = ComputeWork
<1>1. RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' = BurstBottom
  BY ComputeWorkUnchangedDeliver
<1>bb. BurstBound' = BurstBound
  BY DEF BurstBound
<1> QED BY <1>1, <1>bb DEF ComputeWork, BurstScalar

LEMMA ComputeWorkUnchangedFaultyStep ==
  ASSUME TypeOK, NEW p \in Faulty, FaultyStep(p)
  PROVE  ComputeWork' = ComputeWork
<1>1. RoundGap' = RoundGap /\ StepWork' = StepWork /\ BurstBottom' = BurstBottom
  BY ComputeWorkUnchangedFaulty
<1>bb. BurstBound' = BurstBound
  BY DEF BurstBound
<1> QED BY <1>1, <1>bb DEF ComputeWork, BurstScalar

\* (c) ComputeWork = 0 implies honest quiescence (no CanCompute enabled).
\* BurstScalar = 0 forces StepWork = 0 (every honest validator is "decided") and
\* ValidStale = 0 (no honest valid record is stale). DecidedStepOp then gives
\* decision # nil for the decided validators, so every CanCompute disjunct is
\* falsified by one of {step = "decided", decision # nil, valid.round >= round}.
LEMMA ComputeWorkZeroQuiescent ==
  ASSUME TypeOK, ComputeWork = 0,
         \A c \in Honest : decision[c] = nil => step[c] # "decided"
  PROVE  ~ \E p \in Honest : CanCompute(p)
<1>hf. Cardinality(Honest) \in Nat /\ IsFiniteSet(Honest)
  BY HonestFinite, FS_CardinalityType
<1>bn. BurstBound \in Nat
  BY BurstBoundNat
<1>comp. RoundGap \in Nat /\ StepWork \in Nat /\ BurstBottom \in Nat
         /\ ProposeOwed \in Nat /\ OffLiveTimers \in Nat /\ ValidStale \in Nat
  BY RoundGapNat, StepWorkNat, OwedTimersNat DEF BurstBottom
<1>ty. step \in [Honest -> Step] /\ round \in [Honest -> Nat] /\ valid \in [Honest -> LockState]
  BY DEF TypeOK, Rounds
\* --- BurstScalar = 0 forces the top-of-collapse and the bottom to be 0 ---
<1>zero. StepWork = 0 /\ ValidStale = 0
  <2> DEFINE M == (BurstBound + 1) * RoundGap + StepWork
  <2>1. (BurstBound + 1) * M + BurstBottom = 0
    BY DEF ComputeWork, BurstScalar
  <2>Mn. M \in Nat /\ (BurstBound + 1) * M \in Nat
    BY <1>comp, <1>bn
  <2>2. (BurstBound + 1) * M = 0 /\ BurstBottom = 0
    BY <2>1, <2>Mn, <1>comp
  <2>3. M = 0
    BY <1>bn, <2>2, <2>Mn, MultMono
  <2>4. StepWork = 0
    BY <2>3, <1>comp, <1>bn
  <2>5. ValidStale = 0
    BY <2>2, <1>comp DEF BurstBottom
  <2> QED BY <2>4, <2>5
\* --- StepWork = 0 => every honest validator is "decided" ---
<1>dec. \A c \in Honest : step[c] = "decided"
  <2> SUFFICES ASSUME NEW c \in Honest, step[c] # "decided" PROVE FALSE
    OBVIOUS
  <2> DEFINE S == {pj \in Honest \X (1 .. 3) : pj[2] <= StepBudget(pj[1])}
  <2>1. step[c] \in Step /\ StepBudget(c) \in 1 .. 3
    BY <1>ty DEF StepBudget, Step
  <2>2. << c, 1 >> \in S
    BY <2>1
  <2>3. StepWork = Cardinality(S)
    BY DEF StepWork
  <2>4. IsFiniteSet(S)
    BY <1>hf, FS_Interval, FS_Product, FS_Subset
  <2>5. {<< c, 1 >>} \subseteq S /\ Cardinality({<< c, 1 >>}) = 1
    BY <2>2, FS_Singleton
  <2>6. Cardinality(S) >= 1
    BY <2>4, <2>5, FS_Subset, FS_CardinalityType
  <2> QED BY <2>3, <2>6, <1>zero
\* --- ValidStale = 0 => no honest valid record is stale ---
<1>vs. \A c \in Honest : ~(valid[c].round < round[c])
  <2> SUFFICES ASSUME NEW c \in Honest, valid[c].round < round[c] PROVE FALSE
    OBVIOUS
  <2> DEFINE VS == {q \in Honest : valid[q].round < round[q]}
  <2>1. c \in VS
    OBVIOUS
  <2>2. ValidStale = Cardinality(VS)
    BY DEF ValidStale
  <2>3. IsFiniteSet(VS)
    BY HonestSubsetFinite
  <2>4. {c} \subseteq VS /\ Cardinality({c}) = 1
    BY <2>1, FS_Singleton
  <2>5. Cardinality(VS) >= 1
    BY <2>3, <2>4, FS_Subset, FS_CardinalityType
  <2> QED BY <2>2, <2>5, <1>zero
\* --- every CanCompute disjunct is now falsified ---
<1> SUFFICES ASSUME NEW p \in Honest, CanCompute(p) PROVE FALSE
  OBVIOUS
<1>d1. step[p] = "decided"
  BY <1>dec
<1>d2. ~(valid[p].round < round[p])
  BY <1>vs
<1>d3. decision[p] # nil
  BY <1>d1
<1> QED BY <1>d1, <1>d2, <1>d3 DEF CanCompute

-----------------------------------------------------------------------------
(***************************************************************************)
(* Phase-4 support for reaching and then staying strictly past GST.        *)
(*                                                                         *)
(* The distance metric Mreach == IF now > GST THEN 0 ELSE (GST+1) - now    *)
(* is a Nat with Mreach = 0 <=> now > GST, so <>(now > GST) reduces by     *)
(* NaturalsInduction to a per-step distance drop. Targeting the STRICT      *)
(* bound directly folds the boundary Tick (now = GST -> GST+1) into that    *)
(* future WF1 obligation.                                                   *)
(*                                                                         *)
(* The checked state and commute helpers stay here; Lemma7Selection owns    *)
(* the open WF1 reach.                                                      *)
(***************************************************************************)

Mreach == IF now > GST THEN 0 ELSE (GST + 1) - now

LEMMA MreachNatState == TypeOK => Mreach \in Nat
  BY GSTType DEF TypeOK, Mreach

LEMMA BoxMreachZero == [](TypeOK => (Mreach <= 0 => now > GST))
<1>1. TypeOK => (Mreach <= 0 => now > GST)
  BY GSTType DEF TypeOK, Mreach
<1> QED BY <1>1, PTL

LEMMA BoxMreachSplit ==
  ASSUME NEW n \in Nat
  PROVE  [](TypeOK => (Mreach <= n + 1 => (Mreach <= n \/ Mreach = n + 1)))
<1>1. TypeOK => (Mreach <= n + 1 => (Mreach <= n \/ Mreach = n + 1))
  BY MreachNatState
<1> QED BY <1>1, PTL

LEMMA BoxMreachExN == [](TypeOK => (\E n \in Nat : Mreach <= n))
<1>1. TypeOK => (\E n \in Nat : Mreach <= n)
  BY MreachNatState
<1> QED BY <1>1, PTL

\* Existential-leads-to commute, specialized to Mreach and the goal now > GST:
\* concludes the <>-goal from the staircase \A n : (Mreach <= n) ~> (now > GST)
\* without instantiating the forall-leads-to at a point (the TLAPS wall).
LEMMA ReachCommute ==
  ASSUME NEW TEMPORAL D, \A n \in Nat : []((Mreach <= n) => D)
  PROVE  [](\A n \in Nat : ((Mreach <= n) => D))
OBVIOUS

LEMMA ReachBoxFO ==
  [](  (\A n \in Nat : ((Mreach <= n) => <>(now > GST)))
       => ((\E n \in Nat : (Mreach <= n)) => <>(now > GST))  )
<1>1. (\A n \in Nat : ((Mreach <= n) => <>(now > GST)))
        => ((\E n \in Nat : (Mreach <= n)) => <>(now > GST))
  OBVIOUS
<1> QED BY <1>1, PTL

THEOREM ReachExistsLT ==
  ASSUME \A n \in Nat : ((Mreach <= n) ~> (now > GST))
  PROVE  (\E n \in Nat : (Mreach <= n)) ~> (now > GST)
<1>0. \A n \in Nat : []((Mreach <= n) => <>(now > GST))
  BY PTL
<1>1. [](\A n \in Nat : ((Mreach <= n) => <>(now > GST)))
  BY <1>0, ReachCommute
<1>2. [](  (\A n \in Nat : ((Mreach <= n) => <>(now > GST)))
           => ((\E n \in Nat : (Mreach <= n)) => <>(now > GST))  )
  BY ReachBoxFO
<1> QED BY <1>1, <1>2, PTL

\* The checked distance and burst helpers above are consumed by ...NonZeno and
\* ...RoundProgress, which own the WF1 reachability argument.

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)