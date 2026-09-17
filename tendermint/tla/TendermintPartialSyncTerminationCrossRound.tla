------------------ MODULE TendermintPartialSyncTerminationCrossRound -----------
(***************************************************************************)
(*  Cross-round convergence above the ceiling of the stable entry. A high  *)
(*  correct value precommit stops every correct process from leaving its   *)
(*  round. This holds while another undecided correct process still has no *)
(*  valid record at that round. Bounded delivery and maximal progress then *)
(*  make the conclusion of paper Lemma 6 an inductive invariant, and not a *)
(*  leads-to fact. There is no operator with the name Lemma6. ValidCatchUp *)
(*  is the inductive form of that lemma. HighLockCatchUp is the conclusion *)
(*  that the module exports, after the delivery deadline.                  *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationRoundProgress

DomCeiling == 2 * Delta + GST

TimeoutsSufficientBeyond ==
  \A r \in Rounds : r >= 2 * Delta => Lemma5Timeouts(r)

\* Paper Lemma 6, inductive form. While any undecided correct process still
\* has no valid round for the high lock, every correct process stays at or
\* below that round. The clock also stays at or before the delivery deadline
\* of the lock.
ValidCatchUp ==
  \A x \in Honest, rr \in Rounds, w \in Values :
    ( /\ Precommit(x, rr, w) \in sent
      /\ rr > DomCeiling
      /\ \E c \in Honest : valid[c].round < rr /\ ~HasDecided(c) )
    => /\ \A c \in Honest : round[c] <= rr
       /\ now <= sentTime[Precommit(x, rr, w)] + Delta

\* Paper Lemma 6, consumer form after the high lock's delivery deadline.
HighLockCatchUp ==
  \A x \in Honest, rr \in Rounds, w \in Values :
    ( /\ Precommit(x, rr, w) \in sent
      /\ rr > DomCeiling
      /\ now > sentTime[Precommit(x, rr, w)] + Delta )
    => \A e \in Honest : valid[e].round >= rr \/ HasDecided(e)

-----------------------------------------------------------------------------
\* State support used by the joint induction.

EntryTimeGeRound ==
  \A c \in Honest : \A r \in Rounds :
    enteredAt[c][r] # OFF => enteredAt[c][r] >= r

LEMMA EntryTimeGeRoundStepL ==
  ASSUME TypeOK, [Next]_vars, RoundBelowNow', EntryTimeGeRound
  PROVE  EntryTimeGeRound'
BY RoundEnteredStep
DEFS Deliver, EntryTimeGeRound, FaultyStep, HonestNext, HonestStep, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
  OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
  OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
  RoundBelowNow, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote,
  SkipRound, Tick, TypeOK, vars

THEOREM EntryTimeGeRoundInv == ASSUME Spec PROVE []EntryTimeGeRound
<1>1. EntryTimeGeRound
  BY DEFS EntryTimeGeRound, Init, OFF, Spec
<1>2. [](TypeOK /\ RoundBelowNow /\ [Next]_vars)
  BY InvProof, RoundBelowNowInv, PTL DEF Spec, Inv
<1>3. [](EntryTimeGeRound => EntryTimeGeRound')
  BY <1>2, EntryTimeGeRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

ValidMonotone ==
  \A c \in Honest : valid[c].round <= valid'[c].round

LEMMA ValidMonotoneStep ==
  ASSUME TypeOK, [Next]_vars, ValidBelowRound
  PROVE  ValidMonotone
BY CrossRoundMonotoneStep
DEFS Deliver, FaultyStep, HonestNext, HonestStep, LockState, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, ValidBelowRound,
  ValidMonotone, vars

LEMMA UndecidedBackStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, ~(HasDecided(c))'
  PROVE  ~HasDecided(c)
BY NilNotInValues
DEFS Deliver, FaultyStep, HasDecided, HonestNext, HonestStep, Message, Next,
  OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, PrecommitMsg, PrevoteMsg, ProposalMsg, Propose,
  RProposals, RProposalsFromProposerAt, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, sent, SkipRound, Tick, TypeOK, vars

LEMMA MissingValidBackStep ==
  ASSUME TypeOK, TypeOK', [Next]_vars, ValidBelowRound, NEW c \in Honest,
         NEW rr \in Rounds, valid'[c].round < rr, ~(HasDecided(c))'
  PROVE  valid[c].round < rr /\ ~HasDecided(c)
<1>1. ValidMonotone
  BY ValidMonotoneStep
<1>2. valid[c].round <= valid'[c].round
  BY <1>1 DEF ValidMonotone
<1>ty. valid[c].round \in Int /\ valid'[c].round \in Int /\ rr \in Nat
  BY DEFS LockState, Rounds, TypeOK
<1>3. valid[c].round < rr
  BY <1>2, <1>ty, SMT
<1>4. ~HasDecided(c)
  BY UndecidedBackStep
<1> QED
  BY <1>3, <1>4

LEMMA HighRoundFacts ==
  ASSUME TypeOK, NEW rr \in Rounds, rr > DomCeiling
  PROVE  /\ rr > GST
         /\ rr >= 2 * Delta
         /\ ~(rr < GST)
BY DeltaType, GSTType DEFS DomCeiling, Rounds

LEMMA HighRoundPrecommitTimeout ==
  ASSUME TypeOK, TimeoutsSufficientBeyond,
         NEW rr \in Rounds, rr > DomCeiling
  PROVE  TimeoutPrecommit(rr) > 2 * Delta
BY HighRoundFacts DEF Lemma5Timeouts, TimeoutsSufficientBeyond

LEMMA NatOrderAbove ==
  ASSUME NEW lower \in Nat, NEW upper \in Nat, NEW floor \in Nat,
         lower <= upper, lower > floor
  PROVE  upper >= floor
BY SMT

LEMMA PrecommitTimerGapArithmetic ==
  ASSUME NEW lockTime \in Nat, NEW quorumTime \in Nat,
         NEW deadline \in Int, NEW timeout \in Nat, NEW delay \in Nat,
         quorumTime <= deadline - timeout,
         lockTime <= quorumTime + delay,
         timeout > 2 * delay
  PROVE  deadline > lockTime + delay
BY SMT

LEMMA NatLinearOrder ==
  ASSUME NEW a \in Nat, NEW b \in Nat
  PROVE  a <= b \/ a > b
BY SMT

LEMMA NatSuccessorAtCeiling ==
  ASSUME NEW current \in Nat, NEW ceiling \in Nat, NEW next \in Nat,
         current <= ceiling, next = current + 1, next > ceiling
  PROVE  current = ceiling
BY SMT

LEMMA NatLeTransitive ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat,
         a <= b, b <= c
  PROVE  a <= c
BY SMT

LEMMA IntNotGeLt ==
  ASSUME NEW a \in Int, NEW b \in Int, ~(a >= b)
  PROVE  a < b
BY SMT

LEMMA NatGtLeContradiction ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a > b, a <= b
  PROVE  FALSE
BY SMT

LEMMA TimerDeadlineContradiction ==
  ASSUME NEW deadline \in Int, NEW current \in Nat,
         NEW sentAt \in Nat, NEW delay \in Nat,
         deadline > sentAt + delay,
         current >= deadline,
         current <= sentAt + delay
  PROVE  FALSE
BY SMT

LEMMA NatGeGtTransitive ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat,
         a >= b, b > c
  PROVE  a > c
BY SMT

LEMMA FreshGapContradiction ==
  ASSUME NEW sentAt \in Nat, NEW current \in Nat,
         NEW entry \in Nat, NEW timeout \in Nat, NEW delay \in Nat,
         sentAt = current,
         sentAt + timeout <= entry + delay,
         entry <= current,
         timeout > 2 * delay
  PROVE  FALSE
BY SMT

LEMMA NatDelayNonnegative ==
  ASSUME NEW a \in Nat, NEW delay \in Nat
  PROVE  a <= a + delay
BY SMT

LEMMA NatSuccessorDistinct ==
  ASSUME NEW a \in Nat
  PROVE  a + 1 # a
BY SMT

LEMMA TickFromClockAdvance ==
  ASSUME TypeOK, [Next]_vars, now' = now + 1
  PROVE  Tick
<1>neq. now' # now
  BY NatSuccessorDistinct DEF TypeOK
<1> QED
  BY <1>neq, NowStaysUnlessTick, Zenon

-----------------------------------------------------------------------------
\* A precommit timer armed at the high lock round expires strictly after the
\* lock's delivery deadline. The arming quorum contains a correct precommit
\* at the same round. LateLockDelivery compares the lock timestamp with that
\* correct member's timestamp, and the precommit timeout contributes the
\* second delivery delay.
LEMMA HighLockPrecommitTimerGap ==
  ASSUME TypeOK, SentTimeLeNow, PrecommitArmedQuorumTimed,
         PrecommitRoundLeSendTime, LateLockDelivery,
         TimeoutsSufficientBeyond,
         NEW c \in Honest, NEW x \in Honest,
         NEW rr \in Rounds, NEW w \in Values,
         Precommit(x, rr, w) \in sent,
         rr > DomCeiling,
         round[c] = rr, timer[c]["precommit"] # OFF
  PROVE  timer[c]["precommit"]
           > sentTime[Precommit(x, rr, w)] + Delta
<1>1. PICK Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
          /\ Precommit(s, rr, v) \in sent
          /\ sentTime[Precommit(s, rr, v)]
               <= timer[c]["precommit"] - TimeoutPrecommit(rr)
    BY DEF PrecommitArmedQuorumTimed
<1>2. PICK y \in Q : y \in Honest
  BY <1>1, ByzHasHonest
<1>3. PICK v \in ValuesOrNil :
          /\ Precommit(y, rr, v) \in sent
          /\ sentTime[Precommit(y, rr, v)]
               <= timer[c]["precommit"] - TimeoutPrecommit(rr)
  BY <1>1, <1>2
<1>hi. rr > GST /\ rr >= 2 * Delta /\ ~(rr < GST)
  BY HighRoundFacts
<1>rt. rr \in Nat
  BY DEF Rounds
<1>4. rr <= sentTime[Precommit(y, rr, v)]
  BY <1>2, <1>3 DEF PrecommitRoundLeSendTime
<1>my. Precommit(y, rr, v) \in Message
  BY <1>2 DEFS Honest, Message, Precommit, PrecommitMsg
<1>4t. sentTime[Precommit(y, rr, v)] \in Nat
  BY <1>3, <1>my DEFS OFF, sent, TypeOK
<1>5. sentTime[Precommit(y, rr, v)] >= GST
  BY ONLY <1>4, <1>4t, <1>hi, <1>rt, GSTType, NatOrderAbove
<1>6. sentTime[Precommit(x, rr, w)]
          <= sentTime[Precommit(y, rr, v)] + Delta
  BY <1>2, <1>3, <1>5, HighRoundFacts DEF LateLockDelivery
<1>7. TimeoutPrecommit(rr) > 2 * Delta
  BY HighRoundPrecommitTimeout
<1>mx. Precommit(x, rr, w) \in Message
  BY DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
<1>tx. sentTime[Precommit(x, rr, w)] \in Nat
  BY <1>mx DEFS OFF, sent, TypeOK
<1>tc. timer[c]["precommit"] \in Int
  BY DEFS TimerType, TypeOK
<1>to. TimeoutPrecommit(rr) \in Nat
  BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit
<1> QED
  BY ONLY <1>3, <1>4t, <1>6, <1>7, <1>tx, <1>tc, <1>to, DeltaType,
     PrecommitTimerGapArithmetic

-----------------------------------------------------------------------------
\* Once the high lock evidence's delivery deadline is reached, every possible
\* state of an undecided process below its valid round enables computation.
LEMMA LateUpdateEnabled ==
  ASSUME TypeOK, GossipDeadline,
         NEW c \in Honest, NEW rr \in Rounds, NEW w \in Values,
         NEW T \in Int, T >= GST, Justified(rr, w, T),
         PolkaDated(rr, w, T), Valid(w), now >= T + Delta,
         round[c] = rr, step[c] \in {"precommit", "decided"},
         valid[c].round < rr
  PROVE  CanCompute(c)
<1>1. PICK prop \in RProposalsFromProposerAt(c, rr) : prop.value = w
  BY JustifiedDelivered
<1>2. RExistsPrevoteQuorum(c, w, rr)
  BY PolkaDeliveredSenders DEF ValuesOrNil
<1> QED
  BY <1>1, <1>2 DEF CanCompute

LEMMA LockEvidenceComputable ==
  ASSUME TypeOK, TypeOK', GossipDeadline, PrecommitBacked, PrevoteJustified,
         PrecommitRoundLeSendTime, DecidedStepOp,
         NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
         NEW c \in Honest,
         Precommit(x, rr, w) \in sent, rr > DomCeiling,
         valid[c].round < rr, ~HasDecided(c), round[c] <= rr,
         now >= sentTime[Precommit(x, rr, w)] + Delta
  PROVE  CanCompute(c)
<1>w. w \in ValuesOrNil
  BY DEF ValuesOrNil
<1>ty. /\ sentTime[Precommit(x, rr, w)] \in Nat
        /\ sentTime[Precommit(x, rr, w)] >= GST
  <2>1. rr <= sentTime[Precommit(x, rr, w)]
    BY <1>w DEF PrecommitRoundLeSendTime
  <2>2. Precommit(x, rr, w) \in Message
    BY <1>w DEFS Honest, Message, Precommit, PrecommitMsg
  <2>3. sentTime[Precommit(x, rr, w)] \in Nat
    BY <2>2 DEFS OFF, sent, TypeOK
  <2>4. rr > GST
    BY HighRoundFacts
  <2>5. rr \in Nat
    BY DEF Rounds
  <2> QED
    BY ONLY <2>1, <2>3, <2>4, <2>5, GSTType, NatOrderAbove
<1>1. Backing(rr, w, sentTime[Precommit(x, rr, w)])
  <2>1. sentTime[Precommit(x, rr, w)]
          <= sentTime[Precommit(x, rr, w)]
    BY <1>ty
  <2> QED
    BY <1>w, <1>ty, <2>1 DEF PrecommitBacked
<1>2. Valid(w)
       /\ PolkaDated(rr, w, sentTime[Precommit(x, rr, w)])
  BY <1>1, NilNotInValues DEF Backing
<1>3. Justified(rr, w, sentTime[Precommit(x, rr, w)])
  BY <1>2, <1>ty, JustifiedFromPolka
<1>4. AnyPrevoteDated(rr, sentTime[Precommit(x, rr, w)])
  BY <1>2, PolkaIsAnyPrevote DEF ValuesOrNil
<1>st. step[c] # "decided"
  BY DEF DecidedStepOp, HasDecided
<1>a. CASE round[c] < rr
  BY <1>3, <1>4, <1>st, <1>ty, <1>a, SkipEnabledFromQuorum
<1>b. CASE round[c] = rr /\ step[c] = "propose"
  BY <1>3, <1>ty, <1>b, ProposeExitEnabled
<1>c. CASE round[c] = rr /\ step[c] = "prevote"
  BY <1>2, <1>3, <1>ty, <1>c, ValuePrecommitEnabled
<1>d. CASE round[c] = rr /\ step[c] \in {"precommit", "decided"}
  BY <1>2, <1>3, <1>ty, <1>d, LateUpdateEnabled
<1>r. round[c] \in Nat /\ rr \in Nat
  BY DEFS Rounds, TypeOK
<1>s. step[c] \in Step
  BY DEF TypeOK
<1> QED
  BY <1>a, <1>b, <1>c, <1>d, <1>r, <1>s DEF Step

-----------------------------------------------------------------------------
\* The old-message round bound. SkipRound would require an honest sender
\* already above rr. OnTimeoutPrecommit at rr would require the timer to have
\* expired, after the catch-up deadline.
LEMMA OldCatchUpRoundBound ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, SentTimeLeNow,
         PrecommitArmedQuorumTimed, PrecommitRoundLeSendTime,
         LateLockDelivery, TimeoutsSufficientBeyond, [Next]_vars,
         ValidCatchUp,
         NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
         Precommit(x, rr, w) \in sent, rr > DomCeiling,
         \E c \in Honest : valid[c].round < rr /\ ~HasDecided(c)
  PROVE  \A c \in Honest : round'[c] <= rr
<1>ih. \A c \in Honest : round[c] <= rr
  BY DEF ValidCatchUp
<1>pc. Precommit(x, rr, w) \in sent
  OBVIOUS
<1>high. rr > DomCeiling
  OBVIOUS
<1> SUFFICES ASSUME NEW c \in Honest PROVE round'[c] <= rr
  OBVIOUS
<1>r. \/ (round' = round /\ enteredAt' = enteredAt)
       \/ \E q \in Honest : \E r2 \in Rounds :
            /\ round' = [round EXCEPT ![q] = r2]
            /\ enteredAt' = [enteredAt EXCEPT ![q][r2] = now]
            /\ ((OnTimeoutPrecommit(q) /\ r2 = round[q] + 1)
                  \/ SkipRound(q, r2))
  BY RoundEnteredStep
<1>1. CASE round'[c] = round[c]
  BY <1>ih, <1>1
<1>2. CASE round'[c] # round[c]
  <2>1. PICK q \in Honest, r2 \in Rounds :
          /\ round' = [round EXCEPT ![q] = r2]
          /\ enteredAt' = [enteredAt EXCEPT ![q][r2] = now]
          /\ ((OnTimeoutPrecommit(q) /\ r2 = round[q] + 1)
                \/ SkipRound(q, r2))
    BY <1>r, <1>2
  <2>2. q = c /\ round'[c] = r2
    BY <1>2, <2>1 DEFS Rounds, TypeOK
  <2>a. CASE OnTimeoutPrecommit(q) /\ r2 = round[q] + 1
    <3>ty. /\ r2 \in Nat /\ rr \in Nat /\ round[q] \in Nat
      BY DEFS Rounds, TypeOK
    <3>ord. r2 <= rr \/ r2 > rr
      BY ONLY <3>ty, NatLinearOrder
    <3>lo. CASE r2 <= rr
      BY <2>2, <3>lo
    <3>hi. CASE r2 > rr
      <4>1. round[q] <= rr
        BY <1>ih
      <4>2. r2 = round[q] + 1
        BY <2>a
      <4>3. round[q] = rr
        BY ONLY <3>ty, <3>hi, <4>1, <4>2, NatSuccessorAtCeiling
      <4>arm. timer[q]["precommit"] # OFF
        BY <2>a DEF OnTimeoutPrecommit
      <4>4. timer[q]["precommit"]
              > sentTime[Precommit(x, rr, w)] + Delta
        BY ONLY TypeOK, SentTimeLeNow, PrecommitArmedQuorumTimed,
          PrecommitRoundLeSendTime, LateLockDelivery,
          TimeoutsSufficientBeyond, <1>pc, <1>high, <4>3, <4>arm,
          HighLockPrecommitTimerGap
      <4>5. now >= timer[q]["precommit"]
        BY <2>a DEF OnTimeoutPrecommit
      <4>6. now <= sentTime[Precommit(x, rr, w)] + Delta
        BY DEF ValidCatchUp
      <4>st. sentTime[Precommit(x, rr, w)] \in Nat
        BY <1>pc
        DEFS Honest, Message, OFF, Precommit, PrecommitMsg, sent, TypeOK,
          ValuesOrNil
      <4>tt. timer[q]["precommit"] \in Int
        BY DEFS TimerType, TypeOK
      <4>nt. now \in Nat
        BY DEF TypeOK
      <4> QED
        BY ONLY <4>4, <4>5, <4>6, <4>st, <4>tt, <4>nt, DeltaType,
          TimerDeadlineContradiction
    <3> QED
      BY <3>ord, <3>lo, <3>hi
  <2>b. CASE SkipRound(q, r2)
    <3>1. PICK h \in Honest : r2 <= round[h]
      BY <2>b, SkipEvidenceHonestRound DEF SkipRound
    <3>2. round[h] <= rr
      BY <1>ih
    <3>ty. /\ r2 \in Nat /\ round[h] \in Nat /\ rr \in Nat
      BY DEFS Rounds, TypeOK
    <3> QED
      BY ONLY <2>2, <3>1, <3>2, <3>ty, NatLeTransitive
  <2> QED
    BY <2>1, <2>2, <2>a, <2>b
<1> QED
  BY <1>1, <1>2

\* A fresh high value precommit cannot coexist with a correct process above
\* its round. The retained timing gap would force that high round's timeout
\* into one delivery delay.
LEMMA FreshHighPrecommitFrontier ==
  ASSUME TypeOK, [Next]_vars, EntryTimeGeRound', EnteredAtLeNow',
         EnteredCurrentRound', LateValueLockGap',
         TimeoutsSufficientBeyond,
         NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
         Precommit(x, rr, w) \in sent',
         Precommit(x, rr, w) \notin sent, rr > DomCeiling
  PROVE  /\ \A c \in Honest : round'[c] <= rr
         /\ now' <= sentTime'[Precommit(x, rr, w)] + Delta
<1>msg. Precommit(x, rr, w) \in Message
  BY DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
<1>new. /\ Precommit(x, rr, w) \in sent'
         /\ Precommit(x, rr, w) \notin sent
  OBVIOUS
<1>a. /\ sentTime'[Precommit(x, rr, w)] = now
       /\ round[x] = rr
       /\ \/ OnPrevoteQuorumValueFirstTime(x)
          \/ OnPrevoteQuorumNil(x)
          \/ OnTimeoutPrevote(x)
  BY ONLY TypeOK, [Next]_vars, <1>msg, <1>new, FreshPrecommitAction
  DEF Precommit
<1>fr. /\ now' = now /\ round' = round /\ enteredAt' = enteredAt
  BY <1>a
  DEFS OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote
<1>high. rr > GST /\ ~(rr < GST)
  BY HighRoundFacts
<1>1. \A c \in Honest : round'[c] <= rr
  <2> SUFFICES ASSUME NEW c \in Honest PROVE round'[c] <= rr
    OBVIOUS
  <2>ty. round'[c] \in Nat /\ rr \in Nat
    BY <1>fr DEFS Rounds, TypeOK
  <2>rt. round'[c] \in Rounds
    BY <2>ty DEF Rounds
  <2>ord. round'[c] <= rr \/ round'[c] > rr
    BY ONLY <2>ty, NatLinearOrder
  <2>lo. CASE round'[c] <= rr
    BY <2>lo
  <2>hi. CASE round'[c] > rr
    <3>e. enteredAt'[c][round'[c]] # OFF
      BY ONLY EnteredCurrentRound' DEF EnteredCurrentRound
    <3>ge. enteredAt'[c][round'[c]] >= round'[c]
      BY ONLY EntryTimeGeRound', <2>rt, <3>e DEF EntryTimeGeRound
    <3>ety. enteredAt'[c][round'[c]] \in Nat
      BY <1>fr, <3>e DEFS OFF, Rounds, TypeOK
    <3>rg. round'[c] > GST
      BY ONLY <1>high, <2>hi, <2>ty, GSTType, NatGeGtTransitive
    <3>g. enteredAt'[c][round'[c]] > GST
      BY ONLY <2>ty, <3>ge, <3>ety, <3>rg, GSTType, NatGeGtTransitive
    <3>gap. \/ sentTime'[Precommit(x, rr, w)] + TimeoutPrecommit(rr)
                   <= enteredAt'[c][round'[c]] + Delta
              \/ rr < GST
      BY ONLY LateValueLockGap', <1>new, <2>hi, <2>rt, <3>e, <3>g
      DEF LateValueLockGap
    <3>1. sentTime'[Precommit(x, rr, w)] + TimeoutPrecommit(rr)
               <= enteredAt'[c][round'[c]] + Delta
      BY <1>high, <3>gap, Zenon
    <3>2. enteredAt'[c][round'[c]] <= now'
      BY ONLY EnteredAtLeNow', <2>rt, <3>e DEF EnteredAtLeNow
    <3>3. TimeoutPrecommit(rr) > 2 * Delta
      BY HighRoundPrecommitTimeout
    <3>eq. sentTime'[Precommit(x, rr, w)] = now'
      BY ONLY <1>a, <1>fr
    <3>to. TimeoutPrecommit(rr) \in Nat
      BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit
    <3>nt. now' \in Nat
      BY <1>fr DEF TypeOK
    <3> QED
      BY ONLY <3>1, <3>2, <3>3, <3>eq, <3>ety, <3>to, <3>nt,
        DeltaType, FreshGapContradiction
  <2> QED
    BY <2>ord, <2>lo, <2>hi
<1>2. now' <= sentTime'[Precommit(x, rr, w)] + Delta
  <2>eq. sentTime'[Precommit(x, rr, w)] = now'
    BY ONLY <1>a, <1>fr
  <2>ty. now' \in Nat
    BY <1>fr DEF TypeOK
  <2> QED
    BY ONLY <2>eq, <2>ty, DeltaType, NatDelayNonnegative
<1> QED
  BY <1>1, <1>2

LEMMA OldCatchUpDeadline ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv,
         GossipDeadline, PrecommitBacked, PrevoteJustified,
         PrecommitRoundLeSendTime, DecidedStepOp, [Next]_vars,
         ValidCatchUp, ValidBelowRound,
         NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
         Precommit(x, rr, w) \in sent, rr > DomCeiling,
         \E c \in Honest : valid'[c].round < rr /\ ~(HasDecided(c))'
  PROVE  now' <= sentTime'[Precommit(x, rr, w)] + Delta
<1>c. PICK c \in Honest : valid'[c].round < rr /\ ~(HasDecided(c))'
  OBVIOUS
<1>pc. Precommit(x, rr, w) \in sent
  OBVIOUS
<1>high. rr > DomCeiling
  OBVIOUS
<1>b. valid[c].round < rr /\ ~HasDecided(c)
  BY ONLY TypeOK, TypeOK', [Next]_vars, ValidBelowRound, <1>c,
    MissingValidBackStep
<1>ih. /\ \A e \in Honest : round[e] <= rr
        /\ now <= sentTime[Precommit(x, rr, w)] + Delta
  BY <1>b DEF ValidCatchUp
<1>fz. sentTime'[Precommit(x, rr, w)] =
         sentTime[Precommit(x, rr, w)]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY ONLY TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
      SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS OFF, sent, SentTimeFrozenPred, vars
<1>1. CASE now' = now
  BY <1>fz, <1>ih, <1>1
<1>2. CASE now' = now + 1
  <2>st. sentTime[Precommit(x, rr, w)] \in Nat
    BY <1>pc
    DEFS Honest, Message, OFF, Precommit, PrecommitMsg, sent, TypeOK,
      ValuesOrNil
  <2>bound. sentTime'[Precommit(x, rr, w)] + Delta \in Nat
    BY <1>fz, <2>st, DeltaType
  <2>ty. now' \in Nat /\ now \in Nat
    BY DEFS TypeOK
  <2>ord. now' <= sentTime'[Precommit(x, rr, w)] + Delta
             \/ now' > sentTime'[Precommit(x, rr, w)] + Delta
    BY ONLY <2>bound, <2>ty, NatLinearOrder
  <2>lo. CASE now' <= sentTime'[Precommit(x, rr, w)] + Delta
    BY <2>lo
  <2>hi. CASE now' > sentTime'[Precommit(x, rr, w)] + Delta
    <3>ihb. now <= sentTime'[Precommit(x, rr, w)] + Delta
      BY <1>fz, <1>ih
    <3>1. now = sentTime'[Precommit(x, rr, w)] + Delta
      BY ONLY <1>2, <2>bound, <2>hi, <2>ty, <3>ihb,
        NatSuccessorAtCeiling
    <3>2. CanCompute(c)
      <4>r. round[c] <= rr
        BY <1>ih
      <4>teq. now = sentTime[Precommit(x, rr, w)] + Delta
        BY <1>fz, <3>1, Zenon
      <4>tty. sentTime[Precommit(x, rr, w)] + Delta \in Nat
        BY <2>st, DeltaType
      <4>t. now >= sentTime[Precommit(x, rr, w)] + Delta
        BY ONLY <4>teq, <4>tty, NatLeReflexive
      <4> QED
        BY ONLY TypeOK, TypeOK', GossipDeadline, PrecommitBacked,
          PrevoteJustified, PrecommitRoundLeSendTime, DecidedStepOp,
          <1>pc, <1>high, <1>b, <4>r, <4>t,
          LockEvidenceComputable
    <3>3. Tick
      BY ONLY TypeOK, [Next]_vars, <1>2, TickFromClockAdvance
    <3> QED
      BY <3>2, <3>3, Zenon DEF Tick
  <2> QED
    BY <2>ord, <2>lo, <2>hi
<1> QED
  BY <1>1, <1>2, NowShape

-----------------------------------------------------------------------------
LEMMA ValidCatchUpStepL ==
  ASSUME TypeOK, TypeOK', RcvdSubsetSent, SentInv, SentTimeLeNow,
         GossipDeadline, PrecommitArmedQuorumTimed,
         PrecommitBacked, PrevoteJustified, PrecommitRoundLeSendTime,
         LateLockDelivery, DecidedStepOp, ValidBelowRound,
         EntryTimeGeRound', EnteredAtLeNow', EnteredCurrentRound',
         LateValueLockGap', TimeoutsSufficientBeyond,
         [Next]_vars, ValidCatchUp
  PROVE  ValidCatchUp'
<1> SUFFICES ASSUME NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
                    Precommit(x, rr, w) \in sent', rr > DomCeiling,
                    \E c \in Honest :
                      valid'[c].round < rr /\ ~(HasDecided(c))'
             PROVE  /\ \A c \in Honest : round'[c] <= rr
                    /\ now' <= sentTime'[Precommit(x, rr, w)] + Delta
  BY DEF ValidCatchUp
<1>1. CASE Precommit(x, rr, w) \notin sent
  BY <1>1, FreshHighPrecommitFrontier
<1>2. CASE Precommit(x, rr, w) \in sent
  <2>pc. Precommit(x, rr, w) \in sent
    BY <1>2
  <2>high. rr > DomCeiling
    OBVIOUS
  <2>b. \E c \in Honest : valid[c].round < rr /\ ~HasDecided(c)
    <3>1. PICK c \in Honest : valid'[c].round < rr /\ ~(HasDecided(c))'
      OBVIOUS
    <3> QED
      BY <3>1, MissingValidBackStep
  <2>1. \A c \in Honest : round'[c] <= rr
    BY ONLY TypeOK, TypeOK', RcvdSubsetSent, SentInv, SentTimeLeNow,
      PrecommitArmedQuorumTimed, PrecommitRoundLeSendTime,
      LateLockDelivery, TimeoutsSufficientBeyond, [Next]_vars,
      ValidCatchUp, <2>pc, <2>high, <2>b, OldCatchUpRoundBound
  <2>2. now' <= sentTime'[Precommit(x, rr, w)] + Delta
    BY <1>2, OldCatchUpDeadline
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2

\* Main inductive proof of paper Lemma 6.
THEOREM ValidCatchUpInv ==
  ASSUME Spec, TimeoutsSufficientBeyond
  PROVE  []ValidCatchUp
<1>1. ValidCatchUp
  BY DEFS Init, OFF, sent, Spec, ValidCatchUp
<1>ty. [](TypeOK /\ TypeOK')
  BY TypeOKBothStates DEF Spec
<1>entry. [](EntryTimeGeRound /\ EntryTimeGeRound')
  BY EntryTimeGeRoundInv, PTL
<1>entered. [](EnteredAtLeNow /\ EnteredAtLeNow')
  BY EnteredAtLeNowInv, PTL
<1>current. [](EnteredCurrentRound /\ EnteredCurrentRound')
  BY EnteredCurrentRoundInv, PTL
<1>gap. [](LateValueLockGap /\ LateValueLockGap')
  BY LateValueLockGapInv, PTL
<1>base. [](RcvdSubsetSent /\ SentInv /\ SentTimeLeNow)
  BY InvProof, SentInvInv, SentTimeLeNowInv, PTL DEF Spec, Inv
<1>messages. [](  GossipDeadline /\ PrecommitArmedQuorumTimed
                   /\ PrecommitBacked /\ PrevoteJustified  )
  BY GossipDeadlineInv, PrecommitArmedQuorumTimedInv, PrecommitBackedInv,
     PrevoteJustifiedInv, PTL
<1>pcRound. []PrecommitRoundLeSendTime
  BY PrecommitRoundLeSendTimeInv
<1>late. []LateLockDelivery
  BY LateLockDeliveryInv
<1>decided. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>validBelow. []ValidBelowRound
  BY ValidBelowRoundInv
<1>rounds. [](  PrecommitRoundLeSendTime /\ LateLockDelivery
                 /\ DecidedStepOp /\ ValidBelowRound  )
  BY <1>pcRound, <1>late, <1>decided, <1>validBelow, PTL
<1>nx. [][Next]_vars
  BY DEF Spec
<1>2. [](  TypeOK /\ TypeOK' /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ GossipDeadline /\ PrecommitArmedQuorumTimed
           /\ PrecommitBacked /\ PrevoteJustified
           /\ PrecommitRoundLeSendTime /\ LateLockDelivery
           /\ DecidedStepOp /\ ValidBelowRound
           /\ EntryTimeGeRound' /\ EnteredAtLeNow'
           /\ EnteredCurrentRound' /\ LateValueLockGap'
           /\ [Next]_vars  )
  BY <1>ty, <1>base, <1>messages, <1>rounds, <1>entry, <1>entered,
     <1>current, <1>gap, <1>nx, PTL
<1>3. [](ValidCatchUp => ValidCatchUp')
  BY <1>2, ValidCatchUpStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

LEMMA HighLockCatchUpFromValid ==
  ASSUME TypeOK, ValidCatchUp
  PROVE  HighLockCatchUp
<1> SUFFICES ASSUME NEW x \in Honest, NEW rr \in Rounds, NEW w \in Values,
                    Precommit(x, rr, w) \in sent, rr > DomCeiling,
                    now > sentTime[Precommit(x, rr, w)] + Delta
             PROVE  \A e \in Honest :
                      valid[e].round >= rr \/ HasDecided(e)
  BY DEF HighLockCatchUp
<1> SUFFICES ASSUME NEW e \in Honest,
                    ~(valid[e].round >= rr \/ HasDecided(e))
             PROVE  FALSE
  OBVIOUS
<1>pc. Precommit(x, rr, w) \in sent
  OBVIOUS
<1>late. now > sentTime[Precommit(x, rr, w)] + Delta
  OBVIOUS
<1>nge. ~(valid[e].round >= rr)
  BY Zenon
<1>nd. ~HasDecided(e)
  BY Zenon
<1>vty. valid[e].round \in Int
  BY DEFS LockState, Rounds, TypeOK
<1>rty. rr \in Int
  BY DEF Rounds
<1>lt. valid[e].round < rr
  BY ONLY <1>nge, <1>vty, <1>rty, IntNotGeLt
<1>m. valid[e].round < rr /\ ~HasDecided(e)
  BY <1>lt, <1>nd
<1>1. now <= sentTime[Precommit(x, rr, w)] + Delta
  BY <1>m DEF ValidCatchUp
<1>st. sentTime[Precommit(x, rr, w)] \in Nat
  BY <1>pc
  DEFS Honest, Message, OFF, Precommit, PrecommitMsg, sent, TypeOK,
    ValuesOrNil
<1>dty. sentTime[Precommit(x, rr, w)] + Delta \in Nat
  BY <1>st, DeltaType
<1>nty. now \in Nat
  BY DEF TypeOK
<1> QED
  BY ONLY <1>late, <1>1, <1>dty, <1>nty, NatGtLeContradiction

LEMMA BoxHighLockCatchUp ==
  [](TypeOK /\ ValidCatchUp => HighLockCatchUp)
<1>1. TypeOK /\ ValidCatchUp => HighLockCatchUp
  BY HighLockCatchUpFromValid
<1> QED
  BY <1>1, PTL

\* Exported paper Lemma 6 theorem used by the dominator proof.
THEOREM HighLockCatchUpInv ==
  ASSUME Spec, TimeoutsSufficientBeyond
  PROVE  []HighLockCatchUp
<1>1. []TypeOK
  BY InvProof DEF Spec, Inv
<1> QED
  BY <1>1, ValidCatchUpInv, BoxHighLockCatchUp, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)