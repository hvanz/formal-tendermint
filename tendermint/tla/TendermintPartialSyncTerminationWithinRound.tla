----------------- MODULE TendermintPartialSyncTerminationWithinRound -----------
(***************************************************************************)
(* Within-round safety support for the repaired paper Lemma 5 case         *)
(* split. The decide and evidence helpers are here, together with the      *)
(* outcome definitions that ...WithinRoundMC and the composition module    *)
(* resolve. TendermintPartialSyncTerminationCascade owns the quantitative     *)
(* cascade Lemma5OrBlockingLock, the proved corollary Lemma5OrPriorLock    *)
(* and the existential aggregation of that corollary.                      *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationBase

(***************************************************************************)
(* Phase 1 safety support for Lemma 5.                                     *)
(***************************************************************************)

\* Every honest process has a recorded entry for its current round. Every
\* recorded entry is for a round already reached and a time not in the future.
RoundEntryHistory ==
  /\ \A c \in Honest : enteredAt[c][round[c]] # OFF
  /\ \A c \in Honest : \A r \in Rounds :
       enteredAt[c][r] # OFF =>
         /\ r <= round[c]
         /\ enteredAt[c][r] <= now

LEMMA EntryUnchangedPreservesHistory ==
  ASSUME TypeOK, RoundEntryHistory,
         round' = round, enteredAt' = enteredAt, now <= now', now' \in Nat
  PROVE RoundEntryHistory'
<1>0. now <= now'
  OBVIOUS
<1>1. ASSUME NEW c \in Honest
      PROVE  enteredAt'[c][round'[c]] # OFF
  BY DEF RoundEntryHistory
<1>2. ASSUME NEW c \in Honest, NEW r \in Rounds
      PROVE  enteredAt'[c][r] # OFF =>
               /\ r <= round'[c]
               /\ enteredAt'[c][r] <= now'
  BY <1>0 DEFS OFF, RoundEntryHistory, TypeOK
<1> QED
  BY <1>1, <1>2 DEF RoundEntryHistory

EntryUnchangedFrame == UNCHANGED <<round, enteredAt, now>>

LEMMA EntryUnchangedFramePreservesHistory ==
  ASSUME TypeOK, RoundEntryHistory, EntryUnchangedFrame
  PROVE RoundEntryHistory'
BY EntryUnchangedPreservesHistory DEFS EntryUnchangedFrame, TypeOK

LEMMA EntryRaisePreservesHistory ==
  ASSUME TypeOK, RoundEntryHistory, NEW p \in Honest, NEW r2 \in Rounds,
         r2 > round[p],
         round' = [round EXCEPT ![p] = r2],
         enteredAt' = [enteredAt EXCEPT ![p][r2] = now], now' = now
  PROVE  RoundEntryHistory'
BY NowNotOff DEFS RoundEntryHistory, Rounds, TypeOK

LEMMA RoundEntryHistoryStep ==
  ASSUME TypeOK, [Next]_vars, RoundEntryHistory
  PROVE  RoundEntryHistory'
<1>0. TypeOK /\ RoundEntryHistory
  OBVIOUS
<1>1. CASE UNCHANGED vars
  <2>1. EntryUnchangedFrame
    BY <1>1 DEF vars, EntryUnchangedFrame
  <2> QED
    BY ONLY <1>0, <2>1, EntryUnchangedFramePreservesHistory
<1>2. CASE Next
  <2>1. CASE \E p \in Honest : HonestNext(p)
    <3> PICK p \in Honest : HonestNext(p)
      BY <2>1
    <3>1. CASE OnTimeoutPrecommit(p)
      BY <3>1, EntryRaisePreservesHistory DEFS OnTimeoutPrecommit, Rounds, TypeOK
    <3>2. CASE \E r2 \in Rounds : SkipRound(p, r2)
      BY <3>2, EntryRaisePreservesHistory DEF SkipRound
    <3>3. CASE Propose(p)
      <4>1. EntryUnchangedFrame
        BY <3>3 DEF Propose, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>4. CASE OnTimeoutPropose(p)
      <4>1. EntryUnchangedFrame
        BY <3>4 DEF OnTimeoutPropose, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>5. CASE OnProposalNoPOL(p)
      <4>1. EntryUnchangedFrame
        BY <3>5 DEF OnProposalNoPOL, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>6. CASE OnProposalWithPOL(p)
      <4>1. EntryUnchangedFrame
        BY <3>6 DEF OnProposalWithPOL, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>7. CASE ScheduleTimeoutPrevote(p)
      <4>1. EntryUnchangedFrame
        BY <3>7 DEF ScheduleTimeoutPrevote, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>8. CASE OnPrevoteQuorumValueFirstTime(p)
      <4>1. EntryUnchangedFrame
        BY <3>8 DEF OnPrevoteQuorumValueFirstTime, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>9. CASE OnPrevoteQuorumValueLateUpdate(p)
      <4>1. EntryUnchangedFrame
        BY <3>9 DEF OnPrevoteQuorumValueLateUpdate, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>10. CASE OnPrevoteQuorumNil(p)
      <4>1. EntryUnchangedFrame
        BY <3>10 DEF OnPrevoteQuorumNil, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>11. CASE OnTimeoutPrevote(p)
      <4>1. EntryUnchangedFrame
        BY <3>11 DEF OnTimeoutPrevote, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>12. CASE ScheduleTimeoutPrecommit(p)
      <4>1. EntryUnchangedFrame
        BY <3>12 DEF ScheduleTimeoutPrecommit, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>13. CASE OnPrecommitQuorumValue(p)
      <4>1. EntryUnchangedFrame
        BY <3>13 DEF OnPrecommitQuorumValue, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3>14. CASE Deliver(p)
      <4>1. EntryUnchangedFrame
        BY <3>14 DEF Deliver, EntryUnchangedFrame
      <4> QED
        BY ONLY <1>0, <4>1, EntryUnchangedFramePreservesHistory
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
         <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
      DEF HonestNext, HonestStep
  <2>2. CASE \E p \in Faulty : FaultyStep(p)
    <3>1. EntryUnchangedFrame
      BY <2>2 DEF FaultyStep, EntryUnchangedFrame
    <3> QED
      BY ONLY <1>0, <3>1, EntryUnchangedFramePreservesHistory
  <2>3. CASE Tick
    BY <2>3, EntryUnchangedPreservesHistory DEFS Tick, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, <1>2 DEF Next
<1> QED
  BY <1>1, <1>2

THEOREM RoundEntryHistoryInv == ASSUME Spec PROVE []RoundEntryHistory
<1>1. RoundEntryHistory
  BY DEF Init, RoundEntryHistory, Spec, Rounds, OFF
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](RoundEntryHistory => RoundEntryHistory')
  BY <1>2, RoundEntryHistoryStep, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* Stable form of the instant when p was first correct process to enter r.
EntriesAtOrAfter(r, t) ==
  \A c \in Honest : enteredAt[c][r] = OFF \/ enteredAt[c][r] >= t

RoundOrigin(p, r) ==
  /\ r > 0
  /\ enteredAt[p][r] # OFF
  /\ enteredAt[p][r] > GST
  /\ EntriesAtOrAfter(r, enteredAt[p][r])

LEMMA Lemma5HypImpliesRoundOrigin ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, Lemma5Hyp(p, r)
  PROVE  RoundOrigin(p, r)
<1>1. r > 0
  BY DEF Lemma5Hyp
<1>2. enteredAt[p][r] = now
  BY DEF Lemma5Hyp, FirstToEnter
<1>3. now \in Nat
  BY DEF TypeOK
<1>4. enteredAt[p][r] # OFF
  BY <1>2, <1>3 DEF OFF
<1>5. now > GST
  BY DEF Lemma5Hyp
<1>6. enteredAt[p][r] > GST
  BY <1>2, <1>5
<1>7. \A c \in Honest :
       enteredAt[c][r] = OFF \/ enteredAt[c][r] >= now
  BY DEF Lemma5Hyp, FirstToEnter
<1>8. EntriesAtOrAfter(r, enteredAt[p][r])
  BY <1>2, <1>7 DEF EntriesAtOrAfter
<1> QED
  BY <1>1, <1>4, <1>6, <1>8 DEF RoundOrigin

\* Entry slots are write once. A newly populated slot records the current
\* clock. RoundEntryHistory proves that a strictly higher round slot is fresh.
EntryUpdateDiscipline ==
  \A c \in Honest : \A r \in Rounds :
    /\ (enteredAt[c][r] # OFF => enteredAt'[c][r] = enteredAt[c][r])
    /\ (enteredAt[c][r] = OFF /\ enteredAt'[c][r] # OFF => enteredAt'[c][r] = now)

LEMMA EntryUnchangedDiscipline ==
  ASSUME enteredAt' = enteredAt
  PROVE  EntryUpdateDiscipline
BY DEF EntryUpdateDiscipline

LEMMA EntryRaiseDiscipline ==
  ASSUME TypeOK, RoundEntryHistory, NEW p \in Honest, NEW r2 \in Rounds,
         r2 > round[p], enteredAt' = [enteredAt EXCEPT ![p][r2] = now]
  PROVE  EntryUpdateDiscipline
<1> SUFFICES ASSUME NEW c \in Honest, NEW r \in Rounds
             PROVE  /\ (enteredAt[c][r] # OFF => enteredAt'[c][r] = enteredAt[c][r])
                    /\ (enteredAt[c][r] = OFF /\ enteredAt'[c][r] # OFF
                          => enteredAt'[c][r] = now)
  BY DEF EntryUpdateDiscipline
<1>0. r2 > round[p]
  OBVIOUS
<1>1. CASE c = p /\ r = r2
  <2>1. enteredAt[c][r] = OFF
    <3> SUFFICES ASSUME enteredAt[c][r] # OFF PROVE FALSE
      OBVIOUS
    <3>1. r <= round[c]
      BY DEF RoundEntryHistory
    <3>2. r2 <= round[p]
      BY <1>1, <3>1
    <3> QED
      BY <1>0, <3>2 DEF TypeOK, Rounds
  <2>2. enteredAt'[c][r] = now
    BY <1>1 DEF TypeOK
  <2> QED
    BY <2>1, <2>2
<1>2. CASE ~(c = p /\ r = r2)
  <2>1. enteredAt'[c][r] = enteredAt[c][r]
    BY <1>2 DEF TypeOK
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2

LEMMA EntryUpdateDisciplineStep ==
  ASSUME TypeOK, RoundEntryHistory, [Next]_vars
  PROVE  EntryUpdateDiscipline
<1>1. CASE UNCHANGED vars
  BY <1>1, EntryUnchangedDiscipline DEF vars
<1>2. CASE Next
  <2>1. CASE \E p \in Honest : HonestNext(p)
    <3> PICK p \in Honest : HonestNext(p)
      BY <2>1
    <3>1. CASE OnTimeoutPrecommit(p)
      <4>1. round[p] + 1 \in Rounds /\ round[p] + 1 > round[p]
        BY DEF TypeOK, Rounds
      <4>2. enteredAt' = [enteredAt EXCEPT ![p][round[p] + 1] = now]
        BY <3>1 DEF OnTimeoutPrecommit
      <4> QED
        BY <4>1, <4>2, EntryRaiseDiscipline
    <3>2. CASE \E r2 \in Rounds : SkipRound(p, r2)
      <4> PICK r2 \in Rounds : SkipRound(p, r2)
        BY <3>2
      <4>1. r2 > round[p] /\ enteredAt' = [enteredAt EXCEPT ![p][r2] = now]
        BY DEF SkipRound
      <4> QED
        BY <4>1, EntryRaiseDiscipline
    <3>3. CASE Propose(p)
      BY <3>3, EntryUnchangedDiscipline DEF Propose
    <3>4. CASE OnTimeoutPropose(p)
      BY <3>4, EntryUnchangedDiscipline DEF OnTimeoutPropose
    <3>5. CASE OnProposalNoPOL(p)
      BY <3>5, EntryUnchangedDiscipline DEF OnProposalNoPOL
    <3>6. CASE OnProposalWithPOL(p)
      BY <3>6, EntryUnchangedDiscipline DEF OnProposalWithPOL
    <3>7. CASE ScheduleTimeoutPrevote(p)
      BY <3>7, EntryUnchangedDiscipline DEF ScheduleTimeoutPrevote
    <3>8. CASE OnPrevoteQuorumValueFirstTime(p)
      BY <3>8, EntryUnchangedDiscipline DEF OnPrevoteQuorumValueFirstTime
    <3>9. CASE OnPrevoteQuorumValueLateUpdate(p)
      BY <3>9, EntryUnchangedDiscipline DEF OnPrevoteQuorumValueLateUpdate
    <3>10. CASE OnPrevoteQuorumNil(p)
      BY <3>10, EntryUnchangedDiscipline DEF OnPrevoteQuorumNil
    <3>11. CASE OnTimeoutPrevote(p)
      BY <3>11, EntryUnchangedDiscipline DEF OnTimeoutPrevote
    <3>12. CASE ScheduleTimeoutPrecommit(p)
      BY <3>12, EntryUnchangedDiscipline DEF ScheduleTimeoutPrecommit
    <3>13. CASE OnPrecommitQuorumValue(p)
      BY <3>13, EntryUnchangedDiscipline DEF OnPrecommitQuorumValue
    <3>14. CASE Deliver(p)
      BY <3>14, EntryUnchangedDiscipline DEF Deliver
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
         <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
         DEF HonestNext, HonestStep
  <2>2. CASE \E p \in Faulty : FaultyStep(p)
    BY <2>2, EntryUnchangedDiscipline DEF FaultyStep
  <2>3. CASE Tick
    BY <2>3, EntryUnchangedDiscipline DEF Tick
  <2> QED
    BY <2>1, <2>2, <2>3, <1>2 DEF Next
<1> QED
  BY <1>1, <1>2

LEMMA EnteredAtFrozenStep ==
  ASSUME TypeOK, RoundEntryHistory, [Next]_vars,
         NEW c \in Honest, NEW r \in Rounds, enteredAt[c][r] # OFF
  PROVE  enteredAt'[c][r] = enteredAt[c][r]
BY EntryUpdateDisciplineStep DEF EntryUpdateDiscipline

LEMMA EntriesAtOrAfterStep ==
  ASSUME TypeOK, RoundEntryHistory, [Next]_vars,
         NEW r \in Rounds, NEW t \in Nat,
         t <= now, EntriesAtOrAfter(r, t)
  PROVE  EntriesAtOrAfter(r, t)'
BY EntryUpdateDisciplineStep DEFS EntriesAtOrAfter, EntryUpdateDiscipline

LEMMA RoundOriginStep ==
  ASSUME TypeOK, RoundEntryHistory, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds, RoundOrigin(p, r)
  PROVE  RoundOrigin(p, r)'
BY EnteredAtFrozenStep, EntriesAtOrAfterStep DEFS OFF, RoundEntryHistory, RoundOrigin, TypeOK

THEOREM RoundOriginStable ==
    ASSUME Spec
    PROVE  \A p \in Honest : \A r \in Rounds :
            [](RoundOrigin(p, r) => []RoundOrigin(p, r))
<1>1. [](TypeOK /\ RoundEntryHistory /\ [Next]_vars)
  BY InvProof, RoundEntryHistoryInv, PTL DEF Spec, Inv
<1>2. TAKE p \in Honest
<1>3. TAKE r \in Rounds
<1>4. [](RoundOrigin(p, r) => RoundOrigin(p, r)')
  BY <1>1, RoundOriginStep, PTL
<1> QED
  BY <1>4, PTL

\*  Paper Lemma 7 has two cases before the round of the selected proposer. In
\*  the first case no correct process locks after GST, and Lemma 5 applies. In
\*  the second case Lemma 6 propagates the latest such lock. The published
\*  proof of Lemma 5 omits one lock. That lock occurs after the first correct
\*  entry into r, while another correct process is still below r. The lock
\*  case of Lemma 7 is therefore recorded here explicitly.
PostGSTPriorRoundLock(r) ==
  \E w \in Values, c \in Honest, lr \in Rounds :
    /\ lr < r
    /\ VotedPrecommit(c, w, lr)
    /\ sentTime[Precommit(c, lr, w)] > GST

LEMMA PostGSTPriorRoundLockStep ==
  ASSUME TypeOK, [Next]_vars,
         [SentTimeFrozenPred]_vars,
         NEW r \in Rounds,
         PostGSTPriorRoundLock(r)
  PROVE  PostGSTPriorRoundLock(r)'
<1>1. PICK w \in Values, c \in Honest, lr \in Rounds :
        /\ lr < r
        /\ VotedPrecommit(c, w, lr)
        /\ sentTime[Precommit(c, lr, w)] > GST
  BY DEF PostGSTPriorRoundLock
<1>m. Precommit(c, lr, w) \in Message
  BY <1>1 DEF VotedPrecommit, sent
<1>sent. Precommit(c, lr, w) \in sent'
  BY <1>1, SentMonotoneStep DEF VotedPrecommit
<1>time. sentTime'[Precommit(c, lr, w)] = sentTime[Precommit(c, lr, w)]
  BY <1>1, <1>m DEF SentTimeFrozenPred, VotedPrecommit, sent, vars
<1> QED
  BY <1>1, <1>sent, <1>time DEF PostGSTPriorRoundLock, VotedPrecommit

THEOREM PostGSTPriorRoundLockStable ==
  ASSUME Spec
  PROVE  \A r \in Rounds :
            [](PostGSTPriorRoundLock(r) => []PostGSTPriorRoundLock(r))
<1>1. [](TypeOK /\ [Next]_vars /\ [SentTimeFrozenPred]_vars)
  BY InvProof, SentTimeFrozenInv, PTL DEF Spec, Inv
<1>2. TAKE r \in Rounds
<1>3. [](PostGSTPriorRoundLock(r) => PostGSTPriorRoundLock(r)')
  BY <1>1, PostGSTPriorRoundLockStep, PTL
<1> QED
  BY <1>3, PTL

\*  The SAME lock case of Lemma 7, relativized to round r. It is a stale
\*  blocking lock that formed DURING round r. A correct process c locked a
\*  value w at a round lr. The value w is different from the proposed value v.
\*  The round lr is strictly below r. It is also strictly above the round vr
\*  of the proof of lock that the proposal of round r carries. The lock
\*  happened no earlier than the instant when p entered r.
\*
\*  PostGSTPriorRoundLock above is anchored to the CONSTANT GST, so it can
\*  only latch. One correct lock after GST makes it true at the hypothesis
\*  state of every later round. A retry then re-derives a fact that it already
\*  had. To anchor the same event to the entry instant enteredAt[p][r] re-arms
\*  it, because a later round has a later, frozen entry time. That one
\*  substitution is what makes a retry argument possible. The lock-relativize
\*  scenario of ...WithinRoundMC checks it. The lock of round 0 satisfies
\*  PostGSTPriorRoundLock(2), and it satisfies every conjunct here except the
\*  timestamp.
\*
\* No rigid parameter is necessary. Every conjunct is a latch, because `sent`
\* only grows, `sentTime` is frozen, and `enteredAt` is write once. The
\* round-r proposal in `sent` pins the reference record (v, vr), because
\* Propose forbids a second proposal from a correct proposer at the same
\* round. The event is therefore a plain state predicate over the parameters
\* of the theorem itself.
\*
\* The timestamp conjunct is `>=`, and NOT `>`. The maximal-progress guard of
\* Tick stops the clock from advancing while any correct process can act. A
\* disruptive lock, and the round entry that it disrupts, are therefore at the
\* SAME clock instant. The recorded counterexample run does exactly that, with
\* both at now = 3 in the phase2-lock-shift scenario of ...WithinRoundMC. A
\* strict `>` would therefore make Lemma5OrBlockingLock below FALSE there.
BlockingLockDuring(p, r) ==
  \E v \in Values, w \in Values, vr \in Rounds \cup {-1},
     c \in Honest, lr \in Rounds :
    /\ Proposal(Proposer[r], r, v, vr) \in sent
    /\ vr < lr
    /\ lr < r
    /\ w # v
    /\ VotedPrecommit(c, w, lr)
    /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]

\* Minimal existing control support needed by the later stage proofs.
Lemma5ControlSafety ==
  /\ ProposeTimerArmedOp
  /\ DecidedStepOp
  /\ SelfVoteEvidenceOp

THEOREM Lemma5ControlSafetyInv == Spec => []Lemma5ControlSafety
<1> SUFFICES ASSUME Spec PROVE []Lemma5ControlSafety
  OBVIOUS
<1>1. []ProposeTimerArmedOp
  BY ProposeTimerArmedInv, ProposeTimerArmedBox, PTL
<1>2. []DecidedStepOp
  BY DecidedStepInv, DecidedStepBox, PTL
<1>3. []SelfVoteEvidenceOp
  BY SelfVoteEvidenceInv
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF Lemma5ControlSafety

\* Phase 2 needs precommit timers and nonempty valid records backed by the
\* message evidence that armed or established them. Both facts are
\* recoverable from existing state because rcvd only grows.
LEMMA RcvdMonotoneAt ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest
  PROVE  rcvd[c] \subseteq rcvd'[c]
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
    OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
    OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose,
    Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

LEMMA AnyPrecommitQuorumMonotone ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW r \in Rounds,
         RExistsAnyPrecommitQuorum(c, r)
  PROVE  RExistsAnyPrecommitQuorum(c, r)'
BY RcvdMonotoneAt DEFS RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound

LEMMA PrevoteQuorumMonotone ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest,
         NEW v \in ValuesOrNil, NEW r \in Rounds,
         RExistsPrevoteQuorum(c, v, r)
  PROVE  RExistsPrevoteQuorum(c, v, r)'
BY RcvdMonotoneAt DEFS RExistsPrevoteQuorum, RPrevotes, RPrevoteSendersFor

PrecommitTimerBacked ==
  \A c \in Honest :
    timer[c]["precommit"] # OFF =>
      RExistsAnyPrecommitQuorum(c, round[c])

LEMMA PrecommitTimerBackedStep ==
  ASSUME TypeOK, [Next]_vars, PrecommitTimerBacked
  PROVE  PrecommitTimerBacked'
<1> USE DEF PrecommitTimerBacked
<1> SUFFICES ASSUME NEW c \in Honest, timer'[c]["precommit"] # OFF
             PROVE (RExistsAnyPrecommitQuorum(c, round[c]))'
  OBVIOUS
<1>ih. timer[c]["precommit"] # OFF =>
          RExistsAnyPrecommitQuorum(c, round[c])
  OBVIOUS
<1> USE DEFS RExistsAnyPrecommitQuorum, RPrecommits, RSendersOfTypeAtRound
<1>1. CASE \E q \in Honest : HonestStep(q)
  BY <1>1, <1>ih DEFS Broadcast, HonestStep, OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
    OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
    OnTimeoutPropose, Propose, ResetTimersFor, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TimerType, TypeOK
<1>2. CASE \E q \in Honest : Deliver(q)
  BY <1>2, <1>ih DEFS Deliver, TypeOK
<1>3. CASE \E q \in Faulty : FaultyStep(q)
  <2>1. UNCHANGED << round, timer >>
    BY <1>3 DEF FaultyStep
  <2>2. timer[c]["precommit"] # OFF
    BY <2>1
  <2>3. RExistsAnyPrecommitQuorum(c, round[c])
    BY <1>ih, <2>2
  <2>4. rcvd[c] \subseteq rcvd'[c]
    BY RcvdMonotoneAt
  <2>5. RSendersOfTypeAtRound(c, "Precommit", round[c])
          \subseteq (RSendersOfTypeAtRound(c, "Precommit", round[c]))'
    BY <2>1, <2>4 DEF RSendersOfTypeAtRound
  <2>6. (RExistsAnyPrecommitQuorum(c, round[c]))'
    BY <2>3, <2>5 DEF RExistsAnyPrecommitQuorum
  <2> QED
    BY <2>1, <2>6
<1>4. CASE Tick
  BY <1>4, <1>ih DEFS Tick
<1>5. CASE UNCHANGED vars
  BY <1>5 DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, HonestNext

THEOREM PrecommitTimerBackedInv == ASSUME Spec PROVE []PrecommitTimerBacked
<1>1. PrecommitTimerBacked
  BY DEF Init, Spec, PrecommitTimerBacked, OFF, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](PrecommitTimerBacked => PrecommitTimerBacked')
  BY <1>2, PrecommitTimerBackedStep, PTL
<1> QED
  BY <1>1, <1>3, PTL

ValidPrevoteBacked ==
  \A c \in Honest :
    valid[c].round >= 0 =>
      /\ Valid(valid[c].value)
      /\ RExistsPrevoteQuorum(c, valid[c].value, valid[c].round)

LEMMA ValidPrevoteBackedStep ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, ValidPrevoteBacked
  PROVE  ValidPrevoteBacked'
<1> SUFFICES ASSUME NEW c \in Honest, valid'[c].round >= 0
             PROVE /\ Valid(valid'[c].value)
                   /\ (RExistsPrevoteQuorum(c, valid[c].value, valid[c].round))'
  BY DEF ValidPrevoteBacked
<1>1. CASE OnPrevoteQuorumValueFirstTime(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
       /\ RExistsPrevoteQuorum(c, prop.value, round[c])
       /\ Valid(prop.value)
       /\ valid' = [valid EXCEPT
            ![c] = [value |-> prop.value, round |-> round[c]]]
       /\ rcvd' = [rcvd EXCEPT
            ![c] = rcvd[c] \cup {Precommit(c, round[c], prop.value)}]
    BY <1>1 DEF OnPrevoteQuorumValueFirstTime, Broadcast
  <2>2. /\ valid'[c].value = prop.value
         /\ valid'[c].round = round[c]
         /\ rcvd[c] \subseteq rcvd'[c]
    BY <2>1, <1>1 DEF TypeOK
  <2> QED
    BY <2>1, <2>2 DEF RExistsPrevoteQuorum,
                       RPrevoteSendersFor, RPrevotes
<1>2. CASE OnPrevoteQuorumValueLateUpdate(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
       /\ RExistsPrevoteQuorum(c, prop.value, round[c])
       /\ Valid(prop.value)
       /\ valid' = [valid EXCEPT
            ![c] = [value |-> prop.value, round |-> round[c]]]
    BY <1>2 DEF OnPrevoteQuorumValueLateUpdate
  <2>2. valid'[c].value = prop.value /\ valid'[c].round = round[c]
    BY <2>1 DEF TypeOK
  <2>3. rcvd' = rcvd
    BY <1>2 DEF OnPrevoteQuorumValueLateUpdate
  <2> QED
    BY <2>1, <2>2, <2>3 DEF RExistsPrevoteQuorum, RPrevoteSendersFor, RPrevotes
<1>3. CASE ~OnPrevoteQuorumValueFirstTime(c)
           /\ ~OnPrevoteQuorumValueLateUpdate(c)
  <2>1. valid'[c] = valid[c]
    BY <1>3 DEF Next, HonestNext, HonestStep, Broadcast, Deliver,
       Propose, OnTimeoutPropose, OnProposalNoPOL, OnProposalWithPOL,
       ScheduleTimeoutPrevote, OnPrevoteQuorumValueFirstTime,
       OnPrevoteQuorumValueLateUpdate, OnPrevoteQuorumNil,
       OnTimeoutPrevote, ScheduleTimeoutPrecommit,
       OnPrecommitQuorumValue, OnTimeoutPrecommit, SkipRound,
       FaultyStep, Tick, TypeOK, vars
  <2>2. /\ Valid(valid[c].value)
        /\ RExistsPrevoteQuorum(c, valid[c].value, valid[c].round)
    BY <2>1, <1>3 DEF ValidPrevoteBacked
  <2>3. rcvd[c] \subseteq rcvd'[c]
    BY RcvdMonotoneAt
  <2>4. RPrevoteSendersFor(c, valid[c].value, valid[c].round)
          \subseteq RPrevoteSendersFor(c, valid[c].value, valid[c].round)'
    BY <2>1, <2>3 DEF RPrevoteSendersFor, RPrevotes
  <2> QED
    BY <2>1, <2>2, <2>4 DEF RExistsPrevoteQuorum
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM ValidPrevoteBackedInv == Spec => []ValidPrevoteBacked
<1> SUFFICES ASSUME Spec PROVE []ValidPrevoteBacked
  OBVIOUS
<1>1. ValidPrevoteBacked
  BY DEF Init, Spec, ValidPrevoteBacked
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ValidPrevoteBacked => ValidPrevoteBacked')
  BY <1>2, ValidPrevoteBackedStep, PTL
<1> QED
  BY <1>1, <1>3, PTL

EntryAdvanceEvidence(c, r) ==
  \/ RExistsAnyPrecommitQuorum(c, r - 1)
  \/ \E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(c, r)

RoundEntryEvidence ==
  \A c \in Honest : \A r \in Rounds :
    r > 0 /\ enteredAt[c][r] # OFF => EntryAdvanceEvidence(c, r)

LEMMA EntryAdvanceEvidenceMonotone ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW r \in Rounds,
         r > 0, EntryAdvanceEvidence(c, r)
  PROVE  EntryAdvanceEvidence(c, r)'
<1>1. rcvd[c] \subseteq rcvd'[c]
  BY RcvdMonotoneAt
<1>2. CASE RExistsAnyPrecommitQuorum(c, r - 1)
  BY <1>1, <1>2 DEF EntryAdvanceEvidence,
                       RExistsAnyPrecommitQuorum,
                       RSendersOfTypeAtRound, RPrecommits
<1>3. CASE \E W \in WeakQuorum :
             W \subseteq RSendersOfAnyMessageAt(c, r)
  BY <1>1, <1>3 DEF EntryAdvanceEvidence, RSendersOfAnyMessageAt,
                       RSendersOfTypeAtRound
<1> QED
  BY <1>2, <1>3 DEF EntryAdvanceEvidence

LEMMA NatSuccPred ==
  ASSUME NEW n \in Nat
  PROVE  (n + 1) - 1 = n
BY SMT

LEMMA RoundSuccPred ==
  ASSUME TypeOK, NEW c \in Honest
  PROVE  (round[c] + 1) - 1 = round[c]
<1>1. round[c] \in Nat
  BY DEF TypeOK, Rounds
<1> QED
  BY <1>1, NatSuccPred

LEMMA NewRoundEntryHasEvidence ==
  ASSUME TypeOK, RoundEntryHistory, PrecommitTimerBacked, [Next]_vars,
         NEW c \in Honest, NEW r \in Rounds, r > 0,
         enteredAt[c][r] = OFF, enteredAt'[c][r] # OFF
  PROVE  EntryAdvanceEvidence(c, r)'
<1>1. CASE \E q \in Honest : HonestStep(q)
  <2> PICK q \in Honest : HonestStep(q)
    BY <1>1
  <2>1. CASE q # c
    <3>1. enteredAt'[c] = enteredAt[c]
      BY <2>1 DEF HonestStep, Propose, OnTimeoutPropose,
         OnProposalNoPOL, OnProposalWithPOL, ScheduleTimeoutPrevote,
         OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
         OnPrevoteQuorumNil, OnTimeoutPrevote, ScheduleTimeoutPrecommit,
         OnPrecommitQuorumValue, OnTimeoutPrecommit, SkipRound, TypeOK
    <3> QED
      BY <3>1
  <2>2. CASE q = c
    <3>1. CASE OnTimeoutPrecommit(c)
      <4>1. /\ r = round[c] + 1
             /\ rcvd' = rcvd
             /\ timer[c]["precommit"] # OFF
        <5>1. enteredAt' =
              [enteredAt EXCEPT ![c][round[c] + 1] = now]
          BY <3>1 DEF OnTimeoutPrecommit
        <5>2. r = round[c] + 1
          BY <5>1 DEF TypeOK
        <5> QED
          BY <3>1, <5>2 DEF OnTimeoutPrecommit
      <4>2. RExistsAnyPrecommitQuorum(c, round[c])
        BY <4>1 DEF PrecommitTimerBacked
      <4>3. round[c] \in Rounds
        BY DEF TypeOK
      <4>4. (round[c] + 1) - 1 = round[c]
        BY RoundSuccPred
      <4>5. r - 1 = round[c]
        BY <4>1, <4>4
      <4>6. RExistsAnyPrecommitQuorum(c, r - 1)'
        BY <4>1, <4>2, <4>5 DEF RExistsAnyPrecommitQuorum,
                                   RSendersOfTypeAtRound, RPrecommits
      <4> QED
        BY <4>6 DEF EntryAdvanceEvidence
    <3>2. CASE \E r2 \in Rounds : SkipRound(c, r2)
      <4>0. PICK r2 \in Rounds : SkipRound(c, r2)
        BY <3>2
      <4>1. /\ r = r2
             /\ rcvd' = rcvd
             /\ \E W \in WeakQuorum :
                  W \subseteq RSendersOfAnyMessageAt(c, r2)
        <5>1. enteredAt' = [enteredAt EXCEPT ![c][r2] = now]
          BY <4>0 DEF SkipRound
        <5>2. r = r2
          BY <5>1 DEF TypeOK
        <5> QED
          BY <4>0, <5>2 DEF SkipRound
      <4> QED
        BY <4>1 DEF EntryAdvanceEvidence, RSendersOfAnyMessageAt,
                     RSendersOfTypeAtRound
    <3>3. CASE Propose(c) \/ OnTimeoutPropose(c) \/
                 OnProposalNoPOL(c) \/ OnProposalWithPOL(c) \/
                 ScheduleTimeoutPrevote(c) \/
                 OnPrevoteQuorumValueFirstTime(c) \/
                 OnPrevoteQuorumValueLateUpdate(c) \/
                 OnPrevoteQuorumNil(c) \/ OnTimeoutPrevote(c) \/
                 ScheduleTimeoutPrecommit(c) \/
                 OnPrecommitQuorumValue(c)
      <4>1. enteredAt' = enteredAt
        BY <3>3 DEF Propose, OnTimeoutPropose, OnProposalNoPOL,
           OnProposalWithPOL, ScheduleTimeoutPrevote,
           OnPrevoteQuorumValueFirstTime,
           OnPrevoteQuorumValueLateUpdate, OnPrevoteQuorumNil,
           OnTimeoutPrevote, ScheduleTimeoutPrecommit,
           OnPrecommitQuorumValue
      <4> QED
        BY <4>1
    <3> QED
      BY <2>2, <3>1, <3>2, <3>3 DEF HonestStep
  <2> QED
    BY <2>1, <2>2
<1>2. CASE \E q \in Honest : Deliver(q)
  BY <1>2 DEF Deliver
<1>3. CASE \E q \in Faulty : FaultyStep(q)
  BY <1>3 DEF FaultyStep
<1>4. CASE Tick
  BY <1>4 DEF Tick
<1>5. CASE UNCHANGED vars
  BY <1>5 DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, HonestNext

LEMMA RoundEntryEvidenceStep ==
  ASSUME TypeOK, RoundEntryHistory, PrecommitTimerBacked,
         RoundEntryEvidence, [Next]_vars
  PROVE  RoundEntryEvidence'
<1> SUFFICES ASSUME NEW c \in Honest, NEW r \in Rounds,
             r > 0, enteredAt'[c][r] # OFF
             PROVE EntryAdvanceEvidence(c, r)'
  BY DEF RoundEntryEvidence
<1>1. CASE enteredAt[c][r] # OFF
  <2>1. EntryAdvanceEvidence(c, r)
    BY <1>1 DEF RoundEntryEvidence
  <2> QED
    BY <2>1, EntryAdvanceEvidenceMonotone
<1>2. CASE enteredAt[c][r] = OFF
  BY <1>2, NewRoundEntryHasEvidence
<1> QED
  BY <1>1, <1>2

THEOREM RoundEntryEvidenceInv == Spec => []RoundEntryEvidence
<1> SUFFICES ASSUME Spec PROVE []RoundEntryEvidence
  OBVIOUS
<1>1. RoundEntryEvidence
  <2> SUFFICES ASSUME NEW c \in Honest, NEW r \in Rounds,
              r > 0, enteredAt[c][r] # OFF
              PROVE EntryAdvanceEvidence(c, r)
    BY DEF RoundEntryEvidence
  <2>1. r # 0
    BY DEF Rounds
  <2>2. enteredAt =
          [v \in Honest |-> [rr \in Rounds |->
            IF rr = 0 THEN 0 ELSE OFF]]
    BY DEF Spec, Init
  <2>3. enteredAt[c][r] = IF r = 0 THEN 0 ELSE OFF
    BY <2>2 DEF TypeOK
  <2>4. enteredAt[c][r] = OFF
    BY <2>1, <2>3
  <2> QED
    BY <2>4
<1>2. [](TypeOK /\ RoundEntryHistory /\ PrecommitTimerBacked /\
          [Next]_vars)
  BY InvProof, RoundEntryHistoryInv, PrecommitTimerBackedInv,
     PTL DEF Spec, Inv
<1>3. [](RoundEntryEvidence => RoundEntryEvidence')
  BY <1>2, RoundEntryEvidenceStep, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* A received proposal has a real value. Kept separate from ENABLED
\* expansion so the action proof remains first-order and small.
LEMMA RProposalValueType ==
  ASSUME TypeOK, RcvdSubsetSent,
         NEW c \in Honest, NEW r \in Rounds,
         NEW prop \in RProposalsFromProposerAt(c, r)
  PROVE  prop.value \in Values
BY DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, RcvdSubsetSent, RProposals, RProposalsFromProposerAt, sent

\* Moved here from ...Dominator: the cascade module needs this invariant, and
\* it cannot see ...Dominator. The proof cites RProposalValueType just above,
\* so ...Base is too high for it.
\* Every nonnegative correct lock has the matching value precommit in sent.
LockBackedByPrecommit ==
  \A c \in Honest :
    locked[c].round >= 0 =>
      /\ locked[c].value \in Values
      /\ Precommit(c, locked[c].round, locked[c].value) \in sent

LEMMA LockBackedByPrecommitStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, [Next]_vars,
         LockBackedByPrecommit
  PROVE  LockBackedByPrecommit'
<1> SUFFICES ASSUME NEW c \in Honest, locked'[c].round >= 0
             PROVE  /\ locked'[c].value \in Values
                    /\ Precommit(c, locked'[c].round, locked'[c].value)
                         \in sent'
  BY DEF LockBackedByPrecommit
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>fn. locked \in [Honest -> LockState]
  BY DEF TypeOK
<1>1. CASE \E p \in Honest : OnPrevoteQuorumValueFirstTime(p)
  <2>1. PICK p \in Honest : OnPrevoteQuorumValueFirstTime(p)
    BY <1>1
  <2>2. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
          /\ Valid(prop.value)
          /\ locked' =
               [locked EXCEPT ![p] =
                 [value |-> prop.value, round |-> round[p]]]
          /\ sentTime' =
               [sentTime EXCEPT ![Precommit(p, round[p], prop.value)] = now]
    BY <2>1 DEF Broadcast, OnPrevoteQuorumValueFirstTime
  <2>pr. p \in Validators /\ round[p] \in Rounds
    BY DEFS Honest, Rounds, TypeOK
  <2>v. prop.value \in Values
    BY ONLY TypeOK, RcvdSubsetSent, <2>2, <2>pr, RProposalValueType
  <2>msg. Precommit(p, round[p], prop.value) \in Message
    BY <2>v, <2>pr, MsgPrecommit DEF ValuesOrNil
  <2>sent. Precommit(p, round[p], prop.value) \in sent'
    BY <2>2, <2>msg
    DEFS OFF, sent, TypeOK
  <2>a. CASE p = c
    <3>rec. locked'[c] =
          [value |-> prop.value, round |-> round[p]]
      BY <2>2, <2>a, <1>fn
    <3> QED
      BY <3>rec, <2>a, <2>v, <2>sent
  <2>b. CASE p # c
    <3>keep. locked'[c] = locked[c]
      BY <2>2, <2>b, <1>fn
    <3>old. /\ locked[c].value \in Values
             /\ Precommit(c, locked[c].round, locked[c].value) \in sent
      BY <3>keep DEF LockBackedByPrecommit
    <3> QED
      BY <3>keep, <3>old, <1>mono
  <2> QED
    BY <2>a, <2>b
<1>2. CASE ~(\E p \in Honest : OnPrevoteQuorumValueFirstTime(p))
  <2>keep. locked' = locked
    BY <1>2
    DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next,
      OnPrecommitQuorumValue, OnPrevoteQuorumNil,
      OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
      OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
      ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
  <2>old. /\ locked[c].value \in Values
           /\ Precommit(c, locked[c].round, locked[c].value) \in sent
    BY <2>keep DEF LockBackedByPrecommit
  <2> QED
    BY <2>keep, <2>old, <1>mono
<1> QED
  BY <1>1, <1>2

THEOREM LockBackedByPrecommitInv ==
  ASSUME Spec PROVE []LockBackedByPrecommit
<1>1. LockBackedByPrecommit
  BY DEFS Init, LockBackedByPrecommit, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ [Next]_vars)
  BY InvProof, SentInvInv, PTL DEF Spec, Inv
<1>3. [](LockBackedByPrecommit => LockBackedByPrecommit')
  BY <1>2, LockBackedByPrecommitStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* With a received valid proposal and its precommit quorum, the decide action
\* is enabled. The action always changes decision[c], so the bracketed and
\* unbracketed actions are equivalent in this context.
DecideAt(c, r, prop) ==
  /\ decision[c] = nil
  /\ prop \in RProposalsFromProposerAt(c, r)
  /\ RExistsPrecommitQuorum(c, prop.value, r)
  /\ Valid(prop.value)
  /\ decision' = [decision EXCEPT ![c] = prop.value]
  /\ step' = [step EXCEPT ![c] = "decided"]
  /\ decidedRound' = [decidedRound EXCEPT ![c] = r]
  /\ UNCHANGED <<round, locked, valid, sentTime, rcvd, timer, now, enteredAt>>

LEMMA EnabledDecide ==
  ASSUME TypeOK, RcvdSubsetSent, NEW c \in Honest, decision[c] = nil,
         NEW r \in Rounds, NEW prop \in RProposalsFromProposerAt(c, r),
         RExistsPrecommitQuorum(c, prop.value, r), Valid(prop.value)
  PROVE  ENABLED <<OnPrecommitQuorumValue(c)>>_vars
<1>1. prop.value \in Values
  BY RProposalValueType
<1>2. prop.value # nil
  BY <1>1, NilNotInValues
<1>3. [decision EXCEPT ![c] = prop.value] # decision
  BY <1>2 DEF TypeOK
<1>4. ENABLED <<DecideAt(c, r, prop)>>_vars
  BY <1>3, AutoUSE, ExpandENABLED DEF DecideAt, vars
<1>5. <<DecideAt(c, r, prop)>>_vars => <<OnPrecommitQuorumValue(c)>>_vars
  BY DEF DecideAt, OnPrecommitQuorumValue, vars
<1> QED
  BY <1>4, <1>5, AutoUSE, ExpandENABLED
  DEFS DecideAt, OnPrecommitQuorumValue, vars

\* Honest broadcasts are timestamped no earlier than the sender's recorded
\* entry into the message round.
HonestMessageEntryOK(m) ==
  m.sender \in Honest =>
    /\ enteredAt[m.sender][m.round] # OFF
    /\ enteredAt[m.sender][m.round] <= sentTime[m]

HonestMessageAfterEntry ==
  \A m \in sent : HonestMessageEntryOK(m)

LEMMA NewHonestBroadcastEntry ==
  ASSUME TypeOK, RoundEntryHistory,
         NEW p \in Honest, NEW m0 \in Message,
         m0.sender = p, m0.round = round[p],
         sentTime' = [sentTime EXCEPT ![m0] = now], enteredAt' = enteredAt,
         NEW m \in sent', m \notin sent
  PROVE  HonestMessageEntryOK(m)'
BY SentExtend DEFS HonestMessageEntryOK, RoundEntryHistory, TypeOK

LEMMA NoNewMessageWhenSentTimeUnchanged ==
  ASSUME sentTime' = sentTime, NEW m \in sent', m \notin sent
  PROVE  FALSE
BY DEF sent

LEMMA NewHonestMessageAfterEntry ==
  ASSUME TypeOK, RcvdSubsetSent, RoundEntryHistory, [Next]_vars,
         NEW m \in sent', m \notin sent, m.sender \in Honest
  PROVE  HonestMessageEntryOK(m)'
<1>1. CASE UNCHANGED vars
  BY <1>1, NoNewMessageWhenSentTimeUnchanged DEF vars
<1>2. CASE Next
  <2>1. CASE \E p \in Honest : HonestNext(p)
    <3> PICK p \in Honest : HonestNext(p)
      BY <2>1
    <3>1. CASE Propose(p)
      <4>1. PICK v \in (IF valid[p].value # nil THEN {valid[p].value} ELSE getValue) :
            Broadcast(p, Proposal(p, round[p], v, valid[p].round))
        BY <3>1 DEF Propose
      <4>2. v \in Values /\ valid[p].round \in Rounds \cup {-1}
        BY <4>1 DEF getValue, ValuesOrNil, TypeOK, LockState
      <4>3. Proposal(p, round[p], v, valid[p].round) \in Message
        BY <4>2, HonestSubValidators, MsgProposal DEF TypeOK, Rounds
      <4>4. /\ sentTime' = [sentTime EXCEPT ![Proposal(p, round[p], v, valid[p].round)] = now]
            /\ enteredAt' = enteredAt
        BY <3>1, <4>1 DEF Propose, Broadcast
      <4> QED
        BY <4>3, <4>4, NewHonestBroadcastEntry DEF Proposal
    <3>2. CASE OnTimeoutPropose(p)
      BY <3>2, HonestSubValidators, MsgPrevote, NewHonestBroadcastEntry
      DEFS Broadcast, OnTimeoutPropose, Prevote, Rounds, TypeOK, ValuesOrNil
    <3>3. CASE OnProposalNoPOL(p)
      BY <3>3, HonestSubValidators, MsgPrevote, NewHonestBroadcastEntry, RProposalValueType
      DEFS Broadcast, OnProposalNoPOL, Prevote, Rounds, TypeOK, ValuesOrNil
    <3>4. CASE OnProposalWithPOL(p)
      BY <3>4, HonestSubValidators, MsgPrevote, NewHonestBroadcastEntry, RProposalValueType
      DEFS Broadcast, OnProposalWithPOL, Prevote, Rounds, TypeOK, ValuesOrNil
    <3>5. CASE OnPrevoteQuorumValueFirstTime(p)
      BY <3>5, HonestSubValidators, MsgPrecommit, NewHonestBroadcastEntry, RProposalValueType
      DEFS Broadcast, OnPrevoteQuorumValueFirstTime, Precommit, Rounds, TypeOK, ValuesOrNil
    <3>6. CASE OnPrevoteQuorumNil(p)
      BY <3>6, HonestSubValidators, MsgPrecommit, NewHonestBroadcastEntry
      DEFS Broadcast, OnPrevoteQuorumNil, Precommit, Rounds, TypeOK, ValuesOrNil
    <3>7. CASE OnTimeoutPrevote(p)
      BY <3>7, HonestSubValidators, MsgPrecommit, NewHonestBroadcastEntry
      DEFS Broadcast, OnTimeoutPrevote, Precommit, Rounds, TypeOK, ValuesOrNil
    <3>8. CASE ScheduleTimeoutPrevote(p)
      BY <3>8, NoNewMessageWhenSentTimeUnchanged DEF ScheduleTimeoutPrevote
    <3>9. CASE OnPrevoteQuorumValueLateUpdate(p)
      BY <3>9, NoNewMessageWhenSentTimeUnchanged DEF OnPrevoteQuorumValueLateUpdate
    <3>10. CASE ScheduleTimeoutPrecommit(p)
      BY <3>10, NoNewMessageWhenSentTimeUnchanged DEF ScheduleTimeoutPrecommit
    <3>11. CASE OnPrecommitQuorumValue(p)
      BY <3>11, NoNewMessageWhenSentTimeUnchanged DEF OnPrecommitQuorumValue
    <3>12. CASE OnTimeoutPrecommit(p)
      BY <3>12, NoNewMessageWhenSentTimeUnchanged DEF OnTimeoutPrecommit
    <3>13. CASE \E r2 \in Rounds : SkipRound(p, r2)
      BY <3>13, NoNewMessageWhenSentTimeUnchanged DEF SkipRound
    <3>14. CASE Deliver(p)
      BY <3>14, NoNewMessageWhenSentTimeUnchanged DEF Deliver
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
         <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
         DEF HonestNext, HonestStep
  <2>2. CASE \E p \in Faulty : FaultyStep(p)
    BY <2>2, SentExtend DEFS FaultyStep, Honest
  <2>3. CASE Tick
    BY <2>3, NoNewMessageWhenSentTimeUnchanged DEF Tick
  <2> QED
    BY <2>1, <2>2, <2>3, <1>2 DEF Next
<1> QED
  BY <1>1, <1>2

LEMMA HonestMessageAfterEntryStep ==
  ASSUME TypeOK, RcvdSubsetSent, RoundEntryHistory,
         HonestMessageAfterEntry, [Next]_vars, [SentTimeFrozenPred]_vars
  PROVE  HonestMessageAfterEntry'
BY EnteredAtFrozenStep, NewHonestMessageAfterEntry
DEFS HonestMessageAfterEntry, HonestMessageEntryOK, Message, PrecommitMsg, PrevoteMsg, ProposalMsg, sent, SentTimeFrozenPred, vars

THEOREM HonestMessageAfterEntryInv ==
    ASSUME Spec PROVE []HonestMessageAfterEntry
<1>1. HonestMessageAfterEntry
  BY DEF Init, Spec, HonestMessageAfterEntry, sent, OFF
<1>2. [](TypeOK /\ RcvdSubsetSent /\ RoundEntryHistory /\ [Next]_vars
          /\ [SentTimeFrozenPred]_vars)
  BY InvProof, RoundEntryHistoryInv, SentTimeFrozenInv, PTL DEF Spec, Inv
<1>3. [](HonestMessageAfterEntry => HonestMessageAfterEntry')
  BY <1>2, HonestMessageAfterEntryStep, PTL
<1> QED
  BY <1>1, <1>3, PTL

Lemma5Outcome(r) ==
  SomeCorrectDecided \/ PostGSTPriorRoundLock(r)

Lemma5BlockingOutcome(p, r) ==
  SomeCorrectDecided \/ BlockingLockDuring(p, r)

GoodRoundResolution ==
  SomeCorrectDecided \/ \E r \in Rounds : PostGSTPriorRoundLock(r)

-----------------------------------------------------------------------------
\* Opaque wrapper used at the quantified citation boundary. This avoids
\* exposing Lemma5Hyp's nested quantifiers while TLAPS introduces p and r.
Lemma5Reach(p, r) ==
  Lemma5Hyp(p, r) ~> Lemma5Outcome(r)

LEMMA AllDecidedImpliesEach ==
  ASSUME NEW p \in Honest
  PROVE  [](AllCorrectDecided => HasDecided(p))
<1>1. AllCorrectDecided => HasDecided(p)
  BY DEF AllCorrectDecided
<1> QED
  BY <1>1, PTL

LEMMA AllDecidedLeadsToEach ==
  ASSUME NEW p \in Honest, <>AllCorrectDecided
  PROVE  <>HasDecided(p)
<1>1. [](AllCorrectDecided => HasDecided(p))
  BY AllDecidedImpliesEach
<1> QED
  BY <1>1, PTL
=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)