--------------- MODULE TendermintPartialSyncTerminationWithinRoundMC ---------
(***************************************************************************)
(* Phase 0 diagnostics for the Lemma 5 proof.                              *)
(*                                                                         *)
(* The passing scenario reaches Lemma5Hyp in round 1, then reaches the     *)
(* strengthened prevote and precommit stages and one correct decision.     *)
(* The old defect scenario preserves the false AllPrevotedBy to            *)
(* AllPrecommittedBy transition in a separate expected failure config.     *)
(* The Phase 2 lock-shift scenario preserves the later counterexample in   *)
(* which Lemma5Hyp loses lock dominance before the common prevote stage.   *)
(***************************************************************************)
EXTENDS TendermintPartialSync, TLC

CONSTANT MCScenario

VARIABLE mcStep

mcVars == <<vars, mcStep>>

MCValidators == {"h1", "h2", "h3", "b"}
MCFaulty == {"b"}
MCValid(v) == TRUE

\* Widened from 0..20: at Delta = 2 the phase2-entry schedule runs to
\* now = 23 and arms round-2 propose timers at now + TimeoutPropose(2) = 32.
MCNat == 0..32

MCProposalMsg == [
  type       : {"Proposal"},
  sender     : Validators,
  round      : Rounds,
  value      : Values,
  validRound : {-1} \cup Rounds
]

MCValue == CHOOSE v \in Values : TRUE

MCValueA == CHOOSE v \in Values : TRUE
MCValueB == CHOOSE v \in Values : v # MCValueA

MCProposer ==
  CASE MCScenario = "positive"
        -> [r \in MCNat |-> IF r = 1 THEN "h1" ELSE "b"]
    [] MCScenario = "phase2-entry"
        -> [r \in MCNat |-> IF r = 2 THEN "h3" ELSE "b"]
    [] MCScenario = "phase2-lock-shift"
        -> [r \in MCNat |-> IF r = 0 \/ r = 1 THEN "h1" ELSE "b"]
    [] MCScenario = "window-gst"
        -> [r \in MCNat |-> IF r = 0 \/ r = 1 THEN "h1" ELSE "b"]
    [] MCScenario = "lock-retry"
        -> [r \in MCNat |-> CASE r = 0 \/ r = 1 -> "h1"
                              [] r = 2         -> "h3"
                              [] OTHER         -> "b"]
    [] MCScenario = "lock-relativize"
        -> [r \in MCNat |-> IF r <= 2 THEN "h1" ELSE "b"]
    [] OTHER
        -> [r \in MCNat |-> IF r = 0 THEN "h1" ELSE "b"]

(***************************************************************************)
(* Lemma 5 predicates mirrored from the proof base. The executable harness *)
(* extends TendermintPartialSync directly because tla2tools does not bundle   *)
(* the TLAPS only NaturalsInduction and FiniteSetTheorems modules.         *)
(* Proposal validRound witnesses use the exact finite MCProposalMsg range. *)
(***************************************************************************)
HasDecided(p)           == decision[p] # nil
VotedPrevote(p, v, r)   == Prevote(p, r, v) \in sent
VotedPrecommit(p, v, r) == Precommit(p, r, v) \in sent

SomeCorrectDecided ==
  \E c \in Honest : HasDecided(c)

FirstToEnter(p, r) ==
  /\ enteredAt[p][r] = now
  /\ \A c \in Honest : round[c] <= r
  /\ \A c \in Honest : enteredAt[c][r] = OFF \/ enteredAt[c][r] >= now

Lemma5Timeouts(r) ==
  /\ TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

Lemma5Hyp(p, r) ==
  /\ now > GST
  /\ r > 0
  /\ FirstToEnter(p, r)
  /\ Proposer[r] \in Honest
  /\ \A c \in Honest : locked[c].round <= valid[Proposer[r]].round
  /\ Lemma5Timeouts(r)

WRDurable(r) ==
  /\ now >= GST
  /\ Proposer[r] \in Honest
  /\ TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

AllPrevotedBy(p, r) ==
  /\ WRDurable(r)
  /\ \E v \in Values :
       /\ Valid(v)
       /\ \E vr \in {-1} \cup Rounds : Proposal(Proposer[r], r, v, vr) \in sent
       /\ \A c \in Honest : VotedPrevote(c, v, r)
  /\ now <= enteredAt[p][r] + 2 * Delta + TimeoutPrecommit(r - 1)

AllPrecommittedBy(p, r) ==
  /\ WRDurable(r)
  /\ \E v \in Values :
       /\ Valid(v)
       /\ \E vr \in {-1} \cup Rounds : Proposal(Proposer[r], r, v, vr) \in sent
       /\ \A c \in Honest : VotedPrecommit(c, v, r)
  /\ now <= enteredAt[p][r] + 3 * Delta + TimeoutPrecommit(r - 1)

(***************************************************************************)
(* Phase 1 predicates mirrored from the proof module for TLC.              *)
(***************************************************************************)
MCRoundEntryHistory ==
  /\ \A c \in Honest : enteredAt[c][round[c]] # OFF
  /\ \A c \in Honest : \A r \in Rounds :
       enteredAt[c][r] # OFF =>
         /\ r <= round[c]
         /\ enteredAt[c][r] <= now

MCRoundOrigin(p, r) ==
  /\ r > 0
  /\ enteredAt[p][r] # OFF
  /\ enteredAt[p][r] > GST
  /\ \A c \in Honest :
       enteredAt[c][r] = OFF \/ enteredAt[c][r] >= enteredAt[p][r]

MCHonestMessageAfterEntry ==
  \A m \in sent :
    m.sender \in Honest =>
      /\ enteredAt[m.sender][m.round] # OFF
      /\ enteredAt[m.sender][m.round] <= sentTime[m]

MCPrevoteControlReady(r, v) ==
  \A c \in Honest :
    \/ VotedPrecommit(c, v, r)
    \/ /\ round[c] = r
       /\ step[c] = "prevote"
       /\ (timer[c]["prevote"] = OFF \/ now < timer[c]["prevote"])

MCPrevoteStage(p, r, v) ==
  /\ MCRoundOrigin(p, r)
  /\ WRDurable(r)
  /\ v \in Values
  /\ Valid(v)
  /\ \E vr \in {-1} \cup Rounds : Proposal(Proposer[r], r, v, vr) \in sent
  /\ \A c \in Honest : VotedPrevote(c, v, r)
  /\ MCPrevoteControlReady(r, v)
  /\ now <= enteredAt[p][r] + 2 * Delta + TimeoutPrecommit(r - 1)

MCPrecommitStage(p, r, v) ==
  /\ MCRoundOrigin(p, r)
  /\ WRDurable(r)
  /\ v \in Values
  /\ Valid(v)
  /\ \E vr \in {-1} \cup Rounds : Proposal(Proposer[r], r, v, vr) \in sent
  /\ \A c \in Honest : VotedPrecommit(c, v, r)
  /\ \A c \in Honest :
       \/ HasDecided(c)
       \/ /\ round[c] = r
          /\ step[c] \in {"precommit", "decided"}
          /\ (timer[c]["precommit"] = OFF \/ now < timer[c]["precommit"])
  /\ now <= enteredAt[p][r] + 3 * Delta + TimeoutPrecommit(r - 1)

MCPostGSTPriorRoundLock(r) ==
  \E w \in Values, c \in Honest, lr \in Rounds :
    /\ lr < r
    /\ VotedPrecommit(c, w, lr)
    /\ sentTime[Precommit(c, lr, w)] > GST

\* The relativized blocking-lock event of the LockRetry plan, mirrored for
\* TLC. It has the same shape as BlockingLockDuring of the proof module. There
\* are two differences, and both belong to the harness. The witness for
\* validRound ranges over the finite range of MCProposalMsg, and not over Int.
\* Both round witnesses are cut down to 0..r. The conjuncts `vr < lr < r` make
\* that equivalent, and it keeps the enumeration off the whole of MCNat.
MCBlockingLockDuring(p, r) ==
  \E v \in Values, w \in Values, vr \in {-1} \cup (0..r), c \in Honest, lr \in 0..r :
    /\ Proposal(Proposer[r], r, v, vr) \in sent
    /\ vr < lr
    /\ lr < r
    /\ w # v
    /\ VotedPrecommit(c, w, lr)
    /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]

\*  The rejected STRICT variant, kept as a live regression. Maximal progress,
\*  which is the ~CanCompute guard of Tick, pushes the disruptive lock into
\*  the SAME clock instant as the entry into the good round. A strict `>`
\*  therefore misses the very scenario that the disjunct exists for, and it
\*  would make Lemma5OrBlockingLock false.
MCBlockingLockDuringStrict(p, r) ==
  \E v \in Values, w \in Values, vr \in {-1} \cup (0..r), c \in Honest, lr \in 0..r :
    /\ Proposal(Proposer[r], r, v, vr) \in sent
    /\ vr < lr
    /\ lr < r
    /\ w # v
    /\ VotedPrecommit(c, w, lr)
    /\ sentTime[Precommit(c, lr, w)] > enteredAt[p][r]

\* The same event with the entry timestamp DROPPED. It isolates the timestamp
\* as the only discriminator. Where this event holds and MCBlockingLockDuring
\* does not, the relativization is what excludes a lock that the GST-relative
\* PostGSTPriorRoundLock still latches.
MCBlockingLockUntimed(p, r) ==
  \E v \in Values, w \in Values, vr \in {-1} \cup (0..r), c \in Honest, lr \in 0..r :
    /\ Proposal(Proposer[r], r, v, vr) \in sent
    /\ vr < lr
    /\ lr < r
    /\ w # v
    /\ VotedPrecommit(c, w, lr)

(***************************************************************************)
(* Script helpers. Every transition is a concrete subaction of Next.       *)
(***************************************************************************)
MCTake(n, A) ==
  /\ mcStep = n
  /\ A
  /\ mcStep' = n + 1

MCHonestProposes(p, v) ==
  /\ v \in Values
  /\ Propose(p)
  /\ sentTime'[Proposal(p, round[p], v, valid[p].round)] = now

MCFaultyActivatesAt(m, c) ==
  /\ m \in Message
  /\ c \in Honest
  /\ m.sender \in Faulty
  /\ sentTime[m] = OFF
  /\ FaultyStep(m.sender)
  /\ sentTime'[m] = now
  /\ m \in rcvd'[c]

(***************************************************************************)
(* Passing path. Round 0 times out under a faulty proposer. h1 is first    *)
(* into round 1 at now = 8. The honest round 1 proposer then drives all    *)
(* honest validators through the candidate stages and h1 decides.          *)
(***************************************************************************)
MCPositiveNext ==
  \/ MCTake(0, Tick)
  \/ MCTake(1, Tick)
  \/ MCTake(2, Tick)
  \/ MCTake(3, Tick)
  \/ MCTake(4, Tick)
  \/ MCTake(5, OnTimeoutPropose("h1"))
  \/ MCTake(6, OnTimeoutPropose("h2"))
  \/ MCTake(7, OnTimeoutPropose("h3"))
  \/ MCTake(8, Deliver("h1"))
  \/ MCTake(9, Deliver("h2"))
  \/ MCTake(10, Deliver("h3"))
  \/ MCTake(11, OnPrevoteQuorumNil("h1"))
  \/ MCTake(12, OnPrevoteQuorumNil("h2"))
  \/ MCTake(13, OnPrevoteQuorumNil("h3"))
  \/ MCTake(14, Deliver("h1"))
  \/ MCTake(15, Deliver("h2"))
  \/ MCTake(16, Deliver("h3"))
  \/ MCTake(17, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(18, ScheduleTimeoutPrecommit("h2"))
  \/ MCTake(19, ScheduleTimeoutPrecommit("h3"))
  \/ MCTake(20, Tick)
  \/ MCTake(21, Tick)
  \/ MCTake(22, Tick)
  \/ MCTake(23, OnTimeoutPrecommit("h1"))
  \/ MCTake(24, OnTimeoutPrecommit("h2"))
  \/ MCTake(25, OnTimeoutPrecommit("h3"))
  \/ MCTake(26, MCHonestProposes("h1", MCValue))
  \/ MCTake(27, OnProposalNoPOL("h1"))
  \/ MCTake(28, Deliver("h2"))
  \/ MCTake(29, OnProposalNoPOL("h2"))
  \/ MCTake(30, Deliver("h3"))
  \/ MCTake(31, OnProposalNoPOL("h3"))
  \/ MCTake(32, Deliver("h1"))
  \/ MCTake(33, OnPrevoteQuorumValueFirstTime("h1"))
  \/ MCTake(34, Deliver("h2"))
  \/ MCTake(35, OnPrevoteQuorumValueFirstTime("h2"))
  \/ MCTake(36, Deliver("h3"))
  \/ MCTake(37, OnPrevoteQuorumValueFirstTime("h3"))
  \/ MCTake(38, Deliver("h1"))
  \/ MCTake(39, OnPrecommitQuorumValue("h1"))

MCPositiveChecks ==
  /\ <>Lemma5Hyp("h1", 1)
  /\ <>(\E v \in Values : MCPrevoteStage("h1", 1, v))
  /\ <>(\E v \in Values : MCPrecommitStage("h1", 1, v))
  /\ (Lemma5Hyp("h1", 1) ~> SomeCorrectDecided)

(***************************************************************************)
(* Preserved defect. All honest validators prevote MCValue at round 0, but *)
(* h1 and h2 time out and precommit nil before they receive the vote of    *)
(* h3. The old milestone AllPrevotedBy stays true on terminal stuttering.  *)
(* The Tick chain runs to now = GST = 6, because AllPrevotedBy needs       *)
(* WRDurable(0). The conjuncts TimeoutPrevote(0) > 2*Delta and             *)
(* TimeoutPrecommit(0) > 2*Delta of WRDurable(0) put a floor of 2*Delta on *)
(* the base timeouts. The prevote timers therefore fire at now = 5, and    *)
(* not at now = 3.                                                         *)
(***************************************************************************)
MCOldDefectNext ==
  \/ MCTake(0, MCHonestProposes("h1", MCValue))
  \/ MCTake(1, OnProposalNoPOL("h1"))
  \/ MCTake(2, MCFaultyActivatesAt(Prevote("b", 0, nil), "h3"))
  \/ MCTake(3, Deliver("h2"))
  \/ MCTake(4, OnProposalNoPOL("h2"))
  \/ MCTake(5, ScheduleTimeoutPrevote("h2"))
  \/ MCTake(6, Deliver("h1"))
  \/ MCTake(7, ScheduleTimeoutPrevote("h1"))
  \/ MCTake(8, Deliver("h3"))
  \/ MCTake(9, OnProposalNoPOL("h3"))
  \/ MCTake(10, OnPrevoteQuorumValueFirstTime("h3"))
  \/ MCTake(11, Tick)
  \/ MCTake(12, Tick)
  \/ MCTake(13, Tick)
  \/ MCTake(14, Tick)
  \/ MCTake(15, Tick)
  \/ MCTake(16, OnTimeoutPrevote("h1"))
  \/ MCTake(17, OnTimeoutPrevote("h2"))
  \/ MCTake(18, Tick)

MCOldDefect ==
  /\ mcStep = 19
  /\ now = GST
  /\ AllPrevotedBy("h1", 0)
  /\ ~AllPrecommittedBy("h1", 0)
  /\ Precommit("h1", 0, nil) \in sent
  /\ Precommit("h2", 0, nil) \in sent
  /\ Precommit("h3", 0, MCValue) \in sent

MCOldDefectReachable == <>MCOldDefect

MCOldTerminalIsDefect == mcStep = 19 => MCOldDefect

MCOldMilestoneProgress ==
  AllPrevotedBy("h1", 0) ~> AllPrecommittedBy("h1", 0)

\* This assertion checks the substantive control state exclusion separately
\* from MCRoundOrigin's positive round requirement.
MCOldDefectExcluded ==
  MCOldDefect =>
    /\ ~MCPrevoteControlReady(0, MCValue)
    /\ ~MCPrevoteStage("h1", 0, MCValue)

(***************************************************************************)
(* Phase 2 entry regression. h1 is first into good round 2 after GST. Its  *)
(* correct proposer h3 receives a round-1 precommit quorum while still in  *)
(* propose. The fired precommit timer advances h3 into round 2, matching   *)
(* Algorithm 1 line 66, then h3 proposes and every honest validator        *)
(* prevotes the selected value.                                            *)
(*                                                                         *)
(* The schedule is tightly constrained. A change to any timing constant    *)
(* stalls it, and does not merely slow it down. At Delta = 2:              *)
(* - T0Propose = 7 is FORCED. ProposeTimeoutMargin forces it, and          *)
(*   TimeoutPropose(2) > 2*Delta + TimeoutPrecommit(1) of WRDurable(2)     *)
(*   forces it independently.                                              *)
(* - The propose timeout of round 1 must not fire after the round-0        *)
(*   precommit timeout of h3. That needs T0Propose + TDelta <= k +         *)
(*   T0Precommit for the k Ticks that follow the entry into round 1, so k  *)
(*   = 5.                                                                  *)
(* - The Gossip deadline caps that run of Ticks. A pending message from    *)
(*   before GST forbids a Tick once now + 1 >= GST + Delta, so GST = 14.   *)
(* - h1, h2 and h3 all schedule their round-1 precommit timers at now =    *)
(*   18. Those three timeouts therefore fire together at now = 22, and no  *)
(*   Tick separates them.                                                  *)
(* The run ends at now = 22, with mcStep = 65.                             *)
(***************************************************************************)
MCPhase2EntryNext ==
  \/ MCTake(0, Tick)
  \/ MCTake(1, Tick)
  \/ MCTake(2, Tick)
  \/ MCTake(3, Tick)
  \/ MCTake(4, Tick)
  \/ MCTake(5, Tick)
  \/ MCTake(6, Tick)
  \/ MCTake(7, OnTimeoutPropose("h1"))
  \/ MCTake(8, OnTimeoutPropose("h2"))
  \/ MCTake(9, OnTimeoutPropose("h3"))
  \/ MCTake(10, Deliver("h1"))
  \/ MCTake(11, Deliver("h2"))
  \/ MCTake(12, OnPrevoteQuorumNil("h1"))
  \/ MCTake(13, OnPrevoteQuorumNil("h2"))
  \/ MCTake(14, MCFaultyActivatesAt(Precommit("b", 0, nil), "h1"))
  \/ MCTake(15, Deliver("h1"))
  \/ MCTake(16, Deliver("h2"))
  \/ MCTake(17, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(18, ScheduleTimeoutPrecommit("h2"))
  \/ MCTake(19, Tick)
  \/ MCTake(20, Tick)
  \/ MCTake(21, Tick)
  \/ MCTake(22, OnTimeoutPrecommit("h1"))
  \/ MCTake(23, OnTimeoutPrecommit("h2"))
  \/ MCTake(24, Tick)
  \/ MCTake(25, Tick)
  \/ MCTake(26, Tick)
  \/ MCTake(27, Tick)
  \/ MCTake(28, Tick)
  \/ MCTake(29, Deliver("h3"))
  \/ MCTake(30, OnPrevoteQuorumNil("h3"))
  \/ MCTake(31, ScheduleTimeoutPrecommit("h3"))
  \/ MCTake(32, Tick)
  \/ MCTake(33, Deliver("h1"))
  \/ MCTake(34, Deliver("h2"))
  \/ MCTake(35, Tick)
  \/ MCTake(36, Tick)
  \/ MCTake(37, OnTimeoutPropose("h1"))
  \/ MCTake(38, OnTimeoutPropose("h2"))
  \/ MCTake(39, MCFaultyActivatesAt(Prevote("b", 1, nil), "h1"))
  \/ MCTake(40, Deliver("h1"))
  \/ MCTake(41, Deliver("h2"))
  \/ MCTake(42, OnPrevoteQuorumNil("h1"))
  \/ MCTake(43, OnPrevoteQuorumNil("h2"))
  \/ MCTake(44, MCFaultyActivatesAt(Precommit("b", 1, nil), "h1"))
  \/ MCTake(45, Deliver("h1"))
  \/ MCTake(46, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(47, OnTimeoutPrecommit("h3"))
  \/ MCTake(48, Deliver("h2"))
  \/ MCTake(49, ScheduleTimeoutPrecommit("h2"))
  \/ MCTake(50, Deliver("h3"))
  \/ MCTake(51, ScheduleTimeoutPrecommit("h3"))
  \/ MCTake(52, Tick)
  \/ MCTake(53, Tick)
  \/ MCTake(54, Tick)
  \/ MCTake(55, Tick)
  \/ MCTake(56, OnTimeoutPrecommit("h1"))
  \/ MCTake(57, OnTimeoutPrecommit("h2"))
  \/ MCTake(58, OnTimeoutPrecommit("h3"))
  \/ MCTake(59, MCHonestProposes("h3", MCValue))
  \/ MCTake(60, OnProposalNoPOL("h3"))
  \/ MCTake(61, Deliver("h1"))
  \/ MCTake(62, OnProposalNoPOL("h1"))
  \/ MCTake(63, Deliver("h2"))
  \/ MCTake(64, OnProposalNoPOL("h2"))

MCPhase2Success ==
  SomeCorrectDecided \/ \E v \in Values : MCPrevoteStage("h1", 2, v)

MCPhase2EntryChecks ==
  /\ <>Lemma5Hyp("h1", 2)
  /\ (Lemma5Hyp("h1", 2) ~> MCPhase2Success)

MCPhase2TerminalEntry ==
  mcStep = 65 =>
    /\ now = 22
    /\ MCRoundOrigin("h1", 2)
    /\ enteredAt["h3"][2] = 22
    /\ \E v \in Values : MCPrevoteStage("h1", 2, v)

(***************************************************************************)
(* Expected Phase 2 failure. At now = 3, h1 is the first honest validator  *)
(* to enter good round 1 and Lemma5Hyp holds with every honest lock at -1. *)
(* A round-0 prevote from b first reaches h3 at now = 3, after h1 enters   *)
(* round 1. That receipt activates gossip and completes an a-polka at h3.  *)
(* h3 locks a in round 0 after the hypothesis point, then rejects h1's     *)
(* round-1 proposal for b. The point-in-time lock-dominance hypothesis was *)
(* discarded by RoundOrigin and does not persist to the prevote stage.     *)
(***************************************************************************)
MCPhase2LockShiftNext ==
  \/ MCTake(0, MCHonestProposes("h1", MCValueA))
  \/ MCTake(1, OnProposalNoPOL("h1"))
  \/ MCTake(2, Tick)
  \/ MCTake(3, Deliver("h3"))
  \/ MCTake(4, OnProposalNoPOL("h3"))
  \/ MCTake(5, OnTimeoutPropose("h2"))
  \/ MCTake(6, MCFaultyActivatesAt(Prevote("b", 0, MCValueB), "h1"))
  \/ MCTake(7, Deliver("h1"))
  \/ MCTake(8, ScheduleTimeoutPrevote("h1"))
  \/ MCTake(9, Deliver("h2"))
  \/ MCTake(10, ScheduleTimeoutPrevote("h2"))
  \/ MCTake(11, Tick)
  \/ MCTake(12, OnTimeoutPrevote("h1"))
  \/ MCTake(13, OnTimeoutPrevote("h2"))
  \/ MCTake(14, MCFaultyActivatesAt(Precommit("b", 0, nil), "h1"))
  \/ MCTake(15, Deliver("h1"))
  \/ MCTake(16, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(17, Deliver("h2"))
  \/ MCTake(18, ScheduleTimeoutPrecommit("h2"))
  \/ MCTake(19, Deliver("h3"))
  \/ MCTake(20, ScheduleTimeoutPrevote("h3"))
  \/ MCTake(21, ScheduleTimeoutPrecommit("h3"))
  \/ MCTake(22, Tick)
  \/ MCTake(23, OnTimeoutPrecommit("h1"))
  \/ MCTake(24, MCHonestProposes("h1", MCValueB))
  \/ MCTake(25, OnProposalNoPOL("h1"))
  \/ MCTake(26, MCFaultyActivatesAt(Prevote("b", 0, MCValueA), "h3"))
  \/ MCTake(27, OnPrevoteQuorumValueFirstTime("h3"))
  \/ MCTake(28, Deliver("h3"))
  \/ MCTake(29, OnTimeoutPrecommit("h3"))
  \/ MCTake(30, OnProposalNoPOL("h3"))

MCPhase2LockShiftSuccess ==
  SomeCorrectDecided \/ \E v \in Values : MCPrevoteStage("h1", 1, v)

MCPhase2LockShiftProgress ==
  Lemma5Hyp("h1", 1) ~> MCPhase2LockShiftSuccess

MCPhase2RepairedProgress ==
  Lemma5Hyp("h1", 1) ~>
    (MCPhase2LockShiftSuccess \/ MCPostGSTPriorRoundLock(1))

MCPhase2LockShiftTerminal ==
  mcStep = 31 =>
    /\ now = 3
    /\ round["h3"] = 1
    /\ locked["h3"].round = 0
    /\ locked["h3"].value = MCValueA
    /\ VotedPrevote("h1", MCValueB, 1)
    /\ VotedPrevote("h3", nil, 1)
    /\ MCPostGSTPriorRoundLock(1)
    /\ ~MCPhase2LockShiftSuccess

(***************************************************************************)
(* LockRetry check 1: the relativized disjunct is not vacuous. The same    *)
(* disruption run reaches MCBlockingLockDuring("h1", 1). h3 locks a at     *)
(* round 0, for a value other than the proposed one, at the instant when   *)
(* h1 entered round 1. That round 0 is strictly above the validRound -1 of *)
(* the round-1 proposal, and it is strictly below round 1. The strict      *)
(* variant is NEVER reached. That is why the timestamp conjunct is `>=`,   *)
(* because maximal progress puts the lock and the entry in the same clock  *)
(* instant.                                                                *)
(***************************************************************************)
MCBlockingLockReachable == <>MCBlockingLockDuring("h1", 1)

MCBlockingLockStrictNever == ~MCBlockingLockDuringStrict("h1", 1)

(***************************************************************************)
(* LockRetry checks 2 and 3: the RETRY. The disruption run above is        *)
(* continued past its terminal state. h2 joins round 1. All three honest   *)
(* validators prevote at round 1, and they then precommit nil on their     *)
(* prevote timeouts. The precommit quorum of round 1 carries them into     *)
(* round 2 at now = 15. That is twelve instants after the round-0 lock     *)
(* that disrupted round 1.                                                 *)
(*                                                                         *)
(* This one run checks two facts that the plan needs.                      *)
(* - The relativization un-latches, which is check 2. At round 2,          *)
(*   PostGSTPriorRoundLock still holds, because it is anchored to the      *)
(*   CONSTANT GST. BlockingLockDuring does not hold, because the round-0   *)
(*   lock is before the instant of the round-2 entry. The lock-relativize  *)
(*   tail isolates the entry timestamp as the ONLY discriminator. It gives *)
(*   round 2 a proposer whose valid round is still -1, which keeps every   *)
(*   other conjunct satisfied.                                             *)
(* - The retry terminates on this run, which is check 3. The round-2       *)
(*   proposer h3 carries the disruptive lock in its own valid record.      *)
(*   Round 2 is therefore a second good round, nothing disrupts it, and h1 *)
(*   decides.                                                              *)
(***************************************************************************)
MCLockRetryPrefix ==
  \/ MCPhase2LockShiftNext
  \* h2 is the last honest validator into round 1. It prevotes the proposal.
  \/ MCTake(31, OnTimeoutPrecommit("h2"))
  \/ MCTake(32, Deliver("h2"))
  \/ MCTake(33, OnProposalNoPOL("h2"))
  \* Round 1 stalls: two prevotes for the proposal and one for nil is no
  \* quorum for either, so all three arm prevote timers and time out.
  \/ MCTake(34, Deliver("h1"))
  \/ MCTake(35, Deliver("h3"))
  \/ MCTake(36, ScheduleTimeoutPrevote("h1"))
  \/ MCTake(37, ScheduleTimeoutPrevote("h2"))
  \/ MCTake(38, ScheduleTimeoutPrevote("h3"))
  \/ MCTake(39, Tick)
  \/ MCTake(40, Tick)
  \/ MCTake(41, Tick)
  \/ MCTake(42, Tick)
  \/ MCTake(43, Tick)
  \/ MCTake(44, Tick)
  \/ MCTake(45, OnTimeoutPrevote("h1"))
  \/ MCTake(46, OnTimeoutPrevote("h2"))
  \/ MCTake(47, OnTimeoutPrevote("h3"))
  \/ MCTake(48, Deliver("h1"))
  \/ MCTake(49, Deliver("h2"))
  \/ MCTake(50, Deliver("h3"))
  \/ MCTake(51, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(52, ScheduleTimeoutPrecommit("h2"))
  \/ MCTake(53, ScheduleTimeoutPrecommit("h3"))
  \/ MCTake(54, Tick)
  \/ MCTake(55, Tick)
  \/ MCTake(56, Tick)
  \/ MCTake(57, Tick)
  \/ MCTake(58, Tick)
  \/ MCTake(59, Tick)
  \* Round 2 is entered at now = 15. h1 is first in, so Lemma5Hyp("h1", 2)
  \* holds at that state whenever the round-2 proposer dominates the locks.
  \/ MCTake(60, OnTimeoutPrecommit("h1"))
  \/ MCTake(61, OnTimeoutPrecommit("h2"))
  \/ MCTake(62, OnTimeoutPrecommit("h3"))

\* Check 3 tail. h3 proposes its own locked value with the proof of lock, so
\* every honest validator prevotes it and h1 decides.
MCLockRetryNext ==
  \/ MCLockRetryPrefix
  \/ MCTake(63, MCHonestProposes("h3", MCValueA))
  \/ MCTake(64, OnProposalWithPOL("h3"))
  \/ MCTake(65, Deliver("h1"))
  \/ MCTake(66, OnProposalWithPOL("h1"))
  \/ MCTake(67, Deliver("h2"))
  \/ MCTake(68, OnProposalWithPOL("h2"))
  \/ MCTake(69, Deliver("h1"))
  \/ MCTake(70, OnPrevoteQuorumValueFirstTime("h1"))
  \/ MCTake(71, Deliver("h2"))
  \/ MCTake(72, OnPrevoteQuorumValueFirstTime("h2"))
  \/ MCTake(73, Deliver("h3"))
  \/ MCTake(74, OnPrevoteQuorumValueFirstTime("h3"))
  \/ MCTake(75, Deliver("h1"))
  \/ MCTake(76, OnPrecommitQuorumValue("h1"))

MCLockRetryComplete == <>(mcStep = 77)

MCLockRetryChecks ==
  /\ <>MCBlockingLockDuring("h1", 1)
  /\ <>Lemma5Hyp("h1", 2)
  /\ (Lemma5Hyp("h1", 2) ~> SomeCorrectDecided)

\* From the round-2 entry on, the GST-relative branch is latched and the
\* entry-relative branch is not.
MCLockRetryUnlatched ==
  mcStep >= 61 =>
    /\ MCPostGSTPriorRoundLock(2)
    /\ ~MCBlockingLockDuring("h1", 2)

MCLockRetryTerminal ==
  mcStep = 77 =>
    /\ now = 15
    /\ enteredAt["h1"][2] = 15
    /\ decision["h1"] = MCValueA
    /\ locked["h1"].round = 2

\* Check 2 tail. Round 2 gets a proposer whose valid round is still -1, so
\* the round-0 lock satisfies every conjunct of the blocking event except the
\* entry timestamp.
MCLockRelativizeNext ==
  \/ MCLockRetryPrefix
  \/ MCTake(63, MCHonestProposes("h1", MCValueB))

MCLockRelativizeComplete == <>(mcStep = 64)

MCLockRelativizeTerminal ==
  mcStep = 64 =>
    /\ now = 15
    /\ enteredAt["h1"][2] = 15
    /\ Proposal("h1", 2, MCValueB, -1) \in sent
    /\ MCPostGSTPriorRoundLock(2)
    /\ MCBlockingLockUntimed("h1", 2)
    /\ ~MCBlockingLockDuring("h1", 2)

-----------------------------------------------------------------------------
(***************************************************************************)
(* REFUTATION of the window lemma as first stated. The expected outcome of *)
(* this run is an INVARIANT VIOLATION of MCLateValueLockWindow at          *)
(* mcStep 24, with MCLateValueLockWindowRepaired holding throughout.       *)
(*                                                                         *)
(* ...RoundProgress's LateValueLockWindow concludes TimeoutPrecommit(lr)   *)
(* <= Delta from a correct value-precommit at round lr timestamped at or   *)
(* after a post-GST entry into a round above lr. Its recorded argument     *)
(* reaches that through "x's arming quorum is in `sent` by arm_x, so c     *)
(* holds it by arm_x + Delta". That step needs arm_x >= GST.               *)
(* DeliveryDeadline(m) is max(sentTime[m], GST) + Delta, so a message sent *)
(* BEFORE GST may be withheld until GST + Delta no matter how early it was *)
(* sent.                                                                   *)
(*                                                                         *)
(* This script exploits exactly that gap. Every message of round 0 is sent *)
(* before GST = 4. h1 and h2 receive the prevotes of round 0 at once, and  *)
(* TimeoutPrevote(0) = 1 elapses for them immediately. h1 therefore arms   *)
(* its precommit timer at now = 2, and it enters round 1 at now = 5, one   *)
(* instant after GST. h3 is kept two prevotes short of a quorum until      *)
(* then. Its own prevote timer is therefore still OFF, and no deadline     *)
(* constrains it. The equivocating round-0 prevote of b completes the      *)
(* polka of h3 at now = 5. h3 value-precommits at round 0, at the instant  *)
(* of the round-1 entry, with TimeoutPrecommit(0) = 3 > Delta = 2.         *)
(* Lemma5Hyp("h1", 1) and MCBlockingLockDuring("h1", 1) both hold there.   *)
(* This is therefore a genuine disruption of a good round, and not an      *)
(* off-path state.                                                         *)
(***************************************************************************)
MCLateValueLockWindow ==
  \A c \in Honest, w \in Values, lr \in Rounds, p \in Honest, r \in Rounds :
    ( /\ lr < r
      /\ enteredAt[p][r] # OFF
      /\ enteredAt[p][r] > GST
      /\ Precommit(c, lr, w) \in sent
      /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r] )
    => TimeoutPrecommit(lr) <= Delta

\* The same antecedent with the repaired conclusion. The escape is a
\* disruption round below GST, which is still a CONSTANT ceiling, so the
\* retry downstream still closes. Expected to HOLD on this run.
MCLateValueLockWindowRepaired ==
  \A c \in Honest, w \in Values, lr \in Rounds, p \in Honest, r \in Rounds :
    ( /\ lr < r
      /\ enteredAt[p][r] # OFF
      /\ enteredAt[p][r] > GST
      /\ Precommit(c, lr, w) \in sent
      /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r] )
    => TimeoutPrecommit(lr) <= Delta \/ lr < GST

\* Separates a stalled script from a real property violation.
MCWindowGstComplete == <>(mcStep = 24)

\* The disruption is at a good round: both hold at mcStep 24.
MCWindowGstDisrupted ==
  <>(Lemma5Hyp("h1", 1) \/ MCBlockingLockDuring("h1", 1))

MCWindowGstNext ==
  \/ MCTake(0, MCHonestProposes("h1", MCValueA))
  \/ MCTake(1, OnProposalNoPOL("h1"))
  \/ MCTake(2, Deliver("h3"))
  \/ MCTake(3, OnProposalNoPOL("h3"))
  \/ MCTake(4, Tick)
  \/ MCTake(5, OnTimeoutPropose("h2"))
  \/ MCTake(6, MCFaultyActivatesAt(Prevote("b", 0, MCValueB), "h1"))
  \/ MCTake(7, Deliver("h1"))
  \/ MCTake(8, ScheduleTimeoutPrevote("h1"))
  \/ MCTake(9, Deliver("h2"))
  \/ MCTake(10, ScheduleTimeoutPrevote("h2"))
  \/ MCTake(11, Tick)
  \/ MCTake(12, OnTimeoutPrevote("h1"))
  \/ MCTake(13, OnTimeoutPrevote("h2"))
  \/ MCTake(14, MCFaultyActivatesAt(Precommit("b", 0, nil), "h1"))
  \/ MCTake(15, Deliver("h1"))
  \/ MCTake(16, ScheduleTimeoutPrecommit("h1"))
  \/ MCTake(17, Tick)
  \/ MCTake(18, Tick)
  \/ MCTake(19, Tick)
  \/ MCTake(20, OnTimeoutPrecommit("h1"))
  \/ MCTake(21, MCHonestProposes("h1", MCValueB))
  \/ MCTake(22, MCFaultyActivatesAt(Prevote("b", 0, MCValueA), "h3"))
  \/ MCTake(23, OnPrevoteQuorumValueFirstTime("h3"))

(***************************************************************************)
(* Scenario selection. Bracketed terminal stuttering makes each scripted   *)
(* prefix a complete bounded behavior. Weak fairness forces each enabled   *)
(* scripted action to run before that terminal state.                      *)
(***************************************************************************)
MCInit == Init /\ mcStep = 0

MCNext ==
  CASE MCScenario = "positive" -> MCPositiveNext
    [] MCScenario = "old-defect" -> MCOldDefectNext
    [] MCScenario = "phase2-entry" -> MCPhase2EntryNext
    [] MCScenario = "phase2-lock-shift" -> MCPhase2LockShiftNext
    [] MCScenario = "lock-retry" -> MCLockRetryNext
    [] MCScenario = "lock-relativize" -> MCLockRelativizeNext
    [] MCScenario = "window-gst" -> MCWindowGstNext
    [] OTHER -> FALSE

MCSpec == MCInit /\ [][MCNext]_mcVars /\ WF_mcVars(MCNext)

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)