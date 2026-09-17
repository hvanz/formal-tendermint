------------- MODULE TendermintPartialSyncTerminationInterfaceMC -------------
(***************************************************************************)
(* Phase-0 diagnostics of the statements, for the repair of the            *)
(* termination interface.                                                  *)
(*                                                                         *)
(* The passing configuration follows only concrete subactions of Next. It  *)
(* reaches a positive Lemma-5 round, and then a Lemma-6 lock after GST,    *)
(* with the round frontier intact. The three companion *Counterexample.cfg *)
(* files are expected failures. They keep the defects that motivated the   *)
(* repaired interfaces, and they keep the expected violations out of the   *)
(* normal passing target.                                                  *)
(***************************************************************************)
EXTENDS TendermintPartialSync, TLC

CONSTANT MCScenario

VARIABLE mcStep

mcVars == <<vars, mcStep>>

MCValidators == {"v1", "v2", "v3", "v4"}
MCFaulty == {"v4"}
MCValid(v) == TRUE

MCNat == 0..12

MCProposalMsg == [
  type       : {"Proposal"},
  sender     : Validators,
  round      : Rounds,
  value      : Values,
  validRound : {-1} \cup Rounds
]

MCValueA == CHOOSE v \in Values : TRUE
MCValueB == CHOOSE v \in Values \ {MCValueA} : TRUE

MCVotedPrecommit(p, v, r) == Precommit(p, r, v) \in sent

MCFirstToEnter(p, r) ==
  /\ enteredAt[p][r] = now
  /\ \A c \in Honest : round[c] <= r
  /\ \A c \in Honest : enteredAt[c][r] = OFF \/ enteredAt[c][r] >= now

\* The selection milestone: the instant when a correct process first enters a
\* round, with every correct lock still strictly below it. The lock clause
\* excludes one unsound state. In that state several correct processes enter r
\* at one clock instant, and one of them has already locked AT r. No valid
\* argument about propagation can repair that state.
MCFreshEntry(r) ==
  /\ \E p \in Honest : MCFirstToEnter(p, r)
  /\ \A c \in Honest : locked[c].round < r

\* Round 0 is faulty-led so a timeout round can establish positive-round
\* reachability. Rounds 1..3 are honest-led. The pattern then repeats.
MCPositiveProposer ==
  [r \in MCNat |-> CASE r % 4 = 0 -> "v4"
                     [] r % 4 = 1 -> "v1"
                     [] r % 4 = 2 -> "v2"
                     [] OTHER     -> "v3"]

\* A constant honest proposer makes the old recurrence condition true while
\* the other honest validators never become proposer.
MCFixedHonestProposer == [r \in MCNat |-> "v1"]

\* The frontier counterexample uses an honest proposer at round 0 and a
\* faulty proposer at round 1, where one honest validator races ahead.
MCFrontierProposer ==
  [r \in MCNat |-> CASE r = 0 -> "v1"
                     [] r = 1 -> "v4"
                     [] r % 3 = 0 -> "v1"
                     [] r % 3 = 1 -> "v2"
                     [] OTHER     -> "v3"]

(***************************************************************************)
(* Proposed rigid conditions, copied here before Phase 1 lands them in the *)
(* specification.                                                          *)
(***************************************************************************)
MCLemma5Timeouts(r) ==
  /\ TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

MCLemma5Hyp(p, r) ==
  /\ now > GST
  /\ r > 0
  /\ MCFirstToEnter(p, r)
  /\ Proposer[r] \in Honest
  /\ \A c \in Honest : locked[c].round <= valid[Proposer[r]].round
  /\ MCLemma5Timeouts(r)

MCTimeoutsEventuallySufficient ==
  \E rMin \in Rounds :
    \A r \in Rounds :
      r >= rMin => MCLemma5Timeouts(r)

\* TLC cannot enumerate the unbounded EveryHonestProposesAgain formula.
\* This finite projection checks one full recurrence window after every
\* baseline in 0..3. MCPositiveProposer extends periodically to Nat.
MCEveryHonestProposesAgainWindow ==
  \A p \in Honest :
    \A rMin \in 0..3 :
      \E r \in 0..7 :
        r > rMin /\ Proposer[r] = p

MCPositiveTerminationConditions ==
  /\ MCTimeoutsEventuallySufficient
  /\ MCEveryHonestProposesAgainWindow

(***************************************************************************)
(* Proposed Lemma-6 interface, copied here for statement validation.       *)
(***************************************************************************)
MCRoundFrontier(r) ==
  \A c \in Honest : round[c] <= r

MCLemma6LockEvent(q, v, r, t0) ==
  /\ q \in Honest
  /\ v \in Values
  /\ r \in Rounds
  /\ t0 \in Nat
  /\ now = t0
  /\ now > GST
  /\ locked[q].value = v
  /\ locked[q].round = r
  /\ valid[q].value = v
  /\ valid[q].round = r
  /\ MCVotedPrecommit(q, v, r)
  /\ sentTime[Precommit(q, r, v)] = t0
  \* The proof interface quantifies vr over Int. TLC uses the exact finite
  \* reachable proposal range installed by MCProposalMsg.
  /\ \E vr \in {-1} \cup Rounds :
       Proposal(Proposer[r], r, v, vr) \in rcvd[q]
  /\ RExistsPrevoteQuorum(q, v, r)

MCLemma6Hyp(q, v, r, t0) ==
  /\ MCLemma6LockEvent(q, v, r, t0)
  /\ MCRoundFrontier(r)
  /\ TimeoutPrecommit(r) > 2 * Delta

(***************************************************************************)
(* Script helpers. Every scripted transition of the state is a concrete    *)
(* subaction of the real Next relation of the protocol.                    *)
(***************************************************************************)
MCTake(n, A) ==
  /\ mcStep = n
  /\ A
  /\ mcStep' = n + 1

MCHonestProposes(p, v) ==
  /\ v \in Values
  /\ Propose(p)
  /\ sentTime'[Proposal(p, round[p], v, valid[p].round)] = now

MCFaultySends(m) ==
  /\ m \in Message
  /\ m.sender \in Faulty
  /\ sentTime[m] = OFF
  /\ FaultyStep(m.sender)
  /\ sentTime'[m] = now

\* FaultyStep both activates m AND gives it to ONE honest validator that the
\* adversary chooses. MCFaultySends therefore leaves that recipient free, and
\* TLC explores every choice. A scripted scenario that needs a specific
\* recipient must pin it. A free recipient let one recipient reach a prevote
\* quorum early. That enabled CanCompute for that validator, and the
\* maximal-progress guard of Tick then disabled the next Tick of the script.
MCFaultySendsTo(m, c) == MCFaultySends(m) /\ m \in rcvd'[c]

(***************************************************************************)
(* Passing path. A faulty round 0 times out. v1 is the first into round 1, *)
(* at now = 8, which satisfies Lemma5Hyp. All honest validators then enter *)
(* round 1. v1 proposes MCValueA and locks it at now = 9, with             *)
(* RoundFrontier(1).                                                       *)
(***************************************************************************)
MCPositiveNext ==
  \/ MCTake(0, Tick)
  \/ MCTake(1, Tick)
  \/ MCTake(2, Tick)
  \/ MCTake(3, Tick)
  \/ MCTake(4, Tick)
  \/ MCTake(5, OnTimeoutPropose("v1"))
  \/ MCTake(6, OnTimeoutPropose("v2"))
  \/ MCTake(7, OnTimeoutPropose("v3"))
  \/ MCTake(8, Deliver("v1"))
  \/ MCTake(9, Deliver("v2"))
  \/ MCTake(10, Deliver("v3"))
  \/ MCTake(11, OnPrevoteQuorumNil("v1"))
  \/ MCTake(12, OnPrevoteQuorumNil("v2"))
  \/ MCTake(13, OnPrevoteQuorumNil("v3"))
  \/ MCTake(14, Deliver("v1"))
  \/ MCTake(15, Deliver("v2"))
  \/ MCTake(16, Deliver("v3"))
  \/ MCTake(17, ScheduleTimeoutPrecommit("v1"))
  \/ MCTake(18, ScheduleTimeoutPrecommit("v2"))
  \/ MCTake(19, ScheduleTimeoutPrecommit("v3"))
  \/ MCTake(20, Tick)
  \/ MCTake(21, Tick)
  \/ MCTake(22, Tick)
  \/ MCTake(23, OnTimeoutPrecommit("v1"))
  \/ MCTake(24, OnTimeoutPrecommit("v2"))
  \/ MCTake(25, OnTimeoutPrecommit("v3"))
  \/ MCTake(26, MCHonestProposes("v1", MCValueA))
  \/ MCTake(27, OnProposalNoPOL("v1"))
  \/ MCTake(28, Deliver("v2"))
  \/ MCTake(29, OnProposalNoPOL("v2"))
  \/ MCTake(30, MCFaultySendsTo(Prevote("v4", 1, MCValueA), "v1"))
  \/ MCTake(31, Tick)
  \/ MCTake(32, Deliver("v1"))
  \/ MCTake(33, OnPrevoteQuorumValueFirstTime("v1"))

MCPositiveReachability ==
  /\ <>MCLemma5Hyp("v1", 1)
  /\ <>MCFreshEntry(1)
  /\ <>MCLemma6Hyp("v1", MCValueA, 1, now)

(***************************************************************************)
(* Prefix of the short-timeout counterexample. The propose timer of honest *)
(* round 0 fires at now = T0Propose = 3, before the proposal reaches v2    *)
(* and v3. Both therefore prevote nil, and the round ends with nil         *)
(* precommits only and with no decision. The delivery deadline GST + Delta *)
(* bounds the length of the Tick chain, which is why this configuration    *)
(* needs Delta = 4. See the header of the .cfg file for the derivation.    *)
(***************************************************************************)
MCShortTimeoutNext ==
  \/ MCTake(0, MCHonestProposes("v1", MCValueA))
  \/ MCTake(1, OnProposalNoPOL("v1"))
  \/ MCTake(2, Tick)
  \/ MCTake(3, Tick)
  \/ MCTake(4, Tick)
  \/ MCTake(5, OnTimeoutPropose("v2"))
  \/ MCTake(6, OnTimeoutPropose("v3"))
  \/ MCTake(7, Deliver("v1"))
  \/ MCTake(8, Deliver("v2"))
  \/ MCTake(9, Deliver("v3"))
  \/ MCTake(10, ScheduleTimeoutPrevote("v1"))
  \/ MCTake(11, ScheduleTimeoutPrevote("v2"))
  \/ MCTake(12, ScheduleTimeoutPrevote("v3"))
  \/ MCTake(13, Tick)
  \/ MCTake(14, OnTimeoutPrevote("v1"))
  \/ MCTake(15, OnTimeoutPrevote("v2"))
  \/ MCTake(16, OnTimeoutPrevote("v3"))
  \/ MCTake(17, Deliver("v1"))
  \/ MCTake(18, Deliver("v2"))
  \/ MCTake(19, Deliver("v3"))
  \/ MCTake(20, ScheduleTimeoutPrecommit("v1"))
  \/ MCTake(21, ScheduleTimeoutPrecommit("v2"))
  \/ MCTake(22, ScheduleTimeoutPrecommit("v3"))
  \/ MCTake(23, Tick)
  \/ MCTake(24, OnTimeoutPrecommit("v1"))
  \/ MCTake(25, OnTimeoutPrecommit("v2"))
  \/ MCTake(26, OnTimeoutPrecommit("v3"))

MCShortTimeoutRoundFailed ==
  /\ mcStep = 27
  /\ \A c \in Honest : round[c] = 1
  /\ \A c \in Honest : decision[c] = nil
  /\ ~MCLemma5Timeouts(1)

MCShortTimeoutReachability == <>MCShortTimeoutRoundFailed

(***************************************************************************)
(*  Frontier counterexample. v2 and v3 precommit nil after a mixed prevote *)
(*  quorum. v2 reaches round 1 before GST. v1 then receives a value quorum *)
(*  of round 0, and it locks MCValueA after GST. A Byzantine validator has *)
(*  sent conflicting prevotes for both values, and round 1 has a faulty    *)
(*  proposer. MCLockWithoutFrontier needs TimeoutPrecommit(0) > 2*Delta,   *)
(*  so T0Precommit = 5 here. The precommit timer of v2 then fires at now = *)
(*  7, which takes five Ticks. No Tick follows the lock. The prevote of    *)
(*  round 0 that is still pending for v1 has the deadline GST + Delta = 8. *)
(*  The value now = 7 is therefore the last one that the Gossip guard      *)
(*  permits.                                                               *)
(***************************************************************************)
MCFrontierNext ==
  \/ MCTake(0, MCHonestProposes("v1", MCValueA))
  \/ MCTake(1, OnProposalNoPOL("v1"))
  \/ MCTake(2, Deliver("v3"))
  \/ MCTake(3, OnProposalNoPOL("v3"))
  \/ MCTake(4, Tick)
  \/ MCTake(5, OnTimeoutPropose("v2"))
  \/ MCTake(6, Deliver("v2"))
  \/ MCTake(7, Deliver("v3"))
  \/ MCTake(8, ScheduleTimeoutPrevote("v2"))
  \/ MCTake(9, ScheduleTimeoutPrevote("v3"))
  \/ MCTake(10, Tick)
  \/ MCTake(11, OnTimeoutPrevote("v2"))
  \/ MCTake(12, OnTimeoutPrevote("v3"))
  \/ MCTake(13, MCFaultySends(Precommit("v4", 0, nil)))
  \/ MCTake(14, Deliver("v2"))
  \/ MCTake(15, ScheduleTimeoutPrecommit("v2"))
  \/ MCTake(16, Tick)
  \/ MCTake(17, Tick)
  \/ MCTake(18, Tick)
  \/ MCTake(19, Tick)
  \/ MCTake(20, Tick)
  \/ MCTake(21, OnTimeoutPrecommit("v2"))
  \/ MCTake(22, MCFaultySends(Prevote("v4", 0, MCValueA)))
  \/ MCTake(23, MCFaultySends(Prevote("v4", 0, MCValueB)))
  \/ MCTake(24, Deliver("v1"))
  \/ MCTake(25, OnPrevoteQuorumValueFirstTime("v1"))

MCLockWithoutFrontier ==
  /\ MCLemma6LockEvent("v1", MCValueA, 0, now)
  /\ TimeoutPrecommit(0) > 2 * Delta
  /\ ~MCRoundFrontier(0)

MCSelectedLockHasRoundFrontier == ~MCLockWithoutFrontier

(***************************************************************************)
(* Scenario selection. The bracketed specification permits terminal        *)
(* stuttering, so reachability properties can be checked on the finite     *)
(* scripted prefix.                                                        *)
(***************************************************************************)
MCInit == Init /\ mcStep = 0

MCNext ==
  CASE MCScenario = "positive"      -> MCPositiveNext
    [] MCScenario = "short-timeout" -> MCShortTimeoutNext
    [] MCScenario = "frontier"      -> MCFrontierNext
    [] OTHER                         -> FALSE

MCSpec == MCInit /\ [][MCNext]_mcVars /\ WF_mcVars(MCNext)

\* The exact old condition and the old property are kept for the
\* configurations of the expected counterexamples, after the change of the
\* public Termination interface.
MCOldCorrectProposerRecurs ==
  []<>(\E p \in Honest : Proposer[round[p]] \in Honest)

MCOldTermination ==
  MCOldCorrectProposerRecurs =>
    (\A p \in Honest : <>(decision[p] # nil))

\* Compare the old weak-proposer condition with the bounded projection of
\* the selected-process condition.
MCProposerStrengthening ==
  MCOldCorrectProposerRecurs => MCEveryHonestProposesAgainWindow

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)