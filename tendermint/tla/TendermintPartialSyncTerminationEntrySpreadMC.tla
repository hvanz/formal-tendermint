---------------- MODULE TendermintPartialSyncTerminationEntrySpreadMC ----------------
(***************************************************************************)
(* Entry-spread counterexample for clause (1) of Lemma 5.                  *)
(*                                                                         *)
(* The script reaches a round 1 that satisfies Lemma 5 hypothesis (1) in   *)
(* the form of the paper (t > GST), and the short timeout clauses          *)
(* TimeoutX(1) > 2 * Delta. All correct processes then precommit nil in    *)
(* round 1, so round 1 cannot decide.                                      *)
(*                                                                         *)
(* The cause is the entry spread. The round-0 certificate of h1 and h3 is  *)
(* sent before GST, so its deadline is GST + Delta, and h2 can receive it  *)
(* as late as now = GST + Delta = 8, and the script gives it at now = 7.   *)
(* With t > GST alone, only Delta + TimeoutPrecommit(0) bounds the entry   *)
(* spread of round 1, not Delta. In the trace, h1 and h3 enter round 1 at  *)
(* now = 7. Their propose timers expire at now = 12, before h2 enters      *)
(* round 1.                                                                *)
(*                                                                         *)
(* The late entry of Lemma5Hyp, now >= GST + TimeoutPrecommit(r - 1), is   *)
(* false at this entry, and MCLateEntryFalseAtEntry checks that. The long  *)
(* timeout clauses, which the deleted timeout margin assumptions gave, are *)
(* also false here.                                                        *)
(*                                                                         *)
(* Constants: Delta = 2, GST = 6, T0Propose = 1, T0Prevote = 1,            *)
(* T0Precommit = 6, TDelta = 4.                                            *)
(***************************************************************************)
EXTENDS TendermintPartialSync, TLC

CONSTANT a

VARIABLE mcStep

mcVars == <<vars, mcStep>>

MCValidators == {"h1", "h2", "h3", "b"}
MCFaulty     == {"b"}
MCValid(v)   == TRUE
MCNat        == 0..13

MCProposalMsg == [
  type       : {"Proposal"},
  sender     : Validators,
  round      : Rounds,
  value      : Values,
  validRound : {-1} \cup Rounds
]

\* Round 1 has a correct proposer. Every other round has the faulty one.
MCProposer == [r \in MCNat |-> IF r = 1 THEN "h2" ELSE "b"]

FirstToEnter(p, r) ==
  /\ enteredAt[p][r] = now
  /\ \A c \in Honest : round[c] <= r
  /\ \A c \in Honest : enteredAt[c][r] = OFF \/ enteredAt[c][r] >= now

LockDominance(r) ==
  \A c \in Honest : locked[c].round <= valid[Proposer[r]].round

\* Hypotheses (1), (2) and (3) in the form of the paper.
HypCommon(p, r) ==
  /\ now > GST
  /\ r > 0
  /\ FirstToEnter(p, r)
  /\ Proposer[r] \in Honest
  /\ LockDominance(r)

\* Clause (4) as Lemma5Timeouts states it.
ShortTimeouts(r) ==
  /\ TimeoutPropose(r)   > 2 * Delta
  /\ TimeoutPrevote(r)   > 2 * Delta
  /\ TimeoutPrecommit(r) > 2 * Delta

\* Clause (4) with the entry spread term, as the proof stated it with the
\* deleted timeout margin assumptions.
LongTimeouts(r) ==
  /\ TimeoutPropose(r)   > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrevote(r)   > 2 * Delta + TimeoutPrecommit(r - 1)
  /\ TimeoutPrecommit(r) > 2 * Delta

\* The late-entry conjunct of clause (1) in Lemma5Hyp.
LateEntry(p, r) == enteredAt[p][r] >= GST + TimeoutPrecommit(r - 1)

MCTake(n, A) ==
  /\ mcStep = n
  /\ A
  /\ mcStep' = n + 1

MCFaultySendsTo(m, c) ==
  /\ m \in Message
  /\ sentTime[m] = OFF
  /\ FaultyStep(m.sender)
  /\ sentTime'[m] = now
  /\ m \in rcvd'[c]

MCProposes(p, v) ==
  /\ Propose(p)
  /\ sentTime'[Proposal(p, round[p], v, valid[p].round)] = now

MCNext ==
  \* Round 0. The faulty proposer is silent.
  \/ MCTake(0, Tick)                                         \* now = 1
  \/ MCTake(1, OnTimeoutPropose("h1"))
  \/ MCTake(2, OnTimeoutPropose("h2"))
  \/ MCTake(3, OnTimeoutPropose("h3"))
  \/ MCTake(4, MCFaultySendsTo(Prevote("b", 0, nil), "h1"))
  \/ MCTake(5, Deliver("h1"))
  \/ MCTake(6, Deliver("h3"))
  \/ MCTake(7, OnPrevoteQuorumNil("h1"))
  \/ MCTake(8, OnPrevoteQuorumNil("h3"))
  \/ MCTake(9, MCFaultySendsTo(Precommit("b", 0, nil), "h1"))
  \/ MCTake(10, Deliver("h1"))
  \/ MCTake(11, Deliver("h3"))
  \* h1 and h3 have the round-0 certificate at now = 1, before GST.
  \/ MCTake(12, ScheduleTimeoutPrecommit("h1"))              \* deadline 7
  \/ MCTake(13, ScheduleTimeoutPrecommit("h3"))              \* deadline 7
  \* The script gives h2 nothing before now = 7.
  \/ MCTake(14, Tick)                                        \* now = 2
  \/ MCTake(15, Tick)
  \/ MCTake(16, Tick)
  \/ MCTake(17, Tick)
  \/ MCTake(18, Tick)
  \/ MCTake(19, Tick)                                        \* now = 7
  \* h1 is the first correct process in round 1, at t = 7 > GST.
  \/ MCTake(20, OnTimeoutPrecommit("h1"))
  \/ MCTake(21, OnTimeoutPrecommit("h3"))
  \/ MCTake(22, Deliver("h2"))
  \/ MCTake(23, OnPrevoteQuorumNil("h2"))
  \/ MCTake(24, ScheduleTimeoutPrecommit("h2"))              \* deadline 13
  \/ MCTake(25, Deliver("h1"))
  \/ MCTake(26, Deliver("h3"))
  \/ MCTake(27, Tick)                                        \* now = 8
  \/ MCTake(28, Tick)
  \/ MCTake(29, Tick)
  \/ MCTake(30, Tick)
  \/ MCTake(31, Tick)                                        \* now = 12
  \* The propose timers of h1 and h3 expire. h2 is still in round 0.
  \/ MCTake(32, OnTimeoutPropose("h1"))
  \/ MCTake(33, OnTimeoutPropose("h3"))
  \/ MCTake(34, MCFaultySendsTo(Prevote("b", 1, nil), "h1"))
  \/ MCTake(35, Deliver("h1"))
  \/ MCTake(36, Deliver("h3"))
  \/ MCTake(37, OnPrevoteQuorumNil("h1"))
  \/ MCTake(38, OnPrevoteQuorumNil("h3"))
  \/ MCTake(39, Deliver("h2"))
  \/ MCTake(40, SkipRound("h2", 1))
  \/ MCTake(41, MCProposes("h2", a))
  \/ MCTake(42, OnProposalNoPOL("h2"))
  \/ MCTake(43, OnPrevoteQuorumNil("h2"))

MCSpec == Init /\ mcStep = 0 /\ [][MCNext]_mcVars

\* ---- Checks at the entry of h1 into round 1 (after step 20) --------------
EntryState == mcStep = 21

\* The hypotheses of the paper hold, with the short clause (4).
MCPaperHypAtEntry ==
  EntryState => (HypCommon("h1", 1) /\ ShortTimeouts(1))

\* The long clause (4) is false: the propose and the prevote clauses fail.
MCLongTimeoutsFalseAtEntry ==
  EntryState =>
    /\ ~ LongTimeouts(1)
    /\ ~ (TimeoutPropose(1) > 2 * Delta + TimeoutPrecommit(0))
    /\ ~ (TimeoutPrevote(1) > 2 * Delta + TimeoutPrecommit(0))

\* The late-entry conjunct of Lemma5Hyp is false at this entry.
MCLateEntryFalseAtEntry ==
  EntryState => ~ LateEntry("h1", 1)

\* The proposer h2 is not in round 1 when the propose timer of h1 expires.
MCProposerLate ==
  mcStep = 33 => /\ round["h2"] = 0
                 /\ ~ \E m \in sent : m.type = "Proposal" /\ m.round = 1

\* ---- The failure --------------------------------------------------------
\* Every correct process precommitted nil in round 1. A round-1 decision
\* needs 2f+1 = 3 round-1 precommits for a value, so only b is left and
\* round 1 cannot decide. There is no value precommit, so there is no lock.
RoundOneFailed ==
  /\ mcStep = 44
  /\ \A h \in Honest : Precommit(h, 1, nil) \in sent
  /\ \A h \in Honest : decision[h] = nil
  /\ \A m \in sent : m.type = "Precommit" => m.valueID = nil

\* Expected to be VIOLATED: the violation trace is the counterexample.
MCRoundOneNotFailed == ~ RoundOneFailed
=============================================================================
\* Modification History
\* Last modified Sep 27 2026 by hvanz (Hernán Vanzetto)
\* Created Sep 26 2026 by hvanz (Hernán Vanzetto)