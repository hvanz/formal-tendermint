----------------------- MODULE TendermintPartialSyncMC -----------------------
(***************************************************************************)
(* Model module for TLC model-checking of TendermintPartialSync.tla.       *)
(* It verifies a finite, nonvacuous projection of the conditional          *)
(* Termination property under fairness, plus the safety invariants. The    *)
(* unbounded EveryHonestProposesAgain condition cannot hold when Nat is    *)
(* overridden by a finite set with a maximum round.                        *)
(*                                                                         *)
(* Sizing:                                                                 *)
(*   f = 1, N = 3f+1 = 4 validators {v1, v2, v3, v4}                       *)
(*   Faulty = {} (the honest algorithm-with-timers; see ../README.md).     *)
(*   V = 1 value: no lock conflicts, so every honest validator prevotes    *)
(*     the proposer's value -- the cleanest check that the                 *)
(*     concrete-quorum + fairness plumbing yields a decision.              *)
(*   ByzQuorum = size->=3 sets (2f+1), WeakQuorum = size->=2 sets (f+1),   *)
(*     both DEFINED in TendermintPartialSync from f and Cardinality.       *)
(*                                                                         *)
(* TIMING PARAMETERS (GST = 0, Delta = 2, T0Propose = 7,                   *)
(* T0Prevote = T0Precommit = 5, TDelta = 1):                               *)
(*   GST = 0 means SYNCHRONOUS FROM THE START: every message sent at time  *)
(*   t has deadline t + 2. A Tick needs now + 1 < t + 2, so the message    *)
(*   arrives by now = t + 1. The round-0 proposal arrives by now = 1, the  *)
(*   prevotes by now = 2 and the precommits by now = 3. The propose        *)
(*   timeout fires at now = 7. So every honest validator decides in the    *)
(*   first round. TLC stopped on a full disk after 3 h 55 min with 4       *)
(*   workers. It found no violation in 369,406 distinct states. The check  *)
(*   is not exhaustive: 209,519 states were still in the queue.            *)
(*   This model does not check a GST > 0 recovery case, where the first    *)
(*   round fails before GST and a later round decides after GST. The       *)
(*   recovery constants of earlier versions used Delta = 1, which          *)
(*   DeltaType does not permit.                                            *)
(*                                                                         *)
(* BOUNDS / SOUNDNESS:                                                     *)
(*   Nat <- MCNat bounds every 'r \in Rounds' quantifier AND the clock     *)
(*   `now`. The clock stays small because Tick is gated by TickUseful      *)
(*   (no pointless ticking) and maximal progress; rounds stay at 0 here    *)
(*   (no timeout fires). MCNat = 0..7 contains the clock values 0..3.      *)
(*   NO state constraint and NO symmetry (both unsound for liveness).      *)
(*   No faulty activity: faulty messages can only help quorums form, so    *)
(*   omitting them is the worst case for liveness. Byzantine SAFETY is     *)
(*   TendermintByzantineMC's job.                                          *)
(*   SPECIFICATION MCLiveSpec (with fairness), not INIT/NEXT.              *)
(*                                                                         *)
(* Companion file: TendermintPartialSyncMC.cfg                             *)
(***************************************************************************)

EXTENDS TendermintPartialSync, FiniteSets, TLC

(***************************************************************************)
(* Concrete instantiations of TendermintPartialSync.tla's CONSTANTS.       *)
(***************************************************************************)
MCValidators == {"v1", "v2", "v3", "v4"}
MCFaulty     == {}
MCValid(v)   == TRUE

\* ---- Finite Message for TLC --------------------------------------------
\* TendermintPartialSync's ProposalMsg has validRound : Int, so Message is
\* infinite and sentTime / sent cannot be enumerated. Bound validRound to
\* {-1} \cup Rounds (every reachable proposal carries either -1 or a real
\* round as its validRound), making Message finite. Overridden in the .cfg
\* via `ProposalMsg <- MCProposalMsg`. PrevoteMsg / PrecommitMsg are already
\* finite (valueID : ValuesOrNil, round : Rounds).
MCProposalMsg == [
  type       : {"Proposal"},
  sender     : Validators,
  round      : Rounds,
  value      : Values,
  validRound : {-1} \cup Rounds
]

\* Bounds Rounds quantifiers, the clock `now` AND validRound's range (via
\* MCProposalMsg). Nat <- MCNat also constrains the timing constants, so
\* MCNat must contain the base timeouts 7, 5, and 5 (else an ASSUME T0XType
\* is false). In the GST=0 synchronous case every honest validator decides
\* in round 0 by now = 3, before any timeout (see the header). So the clock
\* stays in 0..3 and rounds stay 0. 0..7 covers the base timeouts and keeps
\* Message small.
MCNat == 0..7

\* Round-robin over all validators (all honest since Faulty = {}).
\* Domain = MCNat so Proposer \in [Nat -> Validators] holds under the override.
MCProposer == [r \in MCNat |-> CASE r % 4 = 0 -> "v1"
                                 [] r % 4 = 1 -> "v2"
                                 [] r % 4 = 2 -> "v3"
                                 [] OTHER     -> "v4"]

\* Finite projection of EveryHonestProposesAgain. Baselines stop early
\* enough to leave one complete round-robin proposer window in MCNat.
MCEveryHonestProposesAgain ==
  \A p \in Honest :
    \A rMin \in 0..3 :
      \E r \in Rounds :
        r > rMin /\ Proposer[r] = p

MCTerminationConditions == MCEveryHonestProposesAgain

MCTermination ==
  MCTerminationConditions =>
    (\A p \in Honest : <>(decision[p] # nil))

(***************************************************************************)
(* MCNext/MCLiveSpec: honest actions + Tick; no faulty activity (see       *)
(* header). Reuses the spec's HonestNext (= HonestStep \/ Deliver), Tick,  *)
(* and Fairness verbatim; only the faulty disjunct of Next is dropped.     *)
(***************************************************************************)
MCNext ==
  \/ \E p \in Honest : HonestNext(p)
  \/ Tick

MCLiveSpec == Init /\ [][MCNext]_vars /\ Fairness

=============================================================================
\* Modification History
\* Last modified Sep 27 2026 by hvanz (Hernán Vanzetto)
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)