------------------------ MODULE TendermintByzantineMC -----------------------
(***************************************************************************)
(* Model module for TLC model-checking of TendermintByzantine.tla at a     *)
(* concrete BFT split, so honest-scoped Agreement is non-trivial under     *)
(* Byzantine behavior.                                                     *)
(*                                                                         *)
(* Sizing:                                                                 *)
(*   N = 4 validators, f = 1 faulty (BFT minimum 3f+1 = 4)                 *)
(*   Faulty = {v4}, Honest = {v1, v2, v3}                                  *)
(*   V = 2 values (so two distinct values *could* be decided)              *)
(*   MaxRound = 0 (single round): a tractable, EXHAUSTIVE Byzantine-safety *)
(*     smoke check -- can the faulty validator's equivocation make two     *)
(*     honest validators decide different values at round 0? It cannot, by *)
(*     ByzQuorum intersection (a decision needs a 2f+1 precommit quorum,   *)
(*     of                                                                  *)
(*     which >= f+1 are honest). The multi-round lock/PoL Byzantine safety *)
(*     is established for ALL rounds by the TLAPS refinement onto          *)
(*     TendermintVoting (TendermintByzantineRefinement.tla), not by TLC:   *)
(*     with faulty equivocation the multi-round state space is too large   *)
(*     to enumerate.                                                       *)
(*   ByzQuorum = size-3 sets (2f+1), WeakQuorum = size-2 sets (f+1)        *)
(*                                                                         *)
(* Companion file: TendermintByzantineMC.cfg                               *)
(*                                                                         *)
(* TAMING THE STATE SPACE                                                  *)
(*   The spec's FaultyStep is fully permissive (any well-typed message     *)
(*   with sender = the faulty validator). Restrictions keep TLC tractable  *)
(*   without weakening the Agreement check:                                *)
(* 1. The designated proposer at the reachable round 0 is the FAULTY       *)
(*    validator v4 (a Byzantine leader), and MCFaultyStep injects          *)
(*    equivocating PROPOSALS as well as prevotes / precommits. Honest      *)
(*    validators read ProposalsFromProposerAt(0) = v4's (possibly          *)
(*    conflicting) proposals and may prevote them; the check confirms a    *)
(*    Byzantine leader still cannot make two honest validators decide      *)
(*    different values.                                                    *)
(* 2. Faulty injections are confined to round 0 (where equivocation can    *)
(*    build conflicting quorums); honest validators run across rounds      *)
(*    0..MaxRound. The faulty validator EQUIVOCATES freely (conflicting    *)
(*    proposals/prevotes/precommits for different values in the same       *)
(*    round) -- the safety-critical Byzantine power. The fully permissive  *)
(*    FaultyStep at all rounds is covered by the TLAPS refinement, not     *)
(*    TLC: with faulty equivocation the multi-round state space is too     *)
(*    large to enumerate.                                                  *)
(***************************************************************************)

EXTENDS TendermintByzantine, FiniteSets, TLC

(***************************************************************************)
(* Sizing                                                                  *)
(***************************************************************************)
MaxRound == 0

(***************************************************************************)
(* Concrete instantiations of TendermintByzantine.tla's CONSTANTS.         *)
(***************************************************************************)
\* Validators and Faulty are concrete strings so MCProposer/MCFaulty can name
\* them. Values are supplied as MODEL VALUES by the .cfg (for value
\* symmetry).
MCValidators == {"v1", "v2", "v3", "v4"}
MCFaulty     == {"v4"}

\* Every value is application-valid in this model.
MCValid(v) == TRUE

\* The designated proposer is the FAULTY validator v4 (Byzantine leader).
\* Domain covers 0..(MaxRound+1) for AdvanceRound's round[p] + 1 to stay
\* type-valid. At the reachable round 0, Proposer[0] = v4 is faulty: it
\* injects (possibly equivocating) proposals via MCFaultyStep, and honest
\* validators read ProposalsFromProposerAt(0) = v4's proposals.
MCProposer == [r \in 0..(MaxRound + 1) |-> "v4"]

\* Byzantine quorum = 2f+1 = 3: any size-3 subset. Any two size-3 subsets of
\* the 4 validators share >= 2 elements, of which >= 1 is honest (only 1 is
\* faulty), so ByzQuorumIntersection holds.
MCByzQuorum == {S \in SUBSET MCValidators : Cardinality(S) >= 3}

\* Weak quorum = f+1 = 2: any size->=2 subset. Any size-2 subset has >= 1
\* honest element, so WeakQuorumHasHonest holds. (Upward-closed so that a
\* size-2 SkipRound witness is included.)
MCWeakQuorum == {S \in SUBSET MCValidators : Cardinality(S) >= 2}

(***************************************************************************)
(* Override target for Nat (bounds every 'r \in Rounds' quantifier), with  *)
(* the +1 widening for AdvanceRound; MCStateConstraint stops exploration    *)
(* past MaxRound.                                                          *)
(***************************************************************************)
MCRounds == 0..(MaxRound + 1)

(***************************************************************************)
(* Restricted faulty action (see header): equivocating PROPOSALS, prevotes *)
(* and precommits, all at round 0. As the round-0 proposer, v4 is a        *)
(* Byzantine leader; it may inject conflicting fresh proposals for         *)
(* different values, which honest validators read and may prevote. This    *)
(* keeps the model finite-state without weakening the Agreement check (a   *)
(* conflicting decision would still need conflicting precommit quorums,    *)
(* impossible by ByzQuorum intersection, no matter what the leader does).  *)
(***************************************************************************)
MCFaultyStep(p) ==
  /\ \/ \E v \in Values :                                  \* equivocating Byzantine-leader proposals
          sent' = sent \cup {Proposal(p, 0, v, -1)}
     \/ \E t \in {"Prevote", "Precommit"}, v \in ValuesOrNil :
          sent' = sent \cup {IF t = "Prevote" THEN Prevote(p, 0, v) ELSE Precommit(p, 0, v)}
  /\ UNCHANGED << round, step, locked, valid, decision >>

MCNext ==
  \/ \E p \in Honest:
       \/ Propose(p)
       \/ PrevoteNil(p)
       \/ OnProposalNoPOL(p)
       \/ OnProposalWithPOL(p)
       \/ OnPrevoteQuorumValueFirstTime(p)
       \/ OnPrevoteQuorumValueLateUpdate(p)
       \/ OnPrevoteQuorumNil(p)
       \/ PrecommitNil(p)
       \/ OnPrecommitQuorumValue(p)
       \/ AdvanceRound(p)
       \/ SkipRound(p)
  \/ \E p \in Faulty : MCFaultyStep(p)

(***************************************************************************)
(* State constraint: keep honest validators' rounds within MaxRound.       *)
(***************************************************************************)
MCStateConstraint ==
  \A p \in Honest : round[p] <= MaxRound

(***************************************************************************)
(* Symmetry reduction over values only. Validators are NOT permuted: the   *)
(* fixed Faulty set and the round-robin Proposer name specific validators.  *)
(***************************************************************************)
MCSymmetry == Permutations(Values)

============================================================================
\* Modification History
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)
