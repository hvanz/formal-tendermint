------------------------ MODULE TendermintVotingMC --------------------------
(***************************************************************************)
(* Model module for TLC model-checking of TendermintVoting.tla at a        *)
(* BFT-shaped configuration with two values, so Agreement is non-trivial.  *)
(*                                                                         *)
(* Sizing:                                                                 *)
(*   N = 4 validators (BFT minimum: 3f+1 = 4 with f = 1)                   *)
(*   V = 2 values (so two distinct values *could* be decided)              *)
(*   MaxRound = 1 (enough to exercise the cross-round lock/PoL logic)      *)
(*                                                                         *)
(* Companion file: TendermintVotingMC.cfg                                  *)
(*                                                                         *)
(* Quorum is the set of size-3 subsets (2f+1 = 3). Any two size-3 subsets  *)
(* of a 4-element set share at least 2 elements, so QuorumIntersection     *)
(* holds. There is no Proposer (the abstract spec has no proposals and no  *)
(* SkipRound).                                                             *)
(*                                                                         *)
(* With V = 2, this model genuinely exercises Agreement: a counterexample  *)
(* would need a                                                            *)
(* decision for x and a decision for y. The abstract spec's guards         *)
(* (one vote per round, polka-before-precommit, the PoL unlock rule)       *)
(* should make that unreachable.                                           *)
(***************************************************************************)

EXTENDS TendermintVoting, FiniteSets, TLC

MaxRound == 1

(***************************************************************************)
(* Concrete instantiations of TendermintVoting.tla's CONSTANTS.            *)
(***************************************************************************)
\* Validators and Values are supplied as MODEL VALUES by the .cfg (required
\* for symmetry reduction via Permutations), so they are not defined here.
\* Every value is application-valid in this model.
MCValid(v) == TRUE

\* BFT supermajority for N=4, f=1: quorum = 2f + 1 = 3. Any two size-3
\* subsets of a 4-element set share at least 2 elements, so
\* QuorumIntersection holds.
MCQuorum == {S \in SUBSET Validators : Cardinality(S) >= 3}

(***************************************************************************)
(* Override target for Nat. The .cfg replaces 'Nat' with 'MCRounds',       *)
(* bounding every 'r \in Rounds' quantifier (in Next, in Decide, and the   *)
(* PoL existential inside CastPrevoteValue). No +1 widening is needed: the *)
(* abstract spec never produces round[p] + 1 (there is no AdvanceRound     *)
(* and no per-validator round variable).                                   *)
(***************************************************************************)
MCRounds == 0..MaxRound

(***************************************************************************)
(* Init and Next for model checking the new proposal layer.                *)
(*                                                                         *)
(* The spec's Propose is fully permissive and sender-agnostic (any value,  *)
(* any validRound) so both lower specs can map their proposals onto it.    *)
(* Model-checking it directly is ruinous: Propose is always enabled, so    *)
(* 'sent' would range over every subset of the 2 * 3 distinct proposal     *)
(* records for no new Agreement behavior, since the only guard that reads  *)
(* proposals (ExistsProposal) inspects just (value, round) and is          *)
(* monotone.                                                               *)
(*                                                                         *)
(* Instead, observe that ExistsProposal only RESTRICTS prevotes, so the    *)
(* worst case for Agreement is "every value proposed at every round". We   *)
(* pre-load exactly that in MCInit: one canonical proposal (validRound =   *)
(* -1) for every (round, value). The proposal set is then CONSTANT         *)
(* (no Propose action in MCNext, no state-space growth) and permutation-   *)
(* invariant (so both validator- and value-symmetry are retained). Every   *)
(* ExistsProposal(v, r) is true from the outset, so the vote/lock dynamics *)
(* are exactly the gate-free original and Agreement holding here implies   *)
(* it holds for every reachable proposal subset under the real Next. The   *)
(* Propose action's own dynamics are covered by the TLAPS proof, not TLC.  *)
(***************************************************************************)
MCAllProposals ==
  { Proposal(r, v, -1) : r \in Rounds, v \in Values }

MCInit ==
  /\ sent     = MCAllProposals
  /\ locked   = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Validators |-> nil]

MCNext ==
  \E p \in Validators :
    \/ \E r \in Rounds : PrevoteNil(p, r)
    \/ \E r \in Rounds : PrevoteValue(p, r)
    \/ \E r \in Rounds : PrecommitNil(p, r)
    \/ \E r \in Rounds : PrecommitValue(p, r)
    \/ Decide(p)

(***************************************************************************)
(* Symmetry reduction. Validators are interchangeable, and so are the      *)
(* (non-nil) values; MCInit's proposal set, the checked invariants         *)
(* (TypeOK, Agreement, Validity), and MCNext never name a specific         *)
(* validator or value, so quotienting by these permutations is sound. This *)
(* cuts the reachable state space by up to 4! * 2! = 48.                   *)
(***************************************************************************)
MCSymmetry == Permutations(Validators) \cup Permutations(Values)

============================================================================
\* Modification History
\* Created Jun 7 2026 by hvanz (Hernán Vanzetto)