----------------------- MODULE TendermintOperationalMC ----------------------
(***************************************************************************)
(* Model module for TLC model-checking of TendermintOperational.tla at a   *)
(* BFT-shaped configuration.                                               *)
(*                                                                         *)
(* Sizing:                                                                 *)
(*   N = 4 validators (BFT minimum: 3f+1 = 4 with f = 1)                   *)
(*   V = 1 value                                                           *)
(*   MaxRound = 1                                                          *)
(*                                                                         *)
(* Companion file: TendermintOperationalMC.cfg                             *)
(*                                                                         *)
(* Quorum is the set of size-3 subsets (2f+1 = 3), matching the Tendermint *)
(* paper's BFT threshold.                                                  *)
(*                                                                         *)
(* WHAT THIS MODULE PROVIDES                                               *)
(* 1. Concrete instantiations of TendermintOperational.tla's five          *)
(*    CONSTANTS (Validators, Values, Valid, Quorum, nil). The spec is      *)
(*    leaderless (no Proposer).                                            *)
(* 2. MCRounds, an override target for the standard 'Nat'. The .cfg        *)
(*    substitutes Nat <- MCRounds, bounding every 'r \in Rounds'           *)
(*    quantifier in the spec.                                              *)
(* 3. MCInit, which pre-loads a constant proposal set, and MCNext, the     *)
(*    spec's Next without Propose (see the MCNext comment).                *)
(* 4. MCStateConstraint, keeps round[p] <= MaxRound.                       *)
(*                                                                         *)
(* Note that with V = 1 there is only one possible value to decide on, so  *)
(* the Agreement invariant is trivially satisfied. The model is useful     *)
(* for catching spec bugs (TypeOK violations, action UNCHANGED clauses,    *)
(* enabling conditions) at a BFT-shaped scale; for non-trivial Agreement   *)
(* verification a configuration with V >= 2 would be required.             *)
(***************************************************************************)

EXTENDS TendermintOperational, FiniteSets

(***************************************************************************)
(* Sizing                                                                  *)
(***************************************************************************)

MaxRound == 1

(***************************************************************************)
(* Concrete instantiations of TendermintOperational.tla's CONSTANTS.       *)
(* The .cfg substitutes each spec CONSTANT with the MC operator below.     *)
(***************************************************************************)

MCValidators == {"v1", "v2", "v3", "v4"}

MCValues == {"x"}

\* Every value in MCValues is application-valid.
MCValid(v) == TRUE

\* BFT supermajority for N=4, f=1: quorum = 2f + 1 = 3. Any two size-3
\* subsets of a 4-element set share at least 2 elements, so
\* QuorumIntersection holds.
MCQuorum == {S \in SUBSET MCValidators : Cardinality(S) >= 3}

(***************************************************************************)
(* Override target for Nat.                                                *)
(*                                                                         *)
(* The .cfg replaces the standard 'Nat' with 'MCRounds' via TLC's          *)
(* operator-override mechanism. This bounds every 'r \in Rounds' (=        *)
(* 'r \in Nat') quantifier in the spec at once, including the one inside   *)
(* OnPrecommitQuorumValue's body and the one in Next's SkipRound disjunct. *)
(*                                                                         *)
(* The set is widened by one beyond MaxRound so a transition that produces *)
(* round[p] = MaxRound + 1 (via AdvanceRound) is type-valid; the           *)
(* MCStateConstraint below stops TLC from exploring past MaxRound.         *)
(***************************************************************************)
MCRounds == 0..(MaxRound + 1)

(***************************************************************************)
(* Init and Next for model checking.                                       *)
(*                                                                         *)
(* The spec's leaderless Propose is always enabled and quantifies vr over  *)
(* Int; checking it directly at N=4 is intractable (TLC cannot enumerate   *)
(* Int, and even bounded it lets 'sent' range over every subset of the     *)
(* distinct proposal records, exploding the state space). Instead, as in   *)
(* TendermintVotingMC, pre-load a CONSTANT proposal set in MCInit -- one   *)
(* proposal for every (round, value, validRound) -- and omit Propose from  *)
(* MCNext. The proposal set is then fixed (no powerset blow-up), every     *)
(* proposal guard (fresh vr = -1 and Proof-of-Lock vr >= 0) can still      *)
(* fire, and Propose's own dynamics are covered by the TLAPS refinement,   *)
(* not TLC. Agreement/TypeOK over this fixed superset of proposals imply   *)
(* them for every reachable proposal subset under the real Next.           *)
(***************************************************************************)
MCValidRounds == -1..MaxRound

MCAllProposals == { Proposal(r, v, vr) : r \in Rounds, v \in Values, vr \in MCValidRounds }

MCInit ==
  /\ round    = [v \in Validators |-> 0]
  /\ step     = [v \in Validators |-> "propose"]
  /\ locked   = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ valid    = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Validators |-> nil]
  /\ sent     = MCAllProposals

MCNext ==
  \E p \in Validators:
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

(***************************************************************************)
(* State constraint                                                        *)
(***************************************************************************)
MCStateConstraint ==
  \A p \in Validators : round[p] <= MaxRound

============================================================================
\* Modification History
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)
