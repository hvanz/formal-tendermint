------------------- MODULE TendermintOperationalRefinement ------------------
(***************************************************************************)
(* Refinement of the leaderless-operational TendermintOperational.tla by   *)
(* the abstract TendermintVoting.tla.                                      *)
(*                                                                         *)
(* The refinement mapping is the identity on sent (proposals are kept,     *)
(* since the abstract spec carries a proposal layer) and keeps             *)
(* locked/decision as-is:                                                  *)
(*   sent <- sent (all three message types kept)                           *)
(*   locked <- locked                                                      *)
(*   decision <- decision                                                  *)
(* and the CONSTANTS (Validators, Values, Valid, Quorum) map by name. Both *)
(* specs are now leaderless (neither has a Proposer): the operational      *)
(* permissive Propose maps onto the abstract permissive V!Propose, and     *)
(* SkipRound onto stuttering.                                              *)
(*                                                                         *)
(* SELF-CONTAINED                                                          *)
(*   This module EXTENDS the spec TendermintOperational directly and       *)
(*   proves the three operational facts it needs -- TypeOK,                *)
(*   VoteStepProgress and NoPrevoteAtOrAboveOwnRoundInPropose -- locally   *)
(*   (the "bridge invariants" block below). All three are vote-based, so   *)
(*   they are untouched by how Propose chooses its value; a proposal-based *)
(*   fact such as proposal-uniqueness would instead be false here, Propose *)
(*   being leaderless.                                                     *)
(*                                                                         *)
(* WHAT A REFINEMENT PROOF IS FOR                                          *)
(*   A refinement proof shows every behavior of a detailed lower-level     *)
(*   spec is also a behavior of a simpler higher-level spec, under a       *)
(*   mapping from the detailed state onto the abstract state. The payoff   *)
(*   is property inheritance: a safety property proved of the abstract     *)
(*   spec holds of the detailed spec for free. A hard invariant is thus    *)
(*   proved once, on a small abstract model, and reused on the full        *)
(*   model, not reproved against all the lower-level machinery.            *)
(*                                                                         *)
(* MAIN RESULT                                                             *)
(*   THEOREM Refinement == Spec => V!Spec                                  *)
(*   i.e. every lower-level behavior is, under the mapping, a behavior of  *)
(*   the abstract voting spec. TendermintVotingProofs already proves       *)
(*   []Agreement on the abstract spec (its AgreementInv theorem). Since    *)
(*   Agreement mentions only decision (mapped by the identity), it carries *)
(*   back unchanged: lower-level Spec => []Agreement follows from this     *)
(*   Refinement by PTL, and is discharged below as the theorem             *)
(*   AgreementInv (V instances TendermintVotingProofs, so its              *)
(*   AgreementInv theorem is in scope).                                    *)
(*                                                                         *)
(* The lock-chain argument does NOT appear here; it lives in               *)
(* TendermintVotingProofs. This module only shows the lower-level actions  *)
(* respect the abstract guards -- the per-action simulation. The hard work *)
(* is reusing the lower-level invariant VoteStepProgress to discharge the  *)
(* abstract NoPrevoteAtOrAboveRound and NoPrecommitAtOrAboveRound guards.  *)
(***************************************************************************)

EXTENDS TendermintOperational

\* Always-expanded definitions the bridge-invariant proofs below rely on.
USE DEFS Proposal, Prevote, Precommit,
         SentProposals, SentPrevotes, SentPrecommits,
         ProposalsAt, PrevotesAt, PrecommitsAt

(***************************************************************************)
(* Bridge invariants.                                                      *)
(*                                                                         *)
(* TypeOK, VoteStepProgress and NoPrevoteAtOrAboveOwnRoundInPropose are    *)
(* the only operational facts this refinement needs. They are vote-based   *)
(* and so are untouched by the leaderless Propose; they are proved here so *)
(* this module is self-contained. The canonical Agreement route remains    *)
(* the refinement onto TendermintVoting below.                             *)
(***************************************************************************)

THEOREM TypeOKInv == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEFS Init, TypeOK, LockState, Step, Rounds, ValuesOrNil
<1>2. ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  <2>1. CASE Next
    <3> USE <1>2 DEFS TypeOK, Step, Rounds, Message, ProposalMsg, PrevoteMsg, PrecommitMsg, ValuesOrNil
    <3>1. ASSUME Propose
          PROVE  TypeOK'
      BY <3>1 DEFS Propose, LockState
    <3>3. ASSUME NEW p \in Validators, PrevoteNil(p)
          PROVE  TypeOK'
      BY <3>3 DEFS PrevoteNil
    <3>4. ASSUME NEW p \in Validators, OnProposalNoPOL(p)
          PROVE  TypeOK'
      BY <3>4 DEFS OnProposalNoPOL
    <3>5. ASSUME NEW p \in Validators, OnProposalWithPOL(p)
          PROVE  TypeOK'
      BY <3>5 DEFS OnProposalWithPOL
    <3>7. ASSUME NEW p \in Validators, OnPrevoteQuorumValueFirstTime(p)
          PROVE  TypeOK'
      BY <3>7 DEFS OnPrevoteQuorumValueFirstTime, LockState
    <3>8. ASSUME NEW p \in Validators, OnPrevoteQuorumValueLateUpdate(p)
          PROVE  TypeOK'
      BY <3>8 DEFS OnPrevoteQuorumValueLateUpdate, LockState
    <3>9. ASSUME NEW p \in Validators, OnPrevoteQuorumNil(p)
          PROVE  TypeOK'
      BY <3>9 DEFS OnPrevoteQuorumNil
    <3>10. ASSUME NEW p \in Validators, PrecommitNil(p)
           PROVE  TypeOK'
      BY <3>10 DEFS PrecommitNil
    <3>12. ASSUME NEW p \in Validators, OnPrecommitQuorumValue(p)
           PROVE  TypeOK'
      BY <3>12 DEFS OnPrecommitQuorumValue, ValuesOrNil
    <3>13. ASSUME NEW p \in Validators, AdvanceRound(p)
           PROVE  TypeOK'
      BY <3>13 DEFS AdvanceRound
    <3>14. ASSUME NEW p \in Validators, SkipRound(p)
           PROVE  TypeOK'
      BY <3>14 DEFS SkipRound
    <3>15. QED
      BY <2>1, <3>1, <3>3, <3>4, <3>5, <3>7, <3>8, <3>9, <3>10, <3>12, <3>13, <3>14 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <1>2, <2>2 DEFS TypeOK, vars
  <2>3. QED
    BY <1>2, <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

\* Invariant: Votes are never ahead of their sender's local round, and a
\* current-round vote implies the sender has advanced past the step that
\* emits it.
VoteStepProgress ==
  /\ \A m \in SentPrevotes :
        \/ m.round < round[m.sender]
        \/ /\ m.round = round[m.sender]
           /\ step[m.sender] \in {"prevote", "precommit", "decided"}
  /\ \A m \in SentPrecommits :
        \/ m.round < round[m.sender]
        \/ /\ m.round = round[m.sender]
           /\ step[m.sender] \in {"precommit", "decided"}

THEOREM VoteStepProgressInv == Spec => []VoteStepProgress
<1>1. Init => VoteStepProgress
  BY DEFS Init, VoteStepProgress
<1>2. ASSUME TypeOK, VoteStepProgress, [Next]_vars PROVE  VoteStepProgress'
  <2>1. CASE Next
    <3> USE <1>2 DEFS VoteStepProgress, TypeOK, Message, ProposalMsg, PrevoteMsg, PrecommitMsg, ValuesOrNil, Rounds, Step
    <3>1. ASSUME Propose
          PROVE  VoteStepProgress'
      BY <3>1 DEF Propose
    <3>3. ASSUME NEW p \in Validators, PrevoteNil(p)
          PROVE  VoteStepProgress'
      BY <3>3 DEFS PrevoteNil
    <3>4. ASSUME NEW p \in Validators, OnProposalNoPOL(p)
          PROVE  VoteStepProgress'
      BY <3>4 DEFS OnProposalNoPOL
    <3>5. ASSUME NEW p \in Validators, OnProposalWithPOL(p)
          PROVE  VoteStepProgress'
      BY <3>5 DEFS OnProposalWithPOL
    <3>7. ASSUME NEW p \in Validators, OnPrevoteQuorumValueFirstTime(p)
          PROVE  VoteStepProgress'
      BY <3>7 DEFS OnPrevoteQuorumValueFirstTime
    <3>8. ASSUME NEW p \in Validators, OnPrevoteQuorumValueLateUpdate(p)
          PROVE  VoteStepProgress'
      BY <3>8 DEF OnPrevoteQuorumValueLateUpdate
    <3>9. ASSUME NEW p \in Validators, OnPrevoteQuorumNil(p)
          PROVE  VoteStepProgress'
      BY <3>9 DEFS OnPrevoteQuorumNil
    <3>10. ASSUME NEW p \in Validators, PrecommitNil(p)
           PROVE  VoteStepProgress'
      BY <3>10 DEFS PrecommitNil
    <3>12. ASSUME NEW p \in Validators, OnPrecommitQuorumValue(p)
           PROVE  VoteStepProgress'
      BY <3>12 DEFS OnPrecommitQuorumValue
    <3>13. ASSUME NEW p \in Validators, AdvanceRound(p)
           PROVE  VoteStepProgress'
      BY <3>13 DEFS AdvanceRound
    <3>14. ASSUME NEW p \in Validators, SkipRound(p)
           PROVE  VoteStepProgress'
      BY <3>14 DEFS SkipRound
    <3>15. QED
      BY <2>1, <3>1, <3>3, <3>4, <3>5, <3>7, <3>8, <3>9, <3>10, <3>12, <3>13, <3>14 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <1>2, <2>2 DEFS VoteStepProgress, vars
  <2>3. QED
    BY <1>2, <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

\* Lemma: While a validator is still in propose, it cannot already have an
\* old prevote at its current round or a later round.
LEMMA NoPrevoteAtOrAboveOwnRoundInPropose ==
  ASSUME NEW p \in Validators, NEW v, NEW r \in Rounds,
         TypeOK,
         VoteStepProgress,
         step[p] = "propose",
         round[p] <= r
  PROVE  p \notin PrevoteSendersFor(v, r)
BY TypeOK, VoteStepProgress DEFS PrevoteSendersFor, VoteStepProgress, TypeOK, Rounds

(***************************************************************************)
(* The refinement mapping for sent: keep every message. Under TypeOK this  *)
(* equals sent (Message = Proposal \cup Prevote \cup Precommit), so the    *)
(* mapping is the identity; the explicit type filter keeps the projection  *)
(* lemmas below uniform with the other specs in the chain.                 *)
(***************************************************************************)
ProjSent == { m \in sent : m.type \in {"Proposal", "Prevote", "Precommit"} }

V == INSTANCE TendermintVotingProofs WITH sent <- ProjSent

(***************************************************************************)
(* Projection lemmas: the V!-operators over the projected sent coincide    *)
(* with the operational operators over the full sent. These let every      *)
(* action case reduce to operational facts already proven in this file.    *)
(*                                                                         *)
(* All are pure set theory over the definition of ProjSent and the fact    *)
(* that vote messages have type "Prevote"/"Precommit".                     *)
(***************************************************************************)

\* The projected prevote/precommit sets equal the operational ones: a
\* "Prevote" message survives the type-in-{Prevote,Precommit} filter, and
\* filtering it again by type = "Prevote" is the operational SentPrevotes.
LEMMA SentPrevotesProj == V!SentPrevotes = SentPrevotes
BY DEFS V!SentPrevotes, SentPrevotes, ProjSent

LEMMA SentPrecommitsProj == V!SentPrecommits = SentPrecommits
BY DEFS V!SentPrecommits, SentPrecommits, ProjSent

\* The projected proposal set equals the operational one (a "Proposal"
\* message survives the type-in-{Proposal,Prevote,Precommit} filter).
LEMMA SentProposalsProj == V!SentProposals = SentProposals
BY DEFS V!SentProposals, SentProposals, ProjSent

\* A proposal at round r (leaderless: from anyone) witnesses the abstract
\* gate V!ExistsProposal for that proposal's value: it is in the (kept)
\* projected proposal set, at round r. This discharges the gate conjunct
\* of V!PrevoteValue in the OnProposal* value-prevote cases below.
LEMMA ProposalWitnessesExists ==
  ASSUME NEW r, NEW prop \in ProposalsAt(r)
  PROVE  V!ExistsProposal(prop.value, r)
BY SentProposalsProj DEFS ProposalsAt, SentProposals, V!ExistsProposal

\* Hence the quorum-existence predicates coincide.
LEMMA ExistsPrevoteQuorumProj ==
  \A v, r : V!ExistsPrevoteQuorum(v, r) <=> ExistsPrevoteQuorum(v, r)
BY SentPrevotesProj DEFS V!ExistsPrevoteQuorum, ExistsPrevoteQuorum,
  V!PrevoteSendersFor, PrevoteSendersFor, V!PrevotesAt, PrevotesAt

LEMMA ExistsPrecommitQuorumProj ==
  \A v, r : V!ExistsPrecommitQuorum(v, r) <=> ExistsPrecommitQuorum(v, r)
BY SentPrecommitsProj DEFS V!ExistsPrecommitQuorum, ExistsPrecommitQuorum,
  V!PrecommitSendersFor, PrecommitSendersFor, V!PrecommitsAt, PrecommitsAt

(***************************************************************************)
(* The abstract NoPrecommitAtOrAboveRound guard: while a validator is in   *)
(* propose or prevote, VoteStepProgress rules out any precommit at its     *)
(* current round or a later round.                                         *)
(***************************************************************************)
LEMMA NoPrecommitAtOrAboveRoundInPropose ==
  ASSUME NEW p \in Validators, TypeOK, VoteStepProgress, step[p] = "propose"
  PROVE  V!NoPrecommitAtOrAboveRound(p, round[p])
BY SentPrecommitsProj, TypeOK, VoteStepProgress
DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, Rounds, SentPrecommits, 
  Step, TypeOK, V!NoPrecommitAtOrAboveRound, VoteStepProgress

LEMMA NoPrecommitAtOrAboveRoundInPrevote ==
  ASSUME NEW p \in Validators, TypeOK, VoteStepProgress, step[p] = "prevote"
  PROVE  V!NoPrecommitAtOrAboveRound(p, round[p])
BY SentPrecommitsProj, TypeOK, VoteStepProgress
DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, Rounds, SentPrecommits, 
  Step, TypeOK, V!NoPrecommitAtOrAboveRound, VoteStepProgress

LEMMA NoPrevoteAtOrAboveRoundInPropose ==
  ASSUME NEW p \in Validators, TypeOK, VoteStepProgress, step[p] = "propose"
  PROVE  V!NoPrevoteAtOrAboveRound(p, round[p])
BY SentPrevotesProj, TypeOK, VoteStepProgress
DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, Rounds, SentPrevotes, 
  Step, TypeOK, V!NoPrevoteAtOrAboveRound, VoteStepProgress

LEMMA NoHigherRoundPrevoteInPrevote ==
  ASSUME NEW p \in Validators, TypeOK, VoteStepProgress, step[p] = "prevote"
  PROVE  V!NoHigherRoundPrevote(p, round[p])
BY SentPrevotesProj, TypeOK, VoteStepProgress
DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, Rounds, SentPrevotes, 
  Step, TypeOK, V!NoHigherRoundPrevote, VoteStepProgress

\* The abstract message constructors equal the operational ones (same
\* records).
LEMMA PrevoteProj == \A a, b, c : V!Prevote(a, b, c) = Prevote(a, b, c)
BY DEFS V!Prevote, Prevote

LEMMA PrecommitProj == \A a, b, c : V!Precommit(a, b, c) = Precommit(a, b, c)
BY DEFS V!Precommit, Precommit

LEMMA ProposalProj == \A a, b, c : V!Proposal(a, b, c) = Proposal(a, b, c)
BY DEFS V!Proposal, Proposal

\* The abstract and operational nil are the same CHOOSE over the same Values.
LEMMA NilProj == V!nil = nil
BY DEFS V!nil, nil

(***************************************************************************)
(* The refinement theorem.                                                 *)
(***************************************************************************)
THEOREM Refinement == Spec => V!Spec
<1>1. Init => V!Init
  \* sent = {} projects to {}; locked/decision identical to V!Init.
  BY NilProj DEFS Init, V!Init, ProjSent
<1>2. ASSUME TypeOK, VoteStepProgress, [Next]_vars
      PROVE  [V!Next]_(V!vars)
  <2> USE DEF V!vars
  <2>1. CASE UNCHANGED vars
    \* sent unchanged => ProjSent unchanged => V!vars unchanged.
    BY <2>1 DEF vars, ProjSent
  <2>2. CASE Next
    <3> USE <1>2, <2>2, NilProj, PrevoteProj, PrecommitProj DEF V!Rounds, Rounds
    \* ---- Propose maps onto the abstract permissive V!Propose: it adds
    \* Proposal(r, v, vr) with r \in Rounds, v \in Values, vr \in Rounds \cup {-1},
    \* exactly a V!Propose witness, and leaves locked/decision unchanged. ----
    <3>1. ASSUME Propose PROVE [V!Next]_(V!vars)
      \* V!Next wraps V!Propose in \E p \in Validators (p is vacuous for a
      \* leaderless proposal), so a validator witness is needed.
      BY <3>1, ProposalProj, ValidatorsNonEmpty
      DEFS LockState, ProjSent, Proposal, Propose, TypeOK, V!Next, V!Propose, ValuesOrNil
    <3>8. ASSUME NEW p \in Validators, OnPrevoteQuorumValueLateUpdate(p)
          PROVE  [V!Next]_(V!vars)
      BY <3>8 DEF OnPrevoteQuorumValueLateUpdate, ProjSent
    <3>13. ASSUME NEW p \in Validators, AdvanceRound(p)
           PROVE [V!Next]_(V!vars)
      BY <3>13 DEF AdvanceRound, ProjSent
    <3>14. ASSUME NEW p \in Validators, SkipRound(p)
           PROVE  [V!Next]_(V!vars)
      BY <3>14 DEF SkipRound, ProjSent
    \* ---- Vote actions: exhibit the abstract witness. ----
    <3>12. ASSUME NEW p \in Validators, OnPrecommitQuorumValue(p)
           PROVE [V!Next]_(V!vars)
      BY <3>12, ExistsPrecommitQuorumProj
      DEFS Message, OnPrecommitQuorumValue, PrecommitMsg, PrevoteMsg, ProjSent, 
        ProposalMsg, ProposalsAt, SentProposals, TypeOK, V!Decide, V!Next
    <3> USE ExistsPrevoteQuorumProj, NoPrecommitAtOrAboveRoundInPrevote, 
          NoPrecommitAtOrAboveRoundInPropose, NoPrevoteAtOrAboveRoundInPropose, 
          NoHigherRoundPrevoteInPrevote, ProposalWitnessesExists
        DEFS TypeOK, ProjSent, PrecommitMsg, Prevote, Precommit, PrevoteMsg, 
          ProposalMsg, ProposalsAt, SentProposals, V!ExistsProposal, V!Next
    <3>3. ASSUME NEW p \in Validators, PrevoteNil(p)
          PROVE  [V!Next]_(V!vars)
      BY <3>3 DEFS PrevoteNil, Prevote, V!PrevoteNil, V!NoPrecommitAtOrAboveRound, V!NoPrevoteAtOrAboveRound
    \* The value branch prevotes prop.value; V!PrevoteValue's new gate
    \* V!ExistsProposal(prop.value, round[p]) is the proposal prop itself.
    <3>4. ASSUME NEW p \in Validators, OnProposalNoPOL(p)
          PROVE  [V!Next]_(V!vars)
      <4>1. \A prop \in ProposalsAt(round[p]) : V!ExistsProposal(prop.value, round[p])
        BY ProposalWitnessesExists
      <4>2. QED
        BY <3>4, <4>1 DEFS Message, OnProposalNoPOL, V!PrevoteNil, V!PrevoteValue, 
          V!NoPrecommitAtOrAboveRound, V!NoPrevoteAtOrAboveRound
    <3>5. ASSUME NEW p \in Validators, OnProposalWithPOL(p)
          PROVE  [V!Next]_(V!vars)
      <4>1. \A prop \in ProposalsAt(round[p]) : V!ExistsProposal(prop.value, round[p])
        BY ProposalWitnessesExists
      <4>2. QED
        BY <3>5, <4>1 DEFS Message, OnProposalWithPOL, Range, Rounds, V!PrevoteNil, 
          V!PrevoteValue, V!NoPrecommitAtOrAboveRound, V!NoPrevoteAtOrAboveRound
    <3>7. ASSUME NEW p \in Validators, OnPrevoteQuorumValueFirstTime(p)
          PROVE  [V!Next]_(V!vars)
      BY <3>7 DEFS Message, OnPrevoteQuorumValueFirstTime, V!PrecommitValue, 
        V!NoPrecommitAtOrAboveRound, V!NoHigherRoundPrevote
    <3>9. ASSUME NEW p \in Validators, OnPrevoteQuorumNil(p)
          PROVE  [V!Next]_(V!vars)
      BY <3>9 DEFS OnPrevoteQuorumNil, Precommit, V!PrecommitNil, V!NoPrecommitAtOrAboveRound, V!NoHigherRoundPrevote
    <3>10. ASSUME NEW p \in Validators, PrecommitNil(p)
           PROVE  [V!Next]_(V!vars)
      BY <3>10 DEFS PrecommitNil, Precommit, V!PrecommitNil, V!NoPrecommitAtOrAboveRound, V!NoHigherRoundPrevote
    <3>15. QED
      BY <3>1, <3>3, <3>4, <3>5, <3>7, <3>8, <3>9, <3>10, <3>12, <3>13, <3>14 DEF Next
  <2>3. QED
    BY <1>2, <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, VoteStepProgressInv, PTL DEF Spec, V!Spec

-----------------------------------------------------------------------------

(***************************************************************************)
(* End-to-end transfer: operational Agreement follows from the             *)
(* refinement plus the abstract AgreementInv. V!Agreement is the           *)
(* operational Agreement (mentions only decision, mapped by the            *)
(* identity; nil matches by NilProj), so []V!Agreement is []Agreement.     *)
(***************************************************************************)
THEOREM AgreementInv == Spec => []Agreement
<1>1. V!Spec => []V!Agreement
  BY V!AgreementInv, QuorumIntersection, QuorumType, ValidatorsNonEmpty, ValidIsBoolean, ValidNonEmpty, PTL
<1>2. Spec => []V!Agreement
  BY Refinement, <1>1, PTL
<1>3. QED
  BY <1>2, PTL DEF V!Agreement, Agreement, V!nil, nil

(***************************************************************************)
(* End-to-end transfer: operational Validity follows from the refinement   *)
(* plus the abstract ValidityInv. V!Validity is the operational Validity:  *)
(* it mentions only decision (mapped by the identity) and Valid (mapped by *)
(* name), with nil matching by NilProj, so []V!Validity is []Validity.     *)
(***************************************************************************)
THEOREM ValidityInv == Spec => []Validity
<1>1. V!Spec => []V!Validity
  BY V!ValidityInv, QuorumIntersection, QuorumType, ValidatorsNonEmpty, ValidIsBoolean, ValidNonEmpty, PTL
<1>2. Spec => []V!Validity
  BY Refinement, <1>1, PTL
<1>3. QED
  BY <1>2, PTL DEF V!Validity, Validity, V!nil, nil

(***************************************************************************)
(* End-to-end transfer: operational Integrity follows from the refinement  *)
(* plus the abstract IntegrityStepInv. IntegrityStep is an action property *)
(* relating decision to decision', both mapped by the identity (the        *)
(* projection touches only sent), with nil matching by NilProj, so         *)
(* []V!IntegrityStep is []IntegrityStep.                                   *)
(***************************************************************************)
THEOREM IntegrityInv == Spec => []IntegrityStep
<1>1. V!Spec => []V!IntegrityStep
  BY V!IntegrityStepInv, QuorumIntersection, QuorumType, ValidatorsNonEmpty, ValidIsBoolean, ValidNonEmpty, PTL
<1>2. Spec => []V!IntegrityStep
  BY Refinement, <1>1, PTL
<1>3. QED
  BY <1>2, PTL DEF V!IntegrityStep, IntegrityStep, V!nil, nil

=============================================================================
\* Modification History
\* Created Jun 7 2026 by hvanz (Hernán Vanzetto)