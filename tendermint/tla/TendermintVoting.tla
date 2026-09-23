-------------------------- MODULE TendermintVoting --------------------------
(***************************************************************************)
(* Abstract "voting" spec of Tendermint single-height consensus. It is     *)
(* the top of the linear refinement chain                                  *)
(*   TendermintVoting <- TendermintOperational <- TendermintByzantine <-   *)
(*   TendermintPartialSync.                                                *)
(* (B <- A reads "B refines A".) The spec exists to carry a short TLAPS    *)
(* proof of the safety properties (Agreement, Validity) that               *)
(* the lower specs then inherit by refinement. It follows Lamport's        *)
(* voting refinement pattern used in his Paxos spec.                       *)
(*                                                                         *)
(* STATE (minimal; a validator's progress is read off sent, not a          *)
(* round/step counter)                                                     *)
(*   sent      SUBSET Message: every broadcast proposal, prevote and       *)
(*             precommit. It only grows.                                   *)
(*   locked    [Validators -> LockState]: each validator's (value,         *)
(*             round) lock; [nil, -1] means unlocked.                      *)
(*   decision  [Validators -> ValuesOrNil]: each decided value; nil        *)
(*             means undecided.                                            *)
(* There is no round, step, timer, valid record or Proposer function.      *)
(*                                                                         *)
(* MESSAGES                                                                *)
(*   Proposal, Prevote and Precommit, all collected in the single pool     *)
(*   sent. A proposal is sender-agnostic (leaderless).                     *)
(*                                                                         *)
(* ACTIONS (each guarded; each appends one message to sent, or decides)    *)
(*   Propose         propose any value at any round.                       *)
(*   PrevoteNil      prevote nil.                                          *)
(*   PrevoteValue    prevote a proposed, valid value, under the locking    *)
(*                   / proof-of-lock rule.                                 *)
(*   PrecommitNil    precommit nil.                                        *)
(*   PrecommitValue  precommit a value on a polka for it, and lock it.     *)
(*   Decide          decide a value that has a precommit quorum.           *)
(* The Tendermint discipline is enforced by DIRECT GUARDS over sent:       *)
(* one vote per round per validator, polka-before-precommit, and the       *)
(* coupling of locking to precommit-for-value.                             *)
(*                                                                         *)
(* PROPOSALS (leaderless and fully permissive)                             *)
(*   Propose lets ANY validator propose ANY value at ANY round.            *)
(*   PrevoteValue may only prevote a value that some proposal carried at   *)
(*   that round (ExistsProposal). The lock chain, and hence Agreement,     *)
(*   rests only on prevote / precommit quorums, never on who proposed.     *)
(*   Gating prevotes on proposals only removes behaviors.                  *)
(*                                                                         *)
(* PROOF OF LOCK                                                           *)
(*   The third disjunct of PrevoteValue is the proof-of-lock unlock rule   *)
(*   (folded from validRound): a validator locked on v may prevote w       *)
(*   after it sees a lower polka for w. It is a liveness mechanism, but    *)
(*   it is what forces the lock-chain argument behind Agreement.           *)
(*                                                                         *)
(* QUORUMS (symbolic)                                                      *)
(*   Quorum is abstract. The proofs use only QuorumIntersection: any two   *)
(*   quorums share a validator. There is no cardinality and no n = 3f+1.   *)
(*   The model is all-honest; BFT quorum sizes are only the intended       *)
(*   concrete instantiation supplied by the .cfg files.                    *)
(*                                                                         *)
(* SCOPE                                                                   *)
(*   Single height. All validators honest. Rounds unbounded (Nat).         *)
(*   Asynchronous: no clocks, no timers, no fairness, no liveness.         *)
(*   Pure safety form Spec == Init /\ [][Next]_vars.                       *)
(*                                                                         *)
(* WHY IT IS DELIBERATELY NONDETERMINISTIC                                 *)
(*   A validator may vote at any round without "being in" it, and any      *)
(*   validator may propose any value at any round. Refinement needs the    *)
(*   abstract spec to admit at least every concrete behavior, so           *)
(*   Agreement over this larger set is strictly stronger and transfers     *)
(*   down.                                                                 *)
(***************************************************************************)

EXTENDS Integers, TLAPS

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
  Validators,   \* the (non-empty) set of validators
  Values,       \* the set of values; excludes nil
  Valid(_),     \* validity predicate on Values (application-supplied)
  Quorum        \* set of validator-subsets large enough to decide; abstract,
                \* characterized only by QuorumIntersection (any two quorums
                \* share a validator), never by a cardinality.

(***************************************************************************)
(* Assumptions on the constants                                            *)
(***************************************************************************)
ASSUME ValidatorsNonEmpty == Validators # {}
ASSUME ValidIsBoolean     == \A v \in Values : Valid(v) \in BOOLEAN
ASSUME ValidNonEmpty      == \E v \in Values : Valid(v)

\* The only facts the proofs use about Quorum: no cardinality, no faulty
\* count, no n = 3f+1. This model is all-honest; the BFT quorum sizes are
\* merely the intended concrete instantiation supplied by the .cfg files.
ASSUME QuorumType         == Quorum \in SUBSET (SUBSET Validators)
ASSUME QuorumIntersection == \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

(***************************************************************************)
(* Types and operators                                                     *)
(***************************************************************************)
\* An unspecified, sentinel value that is distinct from every element of Values.
nil == CHOOSE v: v \notin Values

\* The set of all non-nil values plus the special nil value.
ValuesOrNil == Values \cup {nil}

\* Round numbers (mathematically unbounded).
Rounds == Nat

\* Combined (value, round) lock state. The "not locked" state is the record
\* [value |-> nil, round |-> -1].
LockState == [value : ValuesOrNil, round : Rounds \cup {-1}]

(***************************************************************************)
(* Message types                                                           *)
(***************************************************************************)

\* A proposal is sender-agnostic (leaderless). It is an origin-less
\* justification [type, round, value, validRound]. Proposer designation is a
\* refinement introduced only at TendermintByzantine, where a named validator
\* may be faulty.
ProposalMsg ==
  [ type : {"Proposal"}, round : Rounds, value : Values, validRound : Rounds \cup {-1} ]

PrevoteMsg ==
  [ type : {"Prevote"}, sender : Validators, round : Rounds, valueID : ValuesOrNil ]

PrecommitMsg ==
  [ type: {"Precommit"}, sender: Validators, round : Rounds, valueID : ValuesOrNil ]

Message == ProposalMsg \cup PrevoteMsg \cup PrecommitMsg

Proposal(r, v, vr) ==
  [ type |-> "Proposal", round |-> r, value |-> v, validRound |-> vr ]

Prevote(p, r, v) ==
  [ type |-> "Prevote", sender |-> p, round |-> r, valueID |-> v ]

Precommit(p, r, v) ==
  [ type  |-> "Precommit", sender |-> p, round |-> r, valueID |-> v ]

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
  sent,    \* SUBSET Message              all broadcast messages (proposals + votes)
  locked,  \* [Validators -> LockState]   locked (value, round); nil/-1 = unlocked
  decision \* [Validators -> ValuesOrNil] decided value (nil = not yet)

vars == << sent, locked, decision >>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ sent     \in SUBSET Message
  /\ locked   \in [Validators -> LockState]
  /\ decision \in [Validators -> ValuesOrNil]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ sent     = {}
  /\ locked   = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Validators |-> nil]

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
SentProposals  == { m \in sent : m.type = "Proposal" }
SentPrevotes   == { m \in sent : m.type = "Prevote" }
SentPrecommits == { m \in sent : m.type = "Precommit" }

\* Some validator proposed value v at round r.
ExistsProposal(v, r) == \E m \in SentProposals : m.round = r /\ m.value = v

PrevotesAt(v, r)   == { m \in SentPrevotes   : m.round = r /\ m.valueID = v }
PrecommitsAt(v, r) == { m \in SentPrecommits : m.round = r /\ m.valueID = v }

PrevoteSendersFor(v, r)   == { m.sender : m \in PrevotesAt(v, r) }
PrecommitSendersFor(v, r) == { m.sender : m \in PrecommitsAt(v, r) }

\* A polka for v at r: a quorum prevoted v at round r.
ExistsPrevoteQuorum(v, r)   == \E Q \in Quorum : Q \subseteq PrevoteSendersFor(v, r)
\* A commit for v at r: a quorum precommitted v at round r.
ExistsPrecommitQuorum(v, r) == \E Q \in Quorum : Q \subseteq PrecommitSendersFor(v, r)

\* One vote per round per validator.
NoPrevoteAtOrAboveRound(p, r) ==
  ~ \E m \in SentPrevotes : m.sender = p /\ m.round >= r
NoHigherRoundPrevote(p, r) ==
  ~ \E m \in SentPrevotes : m.sender = p /\ m.round > r
NoPrecommitAtOrAboveRound(p, r) ==
  ~ \E m \in SentPrecommits : m.sender = p /\ m.round >= r

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A fully permissive, leaderless proposal: ANY value v may be proposed at
\* ANY round r (with any validRound vr). Proposals are sender-agnostic, so
\* there is no proposer parameter, no round-robin Proposer guard, and no
\* value restriction. This single action over-approximates both the honest
\* round-robin Propose of TendermintOperational and a Byzantine proposer's
\* injected proposals, so both lower specs map their proposals onto it. A
\* proposal touches neither locked nor decision; its only role is to enable
\* PrevoteValue (via ExistsProposal).
Propose(r) ==
  /\ \E v \in Values, vr \in Rounds \cup {-1} :
       sent' = sent \cup {Proposal(r, v, vr)}
  /\ UNCHANGED << locked, decision >>

\* PrevoteNil + the nil branches of OnProposalNoPOL/OnProposalWithPOL.
\* A nil prevote is always permitted.
PrevoteNil(p, r) ==
  /\ NoPrevoteAtOrAboveRound(p, r)
  /\ NoPrecommitAtOrAboveRound(p, r)
  /\ sent' = sent \cup {Prevote(p, r, nil)}
  /\ UNCHANGED << locked, decision >>

\* OnProposalNoPOL + OnProposalWithPOL, merged. The third disjunct is the
\* Proof-of-Lock unlock rule, folded from validRound. See the module header:
\* this disjunct is retained by necessity for refinement soundness.
PrevoteValue(p, r) ==
  /\ NoPrevoteAtOrAboveRound(p, r)
  /\ NoPrecommitAtOrAboveRound(p, r)
  /\ \E v \in Values :
       /\ Valid(v)
       /\ ExistsProposal(v, r)      \* may only prevote a proposed value
       /\ \/ locked[p].round = -1   \* never locked  (vr = -1 case)
          \/ locked[p].value = v    \* locked on v
          \/ \E vr \in Rounds :     \* PoL: unlock via a lower polka
               /\ vr < r
               /\ ExistsPrevoteQuorum(v, vr)
               /\ locked[p].round <= vr
       /\ sent' = sent \cup {Prevote(p, r, v)}
  /\ UNCHANGED << locked, decision >>

\* OnPrevoteQuorumNil + PrecommitNil. A nil precommit is always permitted.
PrecommitNil(p, r) ==
  /\ NoPrecommitAtOrAboveRound(p, r)
  /\ NoHigherRoundPrevote(p, r)
  /\ sent' = sent \cup {Precommit(p, r, nil)}
  /\ UNCHANGED << locked, decision >>

\* OnPrevoteQuorumValueFirstTime. Locking is coupled to precommit-for-value:
\* a validator precommits v at r only on a polka for v at r, and locks v at r.
PrecommitValue(p, r) ==
  /\ NoPrecommitAtOrAboveRound(p, r)
  /\ NoHigherRoundPrevote(p, r)
  /\ \E v \in Values :
       /\ Valid(v)
       /\ ExistsPrevoteQuorum(v, r)     \* polka-before-precommit
       /\ sent'   = sent \cup {Precommit(p, r, v)}
       /\ locked' = [locked EXCEPT ![p] = [value |-> v, round |-> r]]
  /\ UNCHANGED decision

\* OnPrecommitQuorumValue. DecisionImpliesPrecommitQuorum is now this guard.
Decide(p) ==
  /\ decision[p] = nil
  /\ \E v \in Values :
       /\ Valid(v)
       /\ \E r \in Rounds : ExistsPrecommitQuorum(v, r)
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ UNCHANGED << sent, locked >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
  \/ \E r \in Rounds : Propose(r)
  \/ \E p \in Validators :
    \/ \E r \in Rounds : PrevoteNil(p, r)
    \/ \E r \in Rounds : PrevoteValue(p, r)
    \/ \E r \in Rounds : PrecommitNil(p, r)
    \/ \E r \in Rounds : PrecommitValue(p, r)
    \/ Decide(p)

(***************************************************************************)
(* Complete specification. Pure safety form: no fairness, no liveness.     *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties (consensus typical properties).                       *)
(***************************************************************************)

\* Agreement: any two validators that have decided agree on the value.
Agreement ==
  \A p, q \in Validators :
    decision[p] # nil /\ decision[q] # nil => decision[p] = decision[q]

\* Validity: any decided value is application-valid.
Validity ==
  \A p \in Validators :
    decision[p] # nil => Valid(decision[p])

\* Integrity: decision, once set, never changes value.
IntegrityStep ==
  \A p \in Validators :
    decision[p] # nil => decision'[p] = decision[p]

=============================================================================
\* Modification History
\* Created Jun 7 2026 by hvanz (Hernán Vanzetto)