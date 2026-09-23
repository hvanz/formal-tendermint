----------------------- MODULE TendermintOperational ------------------------
(***************************************************************************)
(* High-level, operational TLA+ spec of Tendermint: it keeps the           *)
(* per-validator state machine (round and step) that drives the protocol,  *)
(* and derives the safety properties (Agreement, Validity) by              *)
(* refinement from the TendermintVoting spec.                              *)
(*                                                                         *)
(* STATE (six variables; the first five are per-validator functions)       *)
(*   round     [Validators -> Rounds]: current round.                      *)
(*   step      [Validators -> Step]: propose / prevote / precommit /       *)
(*             decided.                                                    *)
(*   locked    [Validators -> LockState]: locked (value, round);           *)
(*             [nil, -1] means unlocked.                                   *)
(*   valid     [Validators -> LockState]: latest value seen with a         *)
(*             prevote quorum.                                             *)
(*   decision  [Validators -> ValuesOrNil]: decided value; nil means       *)
(*             undecided.                                                  *)
(*   sent      SUBSET Message: the global pool of broadcast messages.      *)
(*                                                                         *)
(* MESSAGES                                                                *)
(*   Proposal, Prevote and Precommit, in the single pool sent. A           *)
(*   proposal carries a validRound (for proof-of-lock) and no sender:      *)
(*   proposals are leaderless (see PROPOSALS).                             *)
(*                                                                         *)
(* NETWORK MODEL                                                           *)
(*   One broadcast pool, sent. Validators read it directly in action       *)
(*   guards. There is no per-validator inbox and no Deliver step.          *)
(*   Asynchrony is captured by WHICH action a validator fires and WHEN;    *)
(*   the spec commits to no delivery order.                                *)
(*                                                                         *)
(* ACTIONS (a step machine over round / step per validator)                *)
(*   Propose                        propose any value at any round.        *)
(*   OnProposalNoPOL                prevote a fresh proposal.              *)
(*   OnProposalWithPOL              prevote a proof-of-lock proposal.      *)
(*   PrevoteNil                     give up in propose; prevote nil.       *)
(*   OnPrevoteQuorumValueFirstTime  on a polka, lock and precommit v.      *)
(*   OnPrevoteQuorumValueLateUpdate refresh valid on a later polka.        *)
(*   OnPrevoteQuorumNil             on a nil polka, precommit nil.         *)
(*   PrecommitNil                   give up in prevote; precommit nil.     *)
(*   OnPrecommitQuorumValue         on a precommit quorum, decide.         *)
(*   AdvanceRound                   give up the round; start next.         *)
(*   SkipRound                      catch up to a higher round.            *)
(*                                                                         *)
(* ROUND ADVANCEMENT (no timers)                                           *)
(*   This safety layer has no timing content, so the timeout mechanism     *)
(*   is dropped: no clock, no per-step flag. Algorithm 1's three timeout   *)
(*   transitions become ungated "give-up" actions (PrevoteNil,             *)
(*   PrecommitNil, AdvanceRound), always enabled in their step. A safety   *)
(*   spec does not model WHY a validator gives up. SkipRound is a          *)
(*   separate catch-up, gated by one message from a higher round           *)
(*   (all-honest, so one sender is legitimate evidence).                   *)
(*                                                                         *)
(* PROPOSALS (leaderless)                                                  *)
(*   Propose is permissive: any value at any round, with no proposer       *)
(*   designation and no round-robin. The prevote / precommit guards read   *)
(*   any proposal at the round (ProposalsAt(r)), not a designated          *)
(*   proposer's.                                                           *)
(*                                                                         *)
(* QUORUMS (symbolic)                                                      *)
(*   Quorum is a CONSTANT, characterized only by QuorumIntersection: any   *)
(*   two quorums share a validator. There is no cardinality and no         *)
(*   n = 3f+1. The model is all-honest; BFT quorum sizes are only the      *)
(*   intended concrete instantiation from the .cfg files.                  *)
(*                                                                         *)
(* SCOPE                                                                   *)
(*   Single height (no height increment, no validator-set change). All     *)
(*   validators honest. Rounds unbounded (Nat). Asynchronous, safety       *)
(*   only: Spec == Init /\ [][Next]_vars, no fairness, no liveness.        *)
(*   Byzantine faults, timeouts and liveness are added by lower            *)
(*   refinements.                                                          *)
(***************************************************************************)

EXTENDS Integers, TLAPS

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
  Validators, \* the (non-empty) set of validators
  Values,     \* the set of values; excludes nil
  Valid(_),   \* validity predicate on Values (application-supplied)
  Quorum      \* set of validator-subsets large enough to decide; abstract,
              \* characterized only by QuorumIntersection (any two quorums
              \* share a validator), never by a cardinality.

(***************************************************************************)
(* Assumptions on the constants                                            *)
(***************************************************************************)
\* Not used in the proof.
ASSUME ValidatorsNonEmpty == Validators # {}
ASSUME ValidIsBoolean     == \A v \in Values : Valid(v) \in BOOLEAN
ASSUME ValidNonEmpty      == \E v \in Values : Valid(v)

\* The two axioms below are the ONLY facts the proofs use about Quorum: no
\* proof refers to a cardinality, to a count of faulty validators, or to
\* n = 3f+1. This model is all-honest. The standard BFT quorum sizes are
\* merely the intended concrete instantiation (supplied by the TLC .cfg
\* files).
ASSUME QuorumType         == Quorum \in SUBSET (SUBSET Validators)
ASSUME QuorumIntersection ==
  \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

(***************************************************************************)
(* Types and operators                                                     *)
(***************************************************************************)
\* Half-open integer range [a .. b) (a included, b excluded).
Range(a, b) == {x \in Int: a <= x /\ x < b}

\* An unspecified, sentinel value that is distinct from every element of Values.
nil == CHOOSE v: v \notin Values

\* The set of all non-nil values plus the special nil value.
ValuesOrNil == Values \cup {nil}

\* Round numbers (mathematically unbounded).
Rounds == Nat

\* Validator step within a round.
Step == {"propose", "prevote", "precommit", "decided"}

\* ---- Message types: tagged union with disjoint per-type field sets ----
\* Sender-agnostic (leaderless): proposer designation is introduced only at
\* TendermintByzantine, where a named validator may be faulty. See
\* TendermintVoting.
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

\* Combined (value, round) state for a validator's lock and for the
\* "valid value seen" record. The pseudo-code carries lockedValue/lockedRound
\* and validValue/validRound as paired variables that are always updated
\* together; merging them as a single record makes that coupling explicit.
\* The "not locked" / "no valid value seen" state is the record
\*   [value |-> nil, round |-> -1].
LockState == [value : ValuesOrNil, round : Rounds \cup {-1}]

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
  round,    \* [Validators -> Rounds]    current round per validator
  step,     \* [Validators -> Step]      current step per validator
  locked,   \* [Validators -> LockState] locked (value, round); nil/-1 = unlocked
  valid,    \* [Validators -> LockState] latest prevote-quorum (value, round)
  decision, \* [Validators -> ValuesOrNil] decided value (nil = not yet)
  sent      \* SUBSET Message            all broadcast messages

vars == << round, step, locked, valid, decision, sent >>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ round    \in [Validators -> Rounds]
  /\ step     \in [Validators -> Step]
  /\ locked   \in [Validators -> LockState]
  /\ valid    \in [Validators -> LockState]
  /\ decision \in [Validators -> ValuesOrNil]
  /\ sent     \in SUBSET Message

(***************************************************************************)
(* Initial state.                                                          *)
(* Pseudo-code lines 1-9 ('Initialization') + line 10 ('StartRound(0)'),   *)
(* with StartRound's per-validator effects unrolled. The proposer branch   *)
(* (lines 14-19) is the Propose action; the non-proposer branch (lines     *)
(* 20-21) scheduled a timer, dropped in this timer-free layer.             *)
(***************************************************************************)
Init ==
  /\ round    = [v \in Validators |-> 0]
  /\ step     = [v \in Validators |-> "propose"]
  /\ locked   = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ valid    = [v \in Validators |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Validators |-> nil]
  /\ sent     = {}

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
SentProposals  == { m \in sent : m.type = "Proposal" }
SentPrevotes   == { m \in sent : m.type = "Prevote" }
SentPrecommits == { m \in sent : m.type = "Precommit" }

SentPrevotesNonNilValue   == { m \in SentPrevotes : m.valueID \in Values}
SentPrecommitsNonNilValue == { m \in SentPrecommits : m.valueID \in Values}

ProposalsAt(r)     == { m \in SentProposals : m.round = r }
PrevotesAt(v, r)   == { m \in SentPrevotes : m.round = r /\ m.valueID = v }
PrecommitsAt(v, r) == { m \in SentPrecommits : m.round = r /\ m.valueID = v }

\* Senders of Prevote/Precommit messages for a specific valueID at given round.
PrevoteSendersFor(v, r)   == { m.sender : m \in PrevotesAt(v, r) }
PrecommitSendersFor(v, r) == { m.sender : m \in PrecommitsAt(v, r) }

ExistsPrevoteQuorum(v, r)   == \E Q \in Quorum : Q \subseteq PrevoteSendersFor(v, r) \* a polka
ExistsPrecommitQuorum(v, r) == \E Q \in Quorum : Q \subseteq PrecommitSendersFor(v, r)

\* Some message (proposal or vote) was sent at round r. Sender-agnostic: a
\* proposal carries no sender, and one message is already evidence the round
\* is underway. Gates SkipRound (see below).
ExistsMessageAt(r) == \E m \in sent : m.round = r

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* === Lines 14-19: send a proposal (leaderless) ============================
\* Leaderless-operational: no round-robin Proposer guard. A proposal is an
\* origin-less justification (any value v at any round r, any validRound vr),
\* exactly as TendermintVoting's Propose; proposer designation is a
\* refinement introduced at TendermintByzantine, where a named validator may
\* be faulty. Propose only adds the proposal message and touches no
\* per-validator state, so it maps directly onto the abstract permissive
\* V!Propose.
Propose ==
  /\ \E r \in Rounds, v \in Values, vr \in Rounds \cup {-1} :
        sent' = sent \cup {Proposal(r, v, vr)}
  /\ UNCHANGED << round, step, locked, valid, decision >>

\* === Lines 57-60: give up waiting for a proposal; prevote nil =============
\* Algorithm 1's OnTimeoutPropose with the timer gate dropped (see ROUND
\* ADVANCEMENT): an ungated give-up action, always enabled while in propose.
PrevoteNil(p) ==
  /\ step[p] = "propose"                                     \* line 58
  /\ sent' = sent \cup {Prevote(p, round[p], nil)}           \* line 59
  /\ step' = [step EXCEPT ![p] = "prevote"]                  \* line 60
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 22-27: upon fresh proposal (vr = -1), send prevote =============
OnProposalNoPOL(p) ==
  /\ step[p] = "propose"                                     \* line 22, 'while' guard
  /\ \E prop \in ProposalsAt(round[p]) :                     \* line 22, 'upon-from' condition
       /\ prop.validRound = -1                               \* fresh proposal
       /\ LET v == prop.value
              voteValueID ==
                IF Valid(v) /\ (locked[p].round = -1 \/ locked[p].value = v) \* line 23
                THEN v                                       \* line 24
                ELSE nil                                     \* line 26
          IN /\ sent' = sent \cup {Prevote(p, round[p], voteValueID)}
             /\ step' = [step EXCEPT ![p] = "prevote"]       \* line 27
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 28-33: upon proposal with Proof-of-Lock + prevote polka ========
\* Handles a proposal carrying Proof-of-Lock (validRound >= 0) plus
\* a prevote-quorum for that value at round vr.
OnProposalWithPOL(p) ==
  /\ step[p] = "propose"                                     \* line 28, 'while' guard
  /\ \E prop \in ProposalsAt(round[p]) :                     \* line 28, 'upon-from' condition
       /\ ExistsPrevoteQuorum(prop.value, prop.validRound)   \* line 28, 'AND' clause
       /\ prop.validRound \in Range(0, round[p])             \* line 28, 0 <= vr < round_p
       /\ LET v  == prop.value
              vr == prop.validRound
              voteValueID ==
                IF Valid(v) /\ (locked[p].round <= vr \/ locked[p].value = v) \* line 29
                THEN v                                       \* line 30
                ELSE nil                                     \* line 32
          IN /\ sent' = sent \cup {Prevote(p, round[p], voteValueID)}
             /\ step' = [step EXCEPT ![p] = "prevote"]       \* line 33
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 36-43, upon proposal + prevote polka, when step = prevote ======
OnPrevoteQuorumValueFirstTime(p) ==
  /\ step[p] = "prevote"                                     \* "for the first time" guard
  /\ \E prop \in ProposalsAt(round[p]):                      \* line 36, 'upon' condition
       /\ ExistsPrevoteQuorum(prop.value, round[p])          \* line 36, 'AND' clause
       /\ Valid(prop.value)                                  \* line 36
       /\ LET v == prop.value
              newRecord == [value |-> v, round |-> round[p]] \* both locked and valid get the same value
          IN /\ locked' = [locked EXCEPT ![p] = newRecord]   \* lines 38-39
             /\ sent'   = sent \cup {Precommit(p, round[p], v)} \* line 40
             /\ step'   = [step EXCEPT ![p] = "precommit"]   \* line 41
             /\ valid'  = [valid EXCEPT ![p] = newRecord]    \* lines 42-43
  /\ UNCHANGED << round, decision >>

\* === Lines 36-43, upon proposal + prevote polka, when step >= precommit ===
\* The 'step_p >= precommit' branch where the 'if step_p = prevote then ... endif'
\* block is skipped and ONLY the valid fields are updated.
OnPrevoteQuorumValueLateUpdate(p) ==
  /\ step[p] \in {"precommit", "decided"}                    \* line 36, 'while' guard
  /\ valid[p].round < round[p]                               \* "for the first time" guard
  /\ \E prop \in ProposalsAt(round[p]) :                     \* line 36, 'upon' condition
       /\ ExistsPrevoteQuorum(prop.value, round[p])          \* line 36, 'AND' clause
       /\ Valid(prop.value)                                  \* line 36, 'while' guard
       /\ valid' = [valid EXCEPT ![p] =
                      [value |-> prop.value, round |-> round[p]]]  \* lines 42-43
  /\ UNCHANGED << round, step, locked, decision, sent >>

\* === Lines 44-46: upon polka of nil prevotes, send nil precommit ==========
OnPrevoteQuorumNil(p) ==
  /\ step[p] = "prevote"                                     \* line 44
  /\ ExistsPrevoteQuorum(nil, round[p])
  /\ sent' = sent \cup {Precommit(p, round[p], nil)}         \* line 45
  /\ step' = [step EXCEPT ![p] = "precommit"]                \* line 46
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 61-64: give up waiting for a polka; precommit nil ==============
\* Algorithm 1's OnTimeoutPrevote with the timer gate dropped: an ungated
\* give-up action, always enabled while in prevote.
PrecommitNil(p) ==
  /\ step[p] = "prevote"                                     \* line 62
  /\ sent' = sent \cup {Precommit(p, round[p], nil)}         \* line 63
  /\ step' = [step EXCEPT ![p] = "precommit"]                \* line 64
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 49-54: upon proposal + precommit quorum, decide value ===========
\* Single-height v1: lines 52-54 (h_p++, reset locked/valid, StartRound(0))
\* are NOT modeled. Decision is terminal in our scope.
OnPrecommitQuorumValue(p) ==
  /\ decision[p] = nil                                       \* line 49, 'while' guard
  /\ \E r \in Rounds: \E prop \in ProposalsAt(r):            \* line 49, 'upon' condition
       /\ ExistsPrecommitQuorum(prop.value, r)               \* line 49, 'AND' clause
       /\ Valid(prop.value)                                  \* line 50
       /\ decision' = [decision EXCEPT ![p] = prop.value]    \* line 51
       /\ step'     = [step     EXCEPT ![p] = "decided"]
  /\ UNCHANGED << round, locked, valid, sent >>

\* === Lines 65-67: give up on the current round; start the next one ========
\* Algorithm 1's OnTimeoutPrecommit with the timer gate dropped: an ungated
\* give-up action, enabled in every nondecided step. Calls StartRound(
\* round_p + 1) in the paper; here StartRound's atomic execution is split, so
\* this action only bumps round and resets step to propose. The next round's
\* Propose or PrevoteNil fires as a separate action.
AdvanceRound(p) ==
  /\ step[p] # "decided"                                     \* line 66
  /\ round' = [round EXCEPT ![p] = round[p] + 1]
  /\ step'  = [step  EXCEPT ![p] = "propose"]
  /\ UNCHANGED << locked, valid, decision, sent >>

\* === Lines 55-56: upon any message from a higher round ====================
\* The paper's line-55 "f+1" threshold is a Byzantine defense: it ensures the
\* evidence to skip ahead contains at least one honest sender. In this
\* all-honest spec there are no liars, so a single message from round r is
\* already legitimate evidence that round r is underway, and one sender
\* suffices. The threshold re-appears where it has meaning: WeakQuorum at
\* TendermintByzantine, and concrete f+1 at TendermintPartialSync. (Safety never reads
\* this guard: SkipRound modifies only round/step.)
SkipRound(p) ==
  /\ step[p] # "decided"
  /\ \E r \in Rounds :
        /\ ExistsMessageAt(r)                                \* line 55, 'upon' condition
        /\ r > round[p]                                      \* line 55, 'with' guard
        /\ round' = [round EXCEPT ![p] = r]                  \* line 56
  /\ step'  = [step  EXCEPT ![p] = "propose"]                \* line 56
  /\ UNCHANGED << locked, valid, decision, sent >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
  \/ Propose
  \/ \E p \in Validators:
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
(* Complete specification.                                                 *)
(* Pure safety form: no fairness conjuncts, no liveness.                   *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties (state-based invariant statements).                   *)
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
\* (Action-level property; stated here as a binary relation on consecutive
\* states. TendermintOperationalRefinement.tla wraps it in [][..]_vars to claim
\* it of Spec.)
IntegrityStep ==
  \A p \in Validators :
    decision[p] # nil => decision'[p] = decision[p]

=============================================================================
\* Modification History
\* Created Jun 7 2026 by hvanz (Hernán Vanzetto)
