------------------------ MODULE TendermintByzantine -------------------------
(***************************************************************************)
(* Byzantine TLA+ spec of Tendermint single-height, multi-round            *)
(* consensus. It lifts the operational spec (TendermintOperational) to     *)
(* a Byzantine fault model, in the style of Lamport's "Byzantizing         *)
(* Paxos by refinement". Honest validators run the operational             *)
(* algorithm unchanged; the spec adds an honest / faulty split,            *)
(* Byzantine quorums, and one permissive faulty action.                    *)
(*                                                                         *)
(* FAULT MODEL (Byzantine voters AND leaders)                              *)
(*   Up to f validators are faulty (Faulty); the rest are honest           *)
(*   (Honest == Validators \ Faulty). Faults are authenticated: a          *)
(*   faulty validator cannot forge an honest signature, so every           *)
(*   message it injects has sender \in Faulty. Faulty validators have      *)
(*   no algorithm state; their one action, FaultyStep, adds ANY            *)
(*   well-typed message with its own sender. That subsumes                 *)
(*   equivocation, amnesia, fake proposals and out-of-turn votes: the      *)
(*   full Byzantine power short of forgery.                                *)
(*                                                                         *)
(* BYZANTINE LEADERS                                                       *)
(*   The designated proposer Proposer[r] may be faulty. An honest          *)
(*   validator acts on that proposer's proposal (guards read               *)
(*   ProposalsFromProposerAt, keyed on Proposer[r]); a faulty proposer     *)
(*   injects it via FaultyStep, possibly equivocating. Safety survives:    *)
(*   an equivocating proposer can split honest prevotes, but two values    *)
(*   cannot both reach a polka in one round (each honest validator         *)
(*   prevotes once; two polkas need 2(f+1) > 2f+1 honest prevoters). A     *)
(*   Byzantine leader threatens only liveness.                             *)
(*                                                                         *)
(* STATE (six variables; state is carried only for honest validators)      *)
(*   round     [Honest -> Rounds]: current round.                          *)
(*   step      [Honest -> Step]: propose / prevote / precommit /           *)
(*             decided.                                                    *)
(*   locked    [Honest -> LockState]: locked (value, round).               *)
(*   valid     [Honest -> LockState]: latest value seen with a polka.      *)
(*   decision  [Honest -> ValuesOrNil]: decided value; nil = undecided.    *)
(*   sent      SUBSET Message: the pool of honest AND faulty messages.     *)
(*                                                                         *)
(* MESSAGES                                                                *)
(*   Proposal, Prevote and Precommit. Unlike the upstream specs, a         *)
(*   Proposal here carries a sender: the designated proposer, who may      *)
(*   be faulty.                                                            *)
(*                                                                         *)
(* ACTIONS                                                                 *)
(*   The honest actions are the operational actions verbatim (Propose      *)
(*   through SkipRound), restricted to p \in Honest and reading the        *)
(*   designated proposer's proposal. FaultyStep is the only added          *)
(*   action. Quorum guards use ByzQuorum (polka / commit) and              *)
(*   WeakQuorum (SkipRound). There are no timers, as in the operational    *)
(*   layer.                                                                *)
(*                                                                         *)
(* QUORUMS (Byzantine, symbolic)                                           *)
(*   ByzQuorum (the 2f+1 analogue) and WeakQuorum (the f+1 analogue)       *)
(*   are CONSTANTS, characterized only by honest-intersection axioms:      *)
(*   any two ByzQuorums share an HONEST validator, and every WeakQuorum    *)
(*   contains an honest validator. There is no cardinality; the            *)
(*   concrete 2f+1 / f+1 sizes appear only in the MC .cfg.                 *)
(*                                                                         *)
(* SCOPE                                                                   *)
(*   Single height. Up to f Byzantine validators. Rounds unbounded (Nat).  *)
(*   Asynchronous, safety only: Spec == Init /\ [][Next]_vars, no          *)
(*   fairness, no liveness. The safety properties (Agreement, Validity)    *)
(*   are re-scoped to the HONEST validators, the only ones whose decision  *)
(*   is meaningful. Honest-scoped safety is proved by refinement onto the  *)
(*   operational spec (TendermintByzantineRefinement); liveness under      *)
(*   Byzantine leaders is addressed later at TendermintPartialSync.        *)
(***************************************************************************)

EXTENDS Integers, TLAPS

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
  Validators, \* the (non-empty) set of validators
  Values,     \* the set of values; excludes nil
  Valid(_),   \* validity predicate on Values (application-supplied)
  Proposer,   \* function Round -> Validators choosing the round's proposer
  Faulty,     \* prophecy constant: the (at most f) faulty validators;
              \* used only in the refinement proof, never by the algorithm.
  ByzQuorum,  \* set of validator-subsets that includes a quorum of honest
              \* ones (the 2f+1 analogue); characterized by the honest-
              \* intersection axioms below, never by a cardinality.
  WeakQuorum  \* set of validator-subsets that includes at least one honest
              \* one (the f+1 analogue); used by SkipRound.

\* The honest validators: everyone who is not faulty.
Honest == Validators \ Faulty

(***************************************************************************)
(* Assumptions on the constants                                            *)
(***************************************************************************)
ASSUME ValidatorsNonEmpty == Validators # {}
ASSUME ValidIsBoolean     == \A v \in Values : Valid(v) \in BOOLEAN
ASSUME ValidNonEmpty      == \E v \in Values : Valid(v)

\* Faulty validators are validators; at least one validator is honest.
ASSUME FaultyType     == Faulty \subseteq Validators
ASSUME HonestNonEmpty == Honest # {}

\* The designated proposer may be ANY validator, including a faulty one
\* A faulty designated proposer injects (possibly equivocating) proposals via
\* FaultyStep; an honest one runs Propose. The refinement's projection keeps
\* ALL proposals (sender- stripped), so a faulty leader's proposal still has
\* an upstream image -- the leaderless TendermintOperational/TendermintVoting
\* witness "a proposal exists" without an honest sender -- which is what
\* admits Byzantine leaders while keeping the chain relay-free. Stated as a
\* total function Rounds -> Validators (not the DOMAIN-quantified form) so
\* the refinement gets Proposer[round[p]] \in Validators for free; the MC's
\* finite-domain Proposer satisfies it because the .cfg overrides Nat (hence
\* Rounds) to the same finite range.
ASSUME ProposerType == Proposer \in [Nat -> Validators]  \* Nat = Rounds (defined below)

\* ---- Byzantine quorum axioms (Lamport's BQA) ----------------------------
\* For n = 3f+1, f faulty, ByzQuorum = size-(2f+1) sets and WeakQuorum =
\* size-(f+1) sets, every axiom below holds by pigeonhole; that is the
\* intended concrete instantiation (supplied by the MC .cfg). The proofs
\* stay parametric over these axioms, with no cardinality.
ASSUME ByzQuorumType == ByzQuorum \in SUBSET (SUBSET Validators)
\* Any two Byzantine quorums share an HONEST validator (the Byzantine
\* generalization of plain quorum intersection). This is what carries the
\* lock-chain argument: an honest validator never votes contradictorily.
\* It is the only quorum fact the refinement onto TendermintVoting needs:
\* TendermintVoting's Agreement rests on plain quorum intersection alone,
\* which the honest projection supplies. (The stronger quorum axiom a
\* direct proof at the Protocol layer would use does NOT hold under the
\* honest projection; see the CHAIN POSITION note.)
ASSUME ByzQuorumIntersection ==
  \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Honest # {}
ASSUME WeakQuorumType == WeakQuorum \in SUBSET (SUBSET Validators)
\* Every weak quorum contains at least one honest validator (f+1 of 3f+1).
\* SkipRound's safety intuition; not needed for the safety refinement
\* (SkipRound touches only round/step, which TendermintVoting projects away).
ASSUME WeakQuorumHasHonest ==
  \A W \in WeakQuorum : W \cap Honest # {}

(***************************************************************************)
(* Types and operators (identical to TendermintOperational.tla)               *)
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

\* Pseudo-code line 18: 'proposal <- getValue()'.
getValue == {v \in Values : Valid(v)}

\* ---- Message types -------------------------------------------------------
ProposalMsg ==
  [ type : {"Proposal"}, sender : Validators, round : Rounds, value : Values, validRound : Rounds \cup {-1} ]

PrevoteMsg ==
  [ type : {"Prevote"}, sender : Validators, round : Rounds, valueID : ValuesOrNil ]

PrecommitMsg ==
  [ type: {"Precommit"}, sender: Validators, round : Rounds, valueID : ValuesOrNil ]

Message == ProposalMsg \cup PrevoteMsg \cup PrecommitMsg

Proposal(p, r, v, vr) ==
  [ type |-> "Proposal", sender |-> p, round |-> r, value |-> v, validRound |-> vr ]

Prevote(p, r, v) ==
  [ type |-> "Prevote", sender |-> p, round |-> r, valueID |-> v ]

Precommit(p, r, v) ==
  [ type  |-> "Precommit", sender |-> p, round |-> r, valueID |-> v ]

LockState == [value : ValuesOrNil, round : Rounds \cup {-1}]

(***************************************************************************)
(* State variables                                                         *)
(*                                                                         *)
(* The per-validator control/lock state is carried only for HONEST         *)
(* validators (domain Honest): faulty validators have no algorithm state,  *)
(* only the messages they inject. This makes the refinement mapping onto   *)
(* TendermintOperational (Validators <- Honest) the identity on these      *)
(* functions. The message pool 'sent' holds honest and faulty messages.    *)
(***************************************************************************)
VARIABLES
  round,    \* [Honest -> Rounds]    current round per honest validator
  step,     \* [Honest -> Step]      current step per honest validator
  locked,   \* [Honest -> LockState] locked (value, round)
  valid,    \* [Honest -> LockState] latest prevote-quorum (value, round)
  decision, \* [Honest -> ValuesOrNil] decided value (nil = not yet)
  sent      \* SUBSET Message        all broadcast messages (honest + faulty)

vars == << round, step, locked, valid, decision, sent >>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ round    \in [Honest -> Rounds]
  /\ step     \in [Honest -> Step]
  /\ locked   \in [Honest -> LockState]
  /\ valid    \in [Honest -> LockState]
  /\ decision \in [Honest -> ValuesOrNil]
  /\ sent     \in SUBSET Message

(***************************************************************************)
(* Initial state. Honest validators start in round 0 / propose / unlocked. *)
(***************************************************************************)
Init ==
  /\ round    = [v \in Honest |-> 0]
  /\ step     = [v \in Honest |-> "propose"]
  /\ locked   = [v \in Honest |-> [value |-> nil, round |-> -1]]
  /\ valid    = [v \in Honest |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Honest |-> nil]
  /\ sent     = {}

(***************************************************************************)
(* Helper operators (identical to TendermintOperational.tla, but the       *)
(* quorum predicates use ByzQuorum / WeakQuorum).                          *)
(***************************************************************************)
SentProposals  == { m \in sent : m.type = "Proposal" }
SentPrevotes   == { m \in sent : m.type = "Prevote" }
SentPrecommits == { m \in sent : m.type = "Precommit" }

SentPrevotesNonNilValue   == { m \in SentPrevotes : m.valueID \in Values}
SentPrecommitsNonNilValue == { m \in SentPrecommits : m.valueID \in Values}

ProposalsAt(r)             == { m \in SentProposals : m.round = r }
ProposalsFromProposerAt(r) == { m \in SentProposals : m.round = r /\ m.sender = Proposer[r]}
PrevotesAt(v, r)           == { m \in SentPrevotes : m.round = r /\ m.valueID = v }
PrecommitsAt(v, r)         == { m \in SentPrecommits : m.round = r /\ m.valueID = v }

PrevoteSendersFor(v, r)    == { m.sender : m \in PrevotesAt(v, r) }
PrecommitSendersFor(v, r)  == { m.sender : m \in PrecommitsAt(v, r) }

SendersOfTypeAtRound(t, r) == { m.sender : m \in { x \in sent : x.type = t /\ x.round = r } }

\* A polka / commit is a BYZANTINE quorum of senders: only an honest
\* sub-quorum is trusted, but the quorum itself may include faulty senders.
ExistsPrevoteQuorum(v, r)   == \E Q \in ByzQuorum : Q \subseteq PrevoteSendersFor(v, r)
ExistsPrecommitQuorum(v, r) == \E Q \in ByzQuorum : Q \subseteq PrecommitSendersFor(v, r)
ExistsAnyPrevoteQuorum(r)   == \E Q \in ByzQuorum : Q \subseteq SendersOfTypeAtRound("Prevote", r)
ExistsAnyPrecommitQuorum(r) == \E Q \in ByzQuorum : Q \subseteq SendersOfTypeAtRound("Precommit", r)

SendersOfAnyMessageAt(r) ==
         SendersOfTypeAtRound("Proposal", r)
    \cup SendersOfTypeAtRound("Prevote", r)
    \cup SendersOfTypeAtRound("Precommit", r)

(***************************************************************************)
(* Honest actions.                                                         *)
(*                                                                         *)
(* These are the TendermintOperational actions verbatim (the honest        *)
(* algorithm is unchanged); the Next-state relation restricts them to p    *)
(* \in Honest.                                                             *)
(***************************************************************************)

\* === Lines 14-19: if p is the proposer, send a proposal ===================
Propose(p) ==
  /\ step[p] = "propose"
  /\ Proposer[round[p]] = p
  /\ ~ \E msg \in ProposalsAt(round[p]) : msg.sender = p
  /\ \E v \in IF valid[p].value # nil
              THEN {valid[p].value}
              ELSE getValue :
       sent' = sent \cup {Proposal(p, round[p], v, valid[p].round)}
  /\ UNCHANGED << round, step, locked, valid, decision >>

\* === Lines 57-60: give up waiting for a proposal; prevote nil =============
PrevoteNil(p) ==
  /\ step[p] = "propose"
  /\ sent' = sent \cup {Prevote(p, round[p], nil)}
  /\ step' = [step EXCEPT ![p] = "prevote"]
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 22-27: upon fresh proposal (vr = -1), send prevote =============
OnProposalNoPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in ProposalsFromProposerAt(round[p]) :
       /\ prop.validRound = -1
       /\ LET v == prop.value
              voteValueID ==
                IF Valid(v) /\ (locked[p].round = -1 \/ locked[p].value = v)
                THEN v
                ELSE nil
          IN /\ sent' = sent \cup {Prevote(p, round[p], voteValueID)}
             /\ step' = [step EXCEPT ![p] = "prevote"]
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 28-33: upon proposal with Proof-of-Lock + prevote polka ========
OnProposalWithPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in ProposalsFromProposerAt(round[p]) :
       /\ ExistsPrevoteQuorum(prop.value, prop.validRound)
       /\ prop.validRound \in Range(0, round[p])
       /\ LET v  == prop.value
              vr == prop.validRound
              voteValueID ==
                IF Valid(v) /\ (locked[p].round <= vr \/ locked[p].value = v)
                THEN v
                ELSE nil
          IN /\ sent' = sent \cup {Prevote(p, round[p], voteValueID)}
             /\ step' = [step EXCEPT ![p] = "prevote"]
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 36-43, upon proposal + prevote polka, when step = prevote ======
OnPrevoteQuorumValueFirstTime(p) ==
  /\ step[p] = "prevote"
  /\ \E prop \in ProposalsFromProposerAt(round[p]):
       /\ ExistsPrevoteQuorum(prop.value, round[p])
       /\ Valid(prop.value)
       /\ LET v == prop.value
              newRecord == [value |-> v, round |-> round[p]]
          IN /\ locked' = [locked EXCEPT ![p] = newRecord]
             /\ sent'   = sent \cup {Precommit(p, round[p], v)}
             /\ step'   = [step EXCEPT ![p] = "precommit"]
             /\ valid'  = [valid EXCEPT ![p] = newRecord]
  /\ UNCHANGED << round, decision >>

\* === Lines 36-43, upon proposal + prevote polka, when step >= precommit ===
OnPrevoteQuorumValueLateUpdate(p) ==
  /\ step[p] \in {"precommit", "decided"}
  /\ valid[p].round < round[p]
  /\ \E prop \in ProposalsFromProposerAt(round[p]) :
       /\ ExistsPrevoteQuorum(prop.value, round[p])
       /\ Valid(prop.value)
       /\ valid' = [valid EXCEPT ![p] =
                      [value |-> prop.value, round |-> round[p]]]
  /\ UNCHANGED << round, step, locked, decision, sent >>

\* === Lines 44-46: upon polka of nil prevotes, send nil precommit ==========
OnPrevoteQuorumNil(p) ==
  /\ step[p] = "prevote"
  /\ ExistsPrevoteQuorum(nil, round[p])
  /\ sent' = sent \cup {Precommit(p, round[p], nil)}
  /\ step' = [step EXCEPT ![p] = "precommit"]
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 61-64: give up waiting for a polka; precommit nil ==============
PrecommitNil(p) ==
  /\ step[p] = "prevote"
  /\ sent' = sent \cup {Precommit(p, round[p], nil)}
  /\ step' = [step EXCEPT ![p] = "precommit"]
  /\ UNCHANGED << round, locked, valid, decision >>

\* === Lines 49-54: upon proposal + precommit quorum, decide value ===========
OnPrecommitQuorumValue(p) ==
  /\ decision[p] = nil
  /\ \E r \in Rounds: \E prop \in ProposalsFromProposerAt(r):
       /\ ExistsPrecommitQuorum(prop.value, r)
       /\ Valid(prop.value)
       /\ decision' = [decision EXCEPT ![p] = prop.value]
       /\ step'     = [step     EXCEPT ![p] = "decided"]
  /\ UNCHANGED << round, locked, valid, sent >>

\* === Lines 65-67: give up on the current round; start the next one ========
AdvanceRound(p) ==
  /\ step[p] # "decided"
  /\ round' = [round EXCEPT ![p] = round[p] + 1]
  /\ step'  = [step  EXCEPT ![p] = "propose"]
  /\ UNCHANGED << locked, valid, decision, sent >>

\* === Lines 55-56: upon a weak quorum of senders at a higher round =========
\* WeakQuorum abstracts the "f+1" threshold: f+1 senders include an honest
\* one, which has genuinely reached the higher round, so the skip is safe.
SkipRound(p) ==
  /\ step[p] # "decided"
  /\ \E r \in Rounds :
      /\ \E W \in WeakQuorum: W \subseteq SendersOfAnyMessageAt(r)
      /\ r > round[p]
      /\ round' = [round EXCEPT ![p] = r]
  /\ step'  = [step  EXCEPT ![p] = "propose"]
  /\ UNCHANGED << locked, valid, decision, sent >>

(***************************************************************************)
(* Faulty action.                                                          *)
(*                                                                         *)
(* A faulty validator p may inject ANY well-typed message whose sender is  *)
(* itself (authenticated: it cannot forge an honest sender). Repeated      *)
(* FaultySteps give equivocation, amnesia, fake proposals, and out-of-turn *)
(* votes -- the full Byzantine power short of forgery. It touches no       *)
(* algorithm state (faulty validators have none).                          *)
(***************************************************************************)
FaultyStep(p) ==
  /\ \E m \in Message :
       /\ m.sender = p
       /\ sent' = sent \cup {m}
  /\ UNCHANGED << round, step, locked, valid, decision >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
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
  \/ \E p \in Faulty : FaultyStep(p)

(***************************************************************************)
(* Complete specification. Pure safety form: no fairness, no liveness.     *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety properties, re-scoped to the HONEST validators (the only ones    *)
(* whose decision/lock state is meaningful).                               *)
(***************************************************************************)

\* Agreement: any two HONEST validators that have decided agree on the value.
Agreement ==
  \A p, q \in Honest :
    decision[p] # nil /\ decision[q] # nil => decision[p] = decision[q]

\* Validity: any value decided by an honest validator is application-valid.
Validity ==
  \A p \in Honest :
    decision[p] # nil => Valid(decision[p])

\* Integrity: an honest validator's decision, once set, never changes value.
IntegrityStep ==
  \A p \in Honest :
    decision[p] # nil => decision'[p] = decision[p]

=============================================================================
\* Modification History
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)
