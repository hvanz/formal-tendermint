------------------------ MODULE TendermintPartialSync ------------------------
(***************************************************************************)
(* Partial-synchrony liveness TLA+ spec of Tendermint single-height,       *)
(* multi-round consensus. This is the line-by-line, paper-faithful         *)
(* spec: it adds a real clock, timers, partial synchrony, and concrete     *)
(* quorums. It is the bottom of the refinement chain, so safety            *)
(* (Agreement, Validity, Integrity) is inherited by refinement;            *)
(* liveness, the conditional Termination property, is proved here.         *)
(*                                                                         *)
(* CONCRETE QUORUMS (n = 3f+1)                                             *)
(*   f is a CONSTANT fault bound; |Validators| = 3f+1 and |Faulty| <= f.   *)
(*   ByzQuorum (>= 2f+1) and WeakQuorum (>= f+1) are DEFINED by            *)
(*   cardinality (upward-closed), not symbolic constants. This is the      *)
(*   one layer where cardinality is unavoidable: liveness rests on         *)
(*   quorum AVAILABILITY (QuorumAvailable: an all-honest ByzQuorum         *)
(*   EXISTS), a counting fact no intersection axiom gives. The             *)
(*   honest-intersection safety facts are re-stated as ASSUMEs             *)
(*   (pigeonhole; checked by TLC at f = 1).                                *)
(*                                                                         *)
(* TIMERS AND CLOCK                                                        *)
(*   A discrete clock now (Nat) advances by the Tick action. Timer         *)
(*   deadlines are absolute integers (OFF = -1 is unscheduled); each       *)
(*   OnTimeout* fires when now >= deadline. Durations grow with the        *)
(*   round: TimeoutX(r) = T0X + r * TDelta, three distinct functions       *)
(*   (propose, prevote, precommit). The propose timer is armed at round    *)
(*   start; the prevote and precommit timers are armed by the Schedule*    *)
(*   actions on the first polka.                                           *)
(*                                                                         *)
(* PARTIAL SYNCHRONY (DLS model)                                           *)
(*   Timing constants Delta, GST, T0Propose, T0Prevote, T0Precommit,       *)
(*   TDelta. The pool sent is DERIVED (the support of sentTime), not a     *)
(*   variable. Each honest validator has a received set rcvd[p], and       *)
(*   honest actions read ONLY rcvd[p]: this is where asynchrony bites.     *)
(*   Deliver moves a validator's available messages into rcvd[p]. An       *)
(*   honest send activates gossip at once; a faulty message activates      *)
(*   only on its first correct receipt. After GST the clock may not        *)
(*   pass a pending message's deadline max(sentTime, GST) + Delta (the     *)
(*   paper's two-clause Gossip property).                                  *)
(*                                                                         *)
(* MAXIMAL PROGRESS                                                        *)
(*   Tick is disabled while any honest validator has an enabled            *)
(*   computation step (CanCompute), so computation is instantaneous        *)
(*   relative to the clock: a validator acts on a polka BEFORE its         *)
(*   timeout deadline. Tick is also gated by TickUseful (non-Zeno: time    *)
(*   advances only while a delivery or a live timer is pending).           *)
(*                                                                         *)
(* STATE (eleven variables)                                                *)
(*   round / step / locked / valid / decision  over Honest, as in          *)
(*     TendermintByzantine.                                                *)
(*   sentTime  [Message -> Nat \cup {OFF}]: gossip activation time.        *)
(*   rcvd      [Honest -> SUBSET Message]: per-validator received          *)
(*             messages.                                                   *)
(*   timer     [Honest -> [TimerType -> Int]]: absolute deadlines / OFF.   *)
(*   now       Nat: the global clock.                                      *)
(*   enteredAt [Honest -> [Rounds -> Nat \cup {OFF}]]: round-entry time.   *)
(*   decidedRound [Honest -> Rounds \cup {OFF}]: decision round.           *)
(*                                                                         *)
(* FAULT MODEL                                                             *)
(*   Up to f Byzantine voters AND leaders, inherited verbatim: the         *)
(*   single permissive FaultyStep, and a Proposer[r] that may be           *)
(*   faulty. The honest algorithm-with-timers is this spec read with       *)
(*   Faulty = {}.                                                          *)
(*                                                                         *)
(* SPEC AND FAIRNESS                                                       *)
(*   Spec == Init /\ [][Next]_vars /\ Fairness. Unlike the upper safety    *)
(*   layers, this spec has fairness: weak fairness on every honest         *)
(*   computation and delivery action and on Tick. Faulty validators are    *)
(*   NOT subject to fairness.                                              *)
(*                                                                         *)
(* PROPERTIES                                                              *)
(*   Agreement / Validity / Integrity: safety, inherited by refinement     *)
(*   (also MC-checkable here). Termination: CONDITIONAL. If every honest   *)
(*   validator is proposer in arbitrarily late rounds                      *)
(*   (EveryHonestProposesAgain), then every honest validator eventually    *)
(*   decides. The condition is needed because a faulty proposer can        *)
(*   stall its own round.                                                  *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLAPS

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
  Validators,   \* the (non-empty) set of validators; |Validators| = 3f+1
  Values,       \* the set of values; excludes nil
  Valid(_),     \* validity predicate on Values (application-supplied)
  Proposer,     \* function Round -> Validators choosing the round's proposer
  Faulty,       \* prophecy constant: the (at most f) faulty validators;
                \* used only in the refinement proof, never by the algorithm.
  f,            \* the Byzantine fault bound; |Validators| = 3f+1, |Faulty| <= f
  Delta,        \* message-delay bound that holds after GST (DLS)
  GST,          \* global stabilization time (a constant, unknown to processes)
  T0Propose,    \* base timeoutPropose duration:   TimeoutPropose(0)
  T0Prevote,    \* base timeoutPrevote duration:   TimeoutPrevote(0)
  T0Precommit,  \* base timeoutPrecommit duration: TimeoutPrecommit(0)
  TDelta        \* per-round timeout increment (the paper's timeoutDelta)

\* The honest validators: everyone who is not faulty.
Honest == Validators \ Faulty

\* Algorithm 1's increasing timeouts: timeoutX(r) = initTimeoutX + r*timeoutDelta
\* (paper, Section III). Three DISTINCT functions sharing the per-round increment
\* TDelta, so the within-round decision theorem (paper Lemma 5, condition 4) can
\* state the per-timeout inequalities verbatim:
\*   timeoutPropose(r) > 2*Delta + timeoutPrecommit(r-1),
\*   timeoutPrevote(r) > 2*Delta, timeoutPrecommit(r) > 2*Delta.
\* (Earlier this layer collapsed all three into one TimeoutDur, since only the
\* unbounded GROWTH in r matters for the liveness argument; the split is needed
\* only to transcribe Lemma 5's hypothesis, not by the dynamics.)
TimeoutPropose(r)   == T0Propose   + r * TDelta
TimeoutPrevote(r)   == T0Prevote   + r * TDelta
TimeoutPrecommit(r) == T0Precommit + r * TDelta

(***************************************************************************)
(* Assumptions on the constants                                            *)
(***************************************************************************)
ASSUME ValidIsBoolean == \A v \in Values : Valid(v) \in BOOLEAN
ASSUME ValidNonEmpty  == \E v \in Values : Valid(v)

\* Faulty validators are validators. (Validators # {} and Honest # {} are NOT
\* assumed: they are derived from the cardinality assumptions below -- see
\* the note there -- so positing them would be redundant.)
ASSUME FaultyType == Faulty \subseteq Validators

\* The designated proposer may be ANY validator, including a faulty one
\* Byzantine leaders match TendermintByzantine. A
\* faulty proposer can stall its own round, so Termination is conditional on
\* a correct proposer recurring (see Termination below).
ASSUME ProposerType  == Proposer \in [Nat -> Validators]  \* Nat = Rounds (defined below)

\* ---- Concrete Byzantine quorum sizing (n = 3f+1) ------------------------
\* f is a fault bound; the validator set is FINITE with exactly 3f+1 members,
\* and at most f are faulty. ByzQuorum (the 2f+1 sets) and WeakQuorum (the
\* f+1 sets) are now DEFINED by cardinality, not symbolic CONSTANTS.
\*
\* These also DISCHARGE the nonemptiness facts that TendermintByzantine posits:
\*   Validators # {}, since Cardinality(Validators) = 3f+1 >= 1; and
\* Honest # {},     since |Honest| >= |Validators| - |Faulty| >= 2f+1 >= 1
\* (both via FiniteSetTheorems; Faulty is finite as a subset of a finite
\* set). Finiteness is required: Cardinality is unspecified on infinite sets,
\* so the count = 3f+1 alone would not give nonemptiness without
\* ValidatorsFinite.
ASSUME FaultBoundType        == f \in Nat
ASSUME ValidatorsFinite      == IsFiniteSet(Validators)
ASSUME ValidatorsCardinality == Cardinality(Validators) = 3 * f + 1
ASSUME FaultyCardinality     == Cardinality(Faulty) <= f

\* A Byzantine quorum is any set of >= 2f+1 validators; a weak quorum any
\* set of >= f+1. Upward-closed, so a larger witness is always available.
ByzQuorum  == { Q \in SUBSET Validators : Cardinality(Q) >= 2 * f + 1 }
WeakQuorum == { W \in SUBSET Validators : Cardinality(W) >= f + 1 }

\* ---- Quorum facts (hold by pigeonhole for the sizing above) -------------
\* Re-stated as ASSUMEs (TLC discharges them concretely at f = 1; a TLAPS
\* lemma deriving them from the cardinality is deferred, see ARCHITECTURE).
\* SAFETY facts, inherited from TendermintByzantine (Lamport's BQA):
ASSUME ByzQuorumIntersection ==
  \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Honest # {}
ASSUME WeakQuorumHasHonest ==
  \A W \in WeakQuorum : W \cap Honest # {}
\* LIVENESS fact, NEW at this layer: an all-honest Byzantine quorum EXISTS
\* (there are 2f+1 honest validators). Intersection axioms never give this;
\* it is the quorum-availability counting fact Termination rests on.
ASSUME QuorumAvailable ==
  \E Q \in ByzQuorum : Q \subseteq Honest

\* ---- Timing constants ----------------------------------------------------
\* Delta > 0 (not just \in Nat): the post-GST delivery deadline
\* (IF sentTime >= GST THEN sentTime ELSE GST) + Delta collapses to exactly
\* GST at the pre/post-GST boundary (now = GST) when Delta = 0, so Tick's
\* deadline guard there reduces to PendingDeliveries = {} -- a condition a
\* perpetually-sending Faulty validator can keep un-satisfied forever
\* (the clock-reachability boundary case in the termination proof). Matches
\* the positivity already required of T0Propose/T0Prevote/T0Precommit below; no
\* proof or MC configuration relies on Delta = 0.
ASSUME DeltaType  == Delta \in Nat /\ Delta > 1
ASSUME GSTType    == GST    \in Nat
ASSUME T0ProposeType   == T0Propose   \in Nat /\ T0Propose   > 0
ASSUME T0PrevoteType   == T0Prevote   \in Nat /\ T0Prevote   > 0
ASSUME T0PrecommitType == T0Precommit \in Nat /\ T0Precommit > 0
ASSUME TDeltaType == TDelta \in Nat /\ TDelta > 0

\* Paper Lemma 5 condition 4 for the linear timeout functions. The round
\* term cancels, so these constant margins establish the required propose
\* and prevote inequalities at every round.
ASSUME ProposeTimeoutMargin == T0Propose + TDelta > 2 * Delta + T0Precommit
ASSUME PrevoteTimeoutMargin == T0Prevote + TDelta > 2 * Delta + T0Precommit

(***************************************************************************)
(* Types and operators (identical to TendermintByzantine.tla)              *)
(***************************************************************************)
\* Half-open integer range [a .. b) (a included, b excluded).
Range(a, b) == {x \in Int: a <= x /\ x < b}

\* An unspecified, sentinel value that is distinct from every element of
\* Values.
nil == CHOOSE v: v \notin Values

\* The set of all non-nil values plus the special nil value.
ValuesOrNil == Values \cup {nil}

\* Round numbers (mathematically unbounded).
Rounds == Nat

\* Validator step within a round.
Step == {"propose", "prevote", "precommit", "decided"}

\* The three timeout kinds, indexing the per-validator timer function.
TimerType == {"propose", "prevote", "precommit"}

\* Sentinel for "timer unscheduled" / "message not yet sent".
OFF == -1

\* Pseudo-code line 18: 'proposal <- getValue()'.
getValue == {v \in Values : Valid(v)}

\* ---- Message types (identical to TendermintByzantine.tla) ----
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
(* The consensus/lock state is carried only for HONEST validators (domain  *)
(* Honest), as in TendermintByzantine. Timers store absolute deadlines     *)
(* (OFF = unscheduled). Message state is sentTime (per-message gossip      *)
(* activation) and per-validator received sets rcvd; the pool 'sent' is    *)
(* derived from sentTime (its support), not a variable. A message can be   *)
(* sent once; this does not change from higher-level specs. now is the     *)
(* global clock.                                                           *)
(***************************************************************************)
VARIABLES
  round,    \* [Honest -> Rounds]    current round per honest validator
  step,     \* [Honest -> Step]      current step per honest validator
  locked,   \* [Honest -> LockState] locked (value, round)
  valid,    \* [Honest -> LockState] latest prevote-quorum (value, round)
  decision, \* [Honest -> ValuesOrNil] decided value (nil = not yet)
  sentTime, \* [Message -> Nat \cup {OFF}] honest-gossip activation time
  rcvd,     \* [Honest -> SUBSET Message] messages received by each validator
  timer,    \* [Honest -> [TimerType -> Int]] OFF = unscheduled; >= 0 = deadline
  now,      \* Nat                   global discrete clock
  \* Auxiliary history state used to state the timed termination lemmas.
  enteredAt,   \* [Honest -> [Rounds -> Nat \cup {OFF}]] round-entry time
  decidedRound \* [Honest -> Rounds \cup {OFF}] decision round

vars == << round, step, locked, valid, decision, sentTime, rcvd, timer, now,
           enteredAt, decidedRound >>

\* The global observable pool: messages whose honest gossip has activated.
\* For an honest sender this is its send time. For a faulty sender this is
\* the first correct receipt time. Byzantine activity before a correct
\* receipt is unobservable and is therefore abstracted away.
sent == { m \in Message : sentTime[m] # OFF }

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ round    \in [Honest -> Rounds]
  /\ step     \in [Honest -> Step]
  /\ locked   \in [Honest -> LockState]
  /\ valid    \in [Honest -> LockState]
  /\ decision \in [Honest -> ValuesOrNil]
  /\ sentTime \in [Message -> Nat \cup {OFF}]
  /\ rcvd     \in [Honest -> SUBSET Message]
  /\ timer    \in [Honest -> [TimerType -> Int]]
  /\ now      \in Nat
  /\ enteredAt    \in [Honest -> [Rounds -> Nat \cup {OFF}]]
  /\ decidedRound \in [Honest -> Rounds \cup {OFF}]

(***************************************************************************)
(* Initial state. Honest validators start in round 0 / propose / unlocked. *)
(* The propose timer is armed at round start (Algorithm 1 line 21:         *)
(* StartRound schedules timeoutPropose). All other timers are off. now = 0.*)
(***************************************************************************)
Init ==
  /\ round    = [v \in Honest |-> 0]                                 \* line 3
  /\ step     = [v \in Honest |-> "propose"]                         \* line 4
  /\ locked   = [v \in Honest |-> [value |-> nil, round |-> -1]]
  /\ valid    = [v \in Honest |-> [value |-> nil, round |-> -1]]
  /\ decision = [v \in Honest |-> nil]                               \* line 5
  /\ sentTime = [m \in Message |-> OFF]
  /\ rcvd     = [v \in Honest |-> {}]
  /\ timer    = [v \in Honest |->                                     \* line 21
                  [k \in TimerType |-> IF k = "propose" THEN TimeoutPropose(0) ELSE OFF]]
  /\ now      = 0
  /\ enteredAt    = [v \in Honest |-> [r \in Rounds |-> IF r = 0 THEN 0 ELSE OFF]]
  /\ decidedRound = [v \in Honest |-> OFF]

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)

\* ---- Per-validator helpers: honest actions read only rcvd[p] -------------
\* This is where asynchrony bites: a validator acts on what it has received,
\* not on the global pool.
RProposals(p)  == { m \in rcvd[p] : m.type = "Proposal" }
RPrevotes(p)   == { m \in rcvd[p] : m.type = "Prevote" }
RPrecommits(p) == { m \in rcvd[p] : m.type = "Precommit" }

RProposalsFromProposerAt(p, r) ==
  { m \in RProposals(p) : m.round = r /\ m.sender = Proposer[r] }
RPrevoteSendersFor(p, v, r)    == { m.sender : m \in { x \in RPrevotes(p)   : x.round = r /\ x.valueID = v } }
RPrecommitSendersFor(p, v, r)  == { m.sender : m \in { x \in RPrecommits(p) : x.round = r /\ x.valueID = v } }
RSendersOfTypeAtRound(p, t, r) == { m.sender : m \in { x \in rcvd[p] : x.type = t /\ x.round = r } }

RExistsPrevoteQuorum(p, v, r)   == \E Q \in ByzQuorum : Q \subseteq RPrevoteSendersFor(p, v, r)
RExistsPrecommitQuorum(p, v, r) == \E Q \in ByzQuorum : Q \subseteq RPrecommitSendersFor(p, v, r)
RExistsAnyPrevoteQuorum(p, r)   == \E Q \in ByzQuorum : Q \subseteq RSendersOfTypeAtRound(p, "Prevote", r)
RExistsAnyPrecommitQuorum(p, r) == \E Q \in ByzQuorum : Q \subseteq RSendersOfTypeAtRound(p, "Precommit", r)

RSendersOfAnyMessageAt(p, r) ==
         RSendersOfTypeAtRound(p, "Proposal", r)
    \cup RSendersOfTypeAtRound(p, "Prevote", r)
    \cup RSendersOfTypeAtRound(p, "Precommit", r)

(***************************************************************************)
(* Broadcasting: record the send time and self-deliver instantly.          *)
(***************************************************************************)
Broadcast(p, m) ==
  /\ sentTime' = [sentTime EXCEPT ![m] = now]
  /\ rcvd'     = [rcvd     EXCEPT ![p] = @ \cup {m}]

\* Reset all timers when entering round r: arm the propose timer, clear rest.
\* (Algorithm 1 line 21: StartRound schedules timeoutPropose(round).)
ResetTimersFor(p, r) ==
  [k \in TimerType |-> IF k = "propose" THEN now + TimeoutPropose(r) ELSE OFF]

(***************************************************************************)
(* Honest actions.                                                         *)
(*                                                                         *)
(* The progress actions (Propose / OnProposal* / OnPrevoteQuorum* /        *)
(* OnPrecommitQuorumValue) mirror TendermintByzantine, with two systematic *)
(* changes: (a) message reads are over rcvd[p] (the R* helpers), not the   *)
(* global pool; (b) sending uses Broadcast (records send time and          *)
(* self-delivers). The OnTimeout* actions are gated on now >= deadline     *)
(* (no oracle). The Schedule* actions arm deadlines on the first polka.    *)
(***************************************************************************)

\* === Lines 14-19: if p is the proposer, send a proposal ===================
Propose(p) ==
  /\ step[p] = "propose"
  /\ Proposer[round[p]] = p                                        \* line 14
  /\ ~ \E msg \in sent :
         msg.type = "Proposal" /\ msg.round = round[p] /\ msg.sender = p
  /\ \E v \in IF valid[p].value # nil                              \* line 15
              THEN {valid[p].value}                                \* line 16
              ELSE getValue :                                      \* line 18
       Broadcast(p, Proposal(p, round[p], v, valid[p].round))
  /\ UNCHANGED << round, step, locked, valid, decision, timer, now, enteredAt, decidedRound >>

\* === Lines 57-60: propose timeout elapsed; give up and prevote nil ========
OnTimeoutPropose(p) ==
  /\ step[p] = "propose"                                           \* line 58
  /\ timer[p]["propose"] # OFF /\ now >= timer[p]["propose"]       \* line 57 (timer fired)
  /\ Broadcast(p, Prevote(p, round[p], nil))                       \* line 59
  /\ step'  = [step  EXCEPT ![p] = "prevote"]                      \* line 60
  /\ timer' = [timer EXCEPT ![p]["propose"] = OFF]
  /\ UNCHANGED << round, locked, valid, decision, now, enteredAt, decidedRound >>

\* === Lines 22-27: upon fresh proposal (vr = -1), send prevote =============
OnProposalNoPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :           \* line 22
       /\ prop.validRound = -1
       /\ LET v == prop.value
              voteValueID ==
                IF Valid(v) /\ (locked[p].round = -1 \/ locked[p].value = v)
                THEN v                                             \* lines 23-24
                ELSE nil                                           \* lines 25-26
          IN Broadcast(p, Prevote(p, round[p], voteValueID))
  /\ step'  = [step  EXCEPT ![p] = "prevote"]                      \* line 27
  /\ timer' = [timer EXCEPT ![p]["propose"] = OFF]
  /\ UNCHANGED << round, locked, valid, decision, now, enteredAt, decidedRound >>

\* === Lines 28-33: upon proposal with Proof-of-Lock + prevote polka ========
OnProposalWithPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :     \* line 28
       /\ RExistsPrevoteQuorum(p, prop.value, prop.validRound)
       /\ prop.validRound \in Range(0, round[p])
       /\ LET v  == prop.value
              vr == prop.validRound
              voteValueID ==
                IF Valid(v) /\ (locked[p].round <= vr \/ locked[p].value = v)
                THEN v                                             \* lines 29-30
                ELSE nil                                           \* lines 31-32
          IN Broadcast(p, Prevote(p, round[p], voteValueID))
  /\ step'  = [step  EXCEPT ![p] = "prevote"]                      \* line 33
  /\ timer' = [timer EXCEPT ![p]["propose"] = OFF]
  /\ UNCHANGED << round, locked, valid, decision, now, enteredAt, decidedRound >>

\* === Lines 34-35: upon any-value prevote polka; schedule prevote timeout ==
ScheduleTimeoutPrevote(p) ==
  /\ step[p] = "prevote"
  /\ RExistsAnyPrevoteQuorum(p, round[p])                          \* line 34
  /\ timer[p]["prevote"] = OFF
  /\ timer' = [timer EXCEPT ![p]["prevote"] = now + TimeoutPrevote(round[p])] \* line 35
  /\ UNCHANGED << round, step, locked, valid, decision, sentTime, rcvd, now, enteredAt, decidedRound >>

\* === Lines 36-43, upon proposal + prevote polka, when step = prevote ======
OnPrevoteQuorumValueFirstTimeAt(p, prop) ==
  /\ step[p] = "prevote"                                           \* line 37
  /\ prop \in RProposalsFromProposerAt(p, round[p])                \* line 36
  /\ RExistsPrevoteQuorum(p, prop.value, round[p])
  /\ Valid(prop.value)
  /\ locked' = [locked EXCEPT ![p] =                               \* lines 38-39
                   [value |-> prop.value, round |-> round[p]]]
  /\ Broadcast(p, Precommit(p, round[p], prop.value))              \* line 40
  /\ step' = [step EXCEPT ![p] = "precommit"]                      \* line 41
  /\ valid' = [valid EXCEPT ![p] =                                 \* lines 42-43
                  [value |-> prop.value, round |-> round[p]]]
  /\ UNCHANGED << round, decision, timer, now, enteredAt, decidedRound >>

OnPrevoteQuorumValueFirstTime(p) ==
  /\ step[p] = "prevote"                                           \* line 37
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]):            \* line 36
       /\ RExistsPrevoteQuorum(p, prop.value, round[p])
       /\ Valid(prop.value)
       /\ LET v == prop.value
              newRecord == [value |-> v, round |-> round[p]]
          IN /\ locked' = [locked EXCEPT ![p] = newRecord]         \* lines 38-39
             /\ Broadcast(p, Precommit(p, round[p], v))            \* line 40
             /\ step'   = [step EXCEPT ![p] = "precommit"]         \* line 41
             /\ valid'  = [valid EXCEPT ![p] = newRecord]          \* lines 42-43
  /\ UNCHANGED << round, decision, timer, now, enteredAt, decidedRound >>

\* === Lines 36-43, upon proposal + prevote polka, when step >= precommit ===
OnPrevoteQuorumValueLateUpdate(p) ==
  /\ step[p] \in {"precommit", "decided"}
  /\ valid[p].round < round[p]
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :           \* line 36
       /\ RExistsPrevoteQuorum(p, prop.value, round[p])
       /\ Valid(prop.value)
       /\ valid' = [valid EXCEPT ![p] =                            \* lines 42-43
                      [value |-> prop.value, round |-> round[p]]]
  /\ UNCHANGED << round, step, locked, decision, sentTime, rcvd, timer, now, enteredAt, decidedRound >>

\* === Lines 44-46: upon polka of nil prevotes, send nil precommit ==========
OnPrevoteQuorumNil(p) ==
  /\ step[p] = "prevote"
  /\ RExistsPrevoteQuorum(p, nil, round[p])                        \* line 44
  /\ Broadcast(p, Precommit(p, round[p], nil))                     \* line 45
  /\ step' = [step EXCEPT ![p] = "precommit"]                      \* line 46
  /\ UNCHANGED << round, locked, valid, decision, timer, now, enteredAt, decidedRound >>

\* === Lines 61-64: prevote timeout elapsed; give up and precommit nil ======
OnTimeoutPrevote(p) ==
  /\ step[p] = "prevote"                                           \* line 62
  /\ timer[p]["prevote"] # OFF /\ now >= timer[p]["prevote"]       \* line 61 (timer fired)
  /\ Broadcast(p, Precommit(p, round[p], nil))                     \* line 63
  /\ step'  = [step  EXCEPT ![p] = "precommit"]                    \* line 64
  /\ timer' = [timer EXCEPT ![p]["prevote"] = OFF]
  /\ UNCHANGED << round, locked, valid, decision, now, enteredAt, decidedRound >>

\* === Lines 47-48: upon any-value precommit quorum; schedule precommit TO ==
ScheduleTimeoutPrecommit(p) ==
  /\ RExistsAnyPrecommitQuorum(p, round[p])                        \* line 47
  /\ timer[p]["precommit"] = OFF
  /\ step[p] # "decided"
  /\ timer' = [timer EXCEPT ![p]["precommit"] = now + TimeoutPrecommit(round[p])] \* line 48
  /\ UNCHANGED << round, step, locked, valid, decision, sentTime, rcvd, now, enteredAt, decidedRound >>

\* === Lines 49-54: upon proposal + precommit quorum, decide value ===========
OnPrecommitQuorumValue(p) ==
  /\ decision[p] = nil
  /\ \E r \in Rounds: \E prop \in RProposalsFromProposerAt(p, r):  \* line 49
       /\ RExistsPrecommitQuorum(p, prop.value, r)
       /\ Valid(prop.value)                                        \* line 50
       /\ decision' = [decision EXCEPT ![p] = prop.value]          \* line 51
       /\ step'     = [step     EXCEPT ![p] = "decided"]
       /\ decidedRound' = [decidedRound EXCEPT ![p] = r]
  /\ UNCHANGED << round, locked, valid, sentTime, rcvd, timer, now, enteredAt >>

\* === Lines 65-67: precommit timeout elapsed; start the next round =========
\* The give-up that advances the round. Resets all timers via ResetTimersFor
\* (arms the propose timer for the new round, clears prevote/precommit).
OnTimeoutPrecommit(p) ==
  /\ step[p] # "decided"                                           \* line 66
  /\ timer[p]["precommit"] # OFF /\ now >= timer[p]["precommit"]   \* lines 65-66 (timer fired)
  /\ round' = [round EXCEPT ![p] = round[p] + 1]                   \* line 67
  /\ step'  = [step  EXCEPT ![p] = "propose"]
  /\ timer' = [timer EXCEPT ![p] = ResetTimersFor(p, round[p] + 1)]
  /\ enteredAt' = [enteredAt EXCEPT ![p][round[p] + 1] = now]
  /\ UNCHANGED << locked, valid, decision, sentTime, rcvd, now, decidedRound >>

\* === Lines 55-56: upon a weak quorum of senders at a higher round =========
\* Catch-up. WeakQuorum = f+1 includes an honest sender genuinely at the
\* higher round, so the skip is safe. Resets all timers. Never
\* gated on the clock (it is sound catch-up in any phase) and touches only
\* round/step/timers, so it is invisible to the safety refinement.
SkipRound(p, r) ==
  /\ step[p] # "decided"
  /\ \E W \in WeakQuorum: W \subseteq RSendersOfAnyMessageAt(p, r) \* line 55, upon
  /\ r > round[p]                                                  \* line 55, with
  /\ round' = [round EXCEPT ![p] = r]                              \* line 56
  /\ step'  = [step  EXCEPT ![p] = "propose"]
  /\ timer' = [timer EXCEPT ![p] = ResetTimersFor(p, r)]
  /\ enteredAt' = [enteredAt EXCEPT ![p][r] = now]
  /\ UNCHANGED << locked, valid, decision, sentTime, rcvd, now, decidedRound >>

(***************************************************************************)
(* Byzantine message activation. The action represents the first correct   *)
(* receipt of a Byzantine message. It records that receipt in rcvd[c] and  *)
(* starts the paper's second Gossip deadline. Byzantine messages that      *)
(* never reach a correct validator need no state transition.               *)
(***************************************************************************)
FaultyStep(p) ==
  /\ \E m \in Message, c \in Honest :
       /\ m.sender = p
       /\ sentTime[m] = OFF
       /\ sentTime' = [sentTime EXCEPT ![m] = now]
       /\ rcvd' = [rcvd EXCEPT ![c] = @ \cup {m}]
  /\ UNCHANGED << round, step, locked, valid, decision, timer, now, enteredAt, decidedRound >>

(***************************************************************************)
(* Network: deliver broadcast messages to an honest validator. Batched --  *)
(* one step delivers ALL messages currently available to p. The adversary  *)
(* still controls WHEN delivery happens (the clock may advance with        *)
(* messages undelivered), but the strict upper bound, delivery before the  *)
(* paper deadline, is enforced on the clock (see Tick).                    *)
(***************************************************************************)
DeliveryDeadline(m) == (IF sentTime[m] >= GST THEN sentTime[m] ELSE GST) + Delta

\* Activated messages not yet received by p.
Available(p) == { m \in sent : m \notin rcvd[p] /\ now >= sentTime[m] }

Deliver(p) ==
  /\ Available(p) # {}
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup Available(p)]
  /\ UNCHANGED << round, step, locked, valid, decision, sentTime, timer, now, enteredAt, decidedRound >>

(***************************************************************************)
(* Time. `Tick` advances the clock by one. Two constraints:                *)
(* - DELIVERY DEADLINES: time may not pass any pending message's deadline  *)
(*     max(sendTime, GST) + Delta -- this enforces bounded delay after GST.*)
(* - MAXIMAL PROGRESS: time may not pass while any honest validator has an *)
(*     enabled computation step. This makes computation instantaneous      *)
(*     relative to the clock, so a validator that has received a polka     *)
(*     acts on it BEFORE the timeout deadline is reached.                  *)
(***************************************************************************)
PendingDeliveries == { pm \in Honest \X sent : pm[2] \notin rcvd[pm[1]] }

\* State predicate: does honest p have an enabled computation step right now?
\* Mirrors the enabling guards of HonestStep(p) without primed variables.
CanCompute(p) ==
  \/ step[p] = "propose" /\ Proposer[round[p]] = p
       /\ ~ \E msg \in sent :
              msg.type = "Proposal" /\ msg.round = round[p] /\ msg.sender = p
  \/ step[p] = "propose"
       /\ timer[p]["propose"] # OFF /\ now >= timer[p]["propose"]
  \/ step[p] = "propose"
       /\ \E prop \in RProposalsFromProposerAt(p, round[p]) : prop.validRound = -1
  \/ step[p] = "propose"
       /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
            RExistsPrevoteQuorum(p, prop.value, prop.validRound)
            /\ prop.validRound \in Range(0, round[p])
  \/ step[p] = "prevote"
       /\ timer[p]["prevote"] = OFF /\ RExistsAnyPrevoteQuorum(p, round[p])
  \/ step[p] = "prevote"
       /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
            RExistsPrevoteQuorum(p, prop.value, round[p]) /\ Valid(prop.value)
  \/ step[p] \in {"precommit", "decided"} /\ valid[p].round < round[p]
       /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
            RExistsPrevoteQuorum(p, prop.value, round[p]) /\ Valid(prop.value)
  \/ step[p] = "prevote" /\ RExistsPrevoteQuorum(p, nil, round[p])
  \/ step[p] = "prevote"
       /\ timer[p]["prevote"] # OFF /\ now >= timer[p]["prevote"]
  \/ step[p] # "decided"
       /\ timer[p]["precommit"] = OFF /\ RExistsAnyPrecommitQuorum(p, round[p])
  \/ decision[p] = nil
       /\ \E r \in Rounds : \E prop \in RProposalsFromProposerAt(p, r) :
            RExistsPrecommitQuorum(p, prop.value, r) /\ Valid(prop.value)
  \/ step[p] # "decided"
       /\ timer[p]["precommit"] # OFF /\ now >= timer[p]["precommit"]
  \/ step[p] # "decided"
       /\ \E r \in Rounds :
            (\E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, r))
            /\ r > round[p]

\* A scheduled timer for kind k is live only while p is in the step whose
\* OnTimeout* it guards (a dead timer left in timer[p][k] does not block Tick).
TimerLive(p, k) ==
  CASE k = "propose"   -> step[p] = "propose"
    [] k = "prevote"   -> step[p] = "prevote"
    [] k = "precommit" -> step[p] # "decided"

\* Advancing time is only meaningful while something time-dependent is
\* pending: a message still to deliver, or a live scheduled timer not yet
\* at its deadline. Otherwise the system is quiescent (sound non-Zeno
\* condition; also keeps `now` -- hence the state graph -- finite for TLC).
TickUseful ==
  \/ PendingDeliveries # {}
  \/ \E p \in Honest, k \in TimerType :
       timer[p][k] # OFF /\ now < timer[p][k] /\ TimerLive(p, k)

Tick ==
  /\ TickUseful
  /\ ~ \E p \in Honest : CanCompute(p)                             \* maximal progress
  /\ \A pm \in PendingDeliveries : now + 1 < DeliveryDeadline(pm[2])
  /\ now' = now + 1
  /\ UNCHANGED << round, step, locked, valid, decision, sentTime, rcvd, timer, enteredAt, decidedRound >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
HonestStep(p) ==
  \/ Propose(p)
  \/ OnTimeoutPropose(p)
  \/ OnProposalNoPOL(p)
  \/ OnProposalWithPOL(p)
  \/ ScheduleTimeoutPrevote(p)
  \/ OnPrevoteQuorumValueFirstTime(p)
  \/ OnPrevoteQuorumValueLateUpdate(p)
  \/ OnPrevoteQuorumNil(p)
  \/ OnTimeoutPrevote(p)
  \/ ScheduleTimeoutPrecommit(p)
  \/ OnPrecommitQuorumValue(p)
  \/ OnTimeoutPrecommit(p)
  \/ \E r \in Rounds : SkipRound(p, r)

HonestNext(p) ==
  \/ HonestStep(p)
  \/ Deliver(p)

Next ==
  \/ \E p \in Honest : HonestNext(p)
  \/ \E p \in Faulty : FaultyStep(p)
  \/ Tick

(***************************************************************************)
(* Fairness.                                                               *)
(*                                                                         *)
(* Weak fairness on every honest computation and delivery action, and on   *)
(* Tick (so time progresses). After GST the clock-gated OnTimeout* actions *)
(* fire only at their deadline; WF on the progress actions drives a        *)
(* decision in a long-enough post-GST round. Faulty validators are NOT     *)
(* subject to fairness.                                                    *)
(***************************************************************************)
Fairness ==
  /\ \A p \in Honest :
       /\ WF_vars(Propose(p))
       /\ WF_vars(OnTimeoutPropose(p))
       /\ WF_vars(OnProposalNoPOL(p))
       /\ WF_vars(OnProposalWithPOL(p))
       /\ WF_vars(ScheduleTimeoutPrevote(p))
       /\ WF_vars(OnPrevoteQuorumValueFirstTime(p))
       /\ WF_vars(OnPrevoteQuorumValueLateUpdate(p))
       /\ WF_vars(OnPrevoteQuorumNil(p))
       /\ WF_vars(OnTimeoutPrevote(p))
       /\ WF_vars(ScheduleTimeoutPrecommit(p))
       /\ WF_vars(OnPrecommitQuorumValue(p))
       /\ WF_vars(OnTimeoutPrecommit(p))
       /\ \A r \in Rounds : WF_vars(SkipRound(p, r))
       /\ WF_vars(Deliver(p))
  /\ WF_vars(Tick)

(***************************************************************************)
(* Complete specification: safety + fairness.                              *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties (inherited by refinement onto TendermintByzantine;    *)
(* stated here so the MC can also check them as invariants).               *)
(***************************************************************************)
Agreement ==
  \A p, q \in Honest :
    decision[p] # nil /\ decision[q] # nil => decision[p] = decision[q]

Validity ==
  \A p \in Honest :
    decision[p] # nil => Valid(decision[p])

IntegrityStep ==
  \A p \in Honest :
    decision[p] # nil => decision'[p] = decision[p]

(***************************************************************************)
(* Liveness property.                                                      *)
(*                                                                         *)
(* The paper's proof selects one particular correct validator whose valid  *)
(* round dominates all correct locks, then needs that same validator to be *)
(* proposer later. Recurrence of merely some honest proposer is too weak.  *)
(***************************************************************************)

\* For every honest validator and every round bound, that validator is
\* proposer in some later round.
\* Equivalently, every honest validator is proposer infinitely often.
\*
\* A Byzantine proposer may remain silent. Therefore, proposer selection must
\* assign arbitrarily late rounds to honest validators, so termination does
\* not depend on Byzantine cooperation.
\*
\* Recurrence after every bound matters because GST is unknown and a new lock
\* may require selecting another later proposer round. One honest proposer
\* occurrence before these events is insufficient.
EveryHonestProposesAgain ==
  \A p \in Honest :
    \A rMin \in Rounds :
      \E r \in Rounds :
        r > rMin /\ Proposer[r] = p

TerminationConditions == EveryHonestProposesAgain

Termination ==
  TerminationConditions => (\A p \in Honest : <>(decision[p] # nil))

=============================================================================
\* Modification History
\* Last modified Aug 4 2026 by hvanz (Hernán Vanzetto)
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)
