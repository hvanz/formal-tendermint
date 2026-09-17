------------------- MODULE TendermintPartialSyncRefinement -------------------
(***************************************************************************)
(* Refinement of the partial-synchrony TendermintPartialSync.tla by        *)
(* the Byzantine TendermintByzantine.tla -- the bottom edge of the linear  *)
(* chain                                                                   *)
(*   TendermintVoting <- TendermintOperational <- TendermintByzantine <-   *)
(*   TendermintPartialSync.                                                *)
(* (B <- A reads "B refines A".) This is the SAFETY-INHERITANCE step:      *)
(* every behavior of the timered, partially-synchronous liveness spec is,  *)
(* under the mapping below, a behavior of TendermintByzantine, so the      *)
(* honest-scoped Agreement / Validity / Integrity already established for  *)
(* TendermintByzantine transfer to TendermintPartialSync for free.         *)
(*                                                                         *)
(* THE MAPPING (a near-identity; the clock/delivery state is projected     *)
(* away)                                                                   *)
(*   round, step, locked, valid, decision <- by identity (name)            *)
(*   sent <- the derived operator sent (support of sentTime in             *)
(*     TendermintPartialSync, no longer a variable).                       *)
(*   Validators, Values, Valid, Proposer, Faulty <- by identity (name)     *)
(*   ByzQuorum <- the DEFINED size-(2f+1) family of                        *)
(*   TendermintPartialSync WeakQuorum <- the DEFINED size-(f+1)            *)
(*   family of TendermintPartialSync The variables timer / sentTime /      *)
(*   rcvd / now / enteredAt / decidedRound are NOT in the mapping:         *)
(* TendermintByzantine does not mention them, so they are projected away.  *)
(*                                                                         *)
(* WHY THE SIMULATION IS A MONOTONICITY ARGUMENT                           *)
(*   Honest actions read only the per-validator received set rcvd[p] (the  *)
(*   R* helpers), not the global pool. The link to the global B!sent       *)
(*   guards is the system invariant                                        *)
(*     RcvdSubsetSent == \A p \in Honest : rcvd[p] \subseteq sent          *)
(*   (proved inductive here, together with TypeOK, as Inv). With it, an    *)
(*   R* guard over rcvd[p] IMPLIES the corresponding B! guard over sent    *)
(*   (the Mono* lemmas: subset of senders => the quorum/proposal witness   *)
(*   carries over). Sending: Broadcast / FaultyStep set                    *)
(*   sentTime' = [sentTime EXCEPT ![m] = now], and since now # OFF the     *)
(*   support grows by exactly {m} (the SentExtend lemma), so               *)
(*   sent' = sent \cup {m} = B!sent', matching B!'s pool update.           *)
(* - Schedule{Prevote,Precommit}Timeout touch only the projected-away      *)
(*   timer state, so they map to STUTTERING.                               *)
(* - Deliver and Tick change only rcvd / now (projected away), so they map *)
(*   to STUTTERING.                                                        *)
(* - the timer-gated give-ups OnTimeoutPropose / OnTimeoutPrevote /        *)
(*   OnTimeoutPrecommit map to TendermintByzantine's ungated give-ups      *)
(*   PrevoteNil / PrecommitNil / AdvanceRound (the timer guard is an extra *)
(*   restriction that only reduces behavior).                              *)
(* - SkipRound maps to B!SkipRound (timer resets are projected away).      *)
(*   Fairness is dropped: it only removes behaviors, so trace inclusion is *)
(*   preserved.                                                            *)
(*                                                                         *)
(* DISCHARGING TendermintByzantine's SYMBOLIC-QUORUM ASSUMEs               *)
(*   TendermintByzantine takes ByzQuorum / WeakQuorum as CONSTANTS with    *)
(*   the honest-intersection axioms. Here they are DEFINED by cardinality, *)
(*   so the instance's assumptions become proof obligations:               *)
(* - ByzQuorumType / WeakQuorumType : immediate from the definitions.      *)
(* - ByzQuorumIntersection / WeakQuorumHasHonest : re-stated as ASSUMEs in *)
(*   TendermintPartialSync (the pigeonhole facts; TLC-checked at           *)
(*   f=1), cited by name.                                                  *)
(* - ValidatorsNonEmpty (Validators # {}) and HonestNonEmpty (Honest # {}) *)
(*   : the cardinality assumptions of TendermintPartialSync                *)
(*   (|Validators| = 3f+1, |Faulty| <= f, both finite) yield these via     *)
(*   FiniteSetTheorems -- proved here (ValidatorsNonEmptyL /               *)
(*   HonestNonEmptyL).                                                     *)
(*                                                                         *)
(* MAIN RESULTS                                                            *)
(*   THEOREM InvProof == Spec => []Inv (TypeOK /\ RcvdSubsetSent)          *)
(*   THEOREM Refinement == Spec => B!Spec                                  *)
(*   THEOREM AgreementInv == Spec => []Agreement                           *)
(*   THEOREM ValidityInv == Spec => []Validity                             *)
(*   THEOREM IntegrityInv == Spec => []IntegrityStep                       *)
(*                                                                         *)
(* (Termination -- the conditional liveness property -- is a separate,     *)
(* still-deferred TLAPS effort; it is exercised by TLC in                  *)
(* TendermintPartialSyncMC. This module establishes SAFETY                 *)
(* inheritance only.)                                                      *)
(***************************************************************************)

EXTENDS TendermintPartialSync

(***************************************************************************)
(* The Byzantine spec, instanced under the near-identity mapping. Vars and *)
(* the constants Validators / Values / Valid / Proposer / Faulty map by    *)
(* name; only the symbolic quorum CONSTANTS are pointed at                 *)
(* TendermintPartialSync concrete (cardinality-defined) families. We       *)
(* instance the PROOF module TendermintByzantineRefinement (which EXTENDS  *)
(* TendermintByzantine) so its already-discharged Spec => []Agreement /    *)
(* Validity / Integrity theorems are in scope for the safety transfer      *)
(* below.                                                                  *)
(***************************************************************************)
B == INSTANCE TendermintByzantineRefinement
     WITH ByzQuorum <- ByzQuorum, WeakQuorum <- WeakQuorum

-----------------------------------------------------------------------------
(***************************************************************************)
(* Constructor coincidence lemmas: under the mapping every                 *)
(* TendermintByzantine constant / constructor / message-type operator      *)
(* equals its TendermintPartialSync namesake. Each is a one-line BY        *)
(* DEF, because the instance substitution is the identity on Proposer /    *)
(* Values / Valid and the constructors do not mention sent.                *)
(***************************************************************************)

\* Constants / constructors.
LEMMA NilCo == B!nil = nil
BY DEF B!nil, nil

LEMMA HonestCo == B!Honest = Honest
BY DEF B!Honest, Honest

LEMMA RoundsCo == B!Rounds = Rounds
BY DEF B!Rounds, Rounds

LEMMA getValueCo == B!getValue = getValue
BY DEF B!getValue, getValue

LEMMA RangeCo == \A a, b : B!Range(a, b) = Range(a, b)
BY DEF B!Range, Range

LEMMA ProposalCo   == \A a, b, c, d : B!Proposal(a, b, c, d) = Proposal(a, b, c, d)
BY DEF B!Proposal, Proposal
LEMMA PrevoteCo    == \A a, b, c : B!Prevote(a, b, c) = Prevote(a, b, c)
BY DEF B!Prevote, Prevote
LEMMA PrecommitCo  == \A a, b, c : B!Precommit(a, b, c) = Precommit(a, b, c)
BY DEF B!Precommit, Precommit

LEMMA MessageCo == B!Message = Message
BY NilCo
DEF B!Message, Message, B!ProposalMsg, ProposalMsg, B!PrevoteMsg, PrevoteMsg,
    B!PrecommitMsg, PrecommitMsg, B!ValuesOrNil, ValuesOrNil, B!Rounds, Rounds

-----------------------------------------------------------------------------
(***************************************************************************)
(* Well-typedness of constructed messages, and growth of the derived pool. *)
(***************************************************************************)

\* Honest validators are validators.
LEMMA HonestSubValidators == Honest \subseteq Validators
BY DEF Honest

\* Constructed messages are well-typed (members of Message).
LEMMA MsgProposal ==
  ASSUME NEW pp \in Validators, NEW rr \in Rounds, NEW vv \in Values, NEW vrr \in Rounds \cup {-1}
  PROVE  Proposal(pp, rr, vv, vrr) \in Message
BY DEF Proposal, ProposalMsg, Message

LEMMA MsgPrevote ==
  ASSUME NEW pp \in Validators, NEW rr \in Rounds, NEW vv \in ValuesOrNil
  PROVE  Prevote(pp, rr, vv) \in Message
BY DEF Prevote, PrevoteMsg, Message

LEMMA MsgPrecommit ==
  ASSUME NEW pp \in Validators, NEW rr \in Rounds, NEW vv \in ValuesOrNil
  PROVE  Precommit(pp, rr, vv) \in Message
BY DEF Precommit, PrecommitMsg, Message

\* A single sentTime update (Broadcast / FaultyStep) extends the support by {m}.
\* sent = { x \in Message : sentTime[x] # OFF }; setting sentTime[m] = now with
\* now \in Nat (so now # OFF) adds exactly m.
LEMMA SentExtend ==
  ASSUME TypeOK, NEW m \in Message, sentTime' = [sentTime EXCEPT ![m] = now]
  PROVE  sent' = sent \cup {m}
BY DEFS OFF, sent, TypeOK

-----------------------------------------------------------------------------
(***************************************************************************)
(* Monotonicity lemmas. With rcvd[p] \subseteq sent, an R* guard over      *)
(* rcvd[p] implies the corresponding TendermintByzantine (B!) guard over   *)
(* sent.                                                                   *)
(***************************************************************************)

LEMMA MonoProposals ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW r
  PROVE  RProposalsFromProposerAt(p, r) \subseteq B!ProposalsFromProposerAt(r)
BY DEF RProposalsFromProposerAt, RProposals,
       B!ProposalsFromProposerAt, B!SentProposals

LEMMA MonoPrevoteSenders ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW v, NEW r
  PROVE  RPrevoteSendersFor(p, v, r) \subseteq B!PrevoteSendersFor(v, r)
BY DEF RPrevoteSendersFor, RPrevotes,
       B!PrevoteSendersFor, B!PrevotesAt, B!SentPrevotes

LEMMA MonoPrecommitSenders ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW v, NEW r
  PROVE  RPrecommitSendersFor(p, v, r) \subseteq B!PrecommitSendersFor(v, r)
BY DEF RPrecommitSendersFor, RPrecommits,
       B!PrecommitSendersFor, B!PrecommitsAt, B!SentPrecommits

LEMMA MonoSendersOfType ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW t, NEW r
  PROVE  RSendersOfTypeAtRound(p, t, r) \subseteq B!SendersOfTypeAtRound(t, r)
BY DEF RSendersOfTypeAtRound, B!SendersOfTypeAtRound

LEMMA MonoSendersOfAny ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW r
  PROVE  RSendersOfAnyMessageAt(p, r) \subseteq B!SendersOfAnyMessageAt(r)
BY MonoSendersOfType DEF RSendersOfAnyMessageAt, B!SendersOfAnyMessageAt

LEMMA MonoExistsPrevoteQuorum ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW v, NEW r,
         RExistsPrevoteQuorum(p, v, r)
  PROVE  B!ExistsPrevoteQuorum(v, r)
BY MonoPrevoteSenders DEF RExistsPrevoteQuorum, B!ExistsPrevoteQuorum

LEMMA MonoExistsPrecommitQuorum ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW v, NEW r,
         RExistsPrecommitQuorum(p, v, r)
  PROVE  B!ExistsPrecommitQuorum(v, r)
BY MonoPrecommitSenders DEF RExistsPrecommitQuorum, B!ExistsPrecommitQuorum

LEMMA MonoExistsAnyPrevoteQuorum ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW r,
         RExistsAnyPrevoteQuorum(p, r)
  PROVE  B!ExistsAnyPrevoteQuorum(r)
BY MonoSendersOfType DEF RExistsAnyPrevoteQuorum, B!ExistsAnyPrevoteQuorum

LEMMA MonoExistsAnyPrecommitQuorum ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW r,
         RExistsAnyPrecommitQuorum(p, r)
  PROVE  B!ExistsAnyPrecommitQuorum(r)
BY MonoSendersOfType DEF RExistsAnyPrecommitQuorum, B!ExistsAnyPrecommitQuorum

-----------------------------------------------------------------------------
(***************************************************************************)
(* Discharge of TendermintByzantine's CONSTANT assumptions under the mapping.    *)
(***************************************************************************)

\* The two *Type assumptions are immediate from the cardinality definitions.
LEMMA ByzQuorumTypeL  == ByzQuorum \in SUBSET (SUBSET Validators)
BY DEF ByzQuorum
LEMMA WeakQuorumTypeL == WeakQuorum \in SUBSET (SUBSET Validators)
BY DEF WeakQuorum

\* Nonemptiness from the cardinality ASSUMEs alone (no FiniteSetTheorems):
\* if Honest = {} then Validators \subseteq Faulty, and with Faulty \subseteq
\* Validators that forces Validators = Faulty, hence 3f+1 = |Validators| =
\* |Faulty| <= f -- impossible for f \in Nat. Validators # {} then follows
\* because Honest \subseteq Validators is non-empty.
LEMMA HonestNonEmptyL == Honest # {}
<1> SUFFICES ASSUME Honest = {} PROVE FALSE
  OBVIOUS
<1>1. Validators \subseteq Faulty
  BY DEF Honest
<1>2. Validators = Faulty
  BY <1>1, FaultyType
<1>3. Cardinality(Validators) = Cardinality(Faulty)
  BY <1>2
<1>4. 3 * f + 1 <= f
  BY <1>3, ValidatorsCardinality, FaultyCardinality
<1>. QED
  BY <1>4, FaultBoundType

LEMMA ValidatorsNonEmptyL == Validators # {}
BY HonestNonEmptyL DEF Honest

-----------------------------------------------------------------------------
(***************************************************************************)
(* The system invariant: TypeOK and rcvd[p] \subseteq sent for honest p.   *)
(* rcvd[p] \subseteq sent is what links the per-validator R* guards to the *)
(* global B!sent guards in the refinement step below.                      *)
(***************************************************************************)
RcvdSubsetSent == \A p \in Honest : rcvd[p] \subseteq sent
Inv == TypeOK /\ RcvdSubsetSent

\* sent is a subset of Message (immediate from its definition).
LEMMA SentSubMessage == sent \subseteq Message
BY DEF sent

\* A received proposal's value is a real Value (not nil): the proposal lies
\* in rcvd[p] \subseteq sent \subseteq Message and, being a Proposal message,
\* carries value \in Values. Shared by the three propose / prevote-quorum
\* cases of InvProof, which each PICK such a proposal and then broadcast a
\* vote built from prop.value.
LEMMA RcvdProposalValue ==
  ASSUME NEW p \in Honest, rcvd[p] \subseteq sent, NEW r,
         NEW prop \in RProposalsFromProposerAt(p, r)
  PROVE  prop.value \in Values
BY SentSubMessage
DEF RProposalsFromProposerAt, RProposals, Message, ProposalMsg, PrevoteMsg, PrecommitMsg

\* RcvdSubsetSent is preserved when rcvd[p] and the support both grow by {m}
\* (a Broadcast step). The actor's set gains m, which sent' also gains; every
\* other validator's set is unchanged and still inside sent \subseteq sent'.
LEMMA RcvdExtendOne ==
  ASSUME TypeOK, RcvdSubsetSent, NEW p \in Honest, NEW m,
         rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}],
         sent' = sent \cup {m}
  PROVE  RcvdSubsetSent'
BY DEFS RcvdSubsetSent, TypeOK

(***************************************************************************)
(* The invariant Inv = TypeOK /\ RcvdSubsetSent is inductive. <1>2 is the  *)
(* inductive step: Inv is preserved by every action. Actions that leave    *)
(* sentTime and rcvd unchanged keep sent and rcvd[p] \subseteq sent        *)
(* trivially; the broadcasting / delivery / faulty actions are handled     *)
(* with SentExtend and the message-typedness lemmas.                       *)
(***************************************************************************)
THEOREM InvProof == Spec => []Inv
<1>1. Init => Inv
  BY T0ProposeType, TDeltaType
  DEFS Init, Inv, LockState, OFF, RcvdSubsetSent, Rounds, Step, TimeoutPropose, TimerType, TypeOK, ValuesOrNil
<1>2. ASSUME Inv, [Next]_vars PROVE Inv'
  <2> USE <1>2 DEF Inv
  <2>tok. TypeOK
    BY DEF Inv
  <2>rss. RcvdSubsetSent
    BY DEF Inv
  <2> HIDE DEF Inv
  <2>1. CASE Next
    <3>1. CASE \E p \in Honest : HonestNext(p)
      <4> SUFFICES ASSUME NEW p \in Honest, HonestNext(p) PROVE Inv'
        BY <3>1
      <4> p \in Validators
        BY HonestSubValidators
      <4> rcvd[p] \subseteq sent
        BY <2>rss DEF RcvdSubsetSent
      <4> round[p] \in Rounds /\ valid[p] \in LockState /\ rcvd[p] \in SUBSET Message
        BY <2>tok DEF TypeOK
      <4>1. CASE Propose(p)
        BY <2>rss, <2>tok, <4>1, MsgProposal, RcvdExtendOne, SentExtend
        DEFS Broadcast, getValue, Inv, LockState, Propose, TypeOK, ValuesOrNil
      <4>2. CASE OnTimeoutPropose(p)
        BY <2>rss, <2>tok, <4>2, MsgPrevote, RcvdExtendOne, SentExtend
        DEFS Broadcast, Inv, OFF, OnTimeoutPropose, Step, TypeOK, ValuesOrNil
      <4>3. CASE OnProposalNoPOL(p)
        <5>1. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
                /\ prop.validRound = -1
                /\ Broadcast(p, Prevote(p, round[p],
                    IF Valid(prop.value) /\ (locked[p].round = -1 \/ locked[p].value = prop.value)
                    THEN prop.value ELSE nil))
          BY <4>3 DEF OnProposalNoPOL
        <5> DEFINE vid == IF Valid(prop.value) /\ (locked[p].round = -1 \/ locked[p].value = prop.value)
                          THEN prop.value ELSE nil
        <5> DEFINE m == Prevote(p, round[p], vid)
        <5>4. vid \in ValuesOrNil
          BY <5>1, RcvdProposalValue DEF ValuesOrNil
        <5>5. m \in Message
          BY <5>4, MsgPrevote
        <5>6. /\ sentTime' = [sentTime EXCEPT ![m] = now]
              /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
          BY <5>1 DEF Broadcast
        <5>7. sent' = sent \cup {m}
          BY <5>5, <5>6, SentExtend, <2>tok
        <5>8. TypeOK'
          BY <4>3, <5>5, <5>6, <2>tok DEF OnProposalNoPOL, TypeOK, Step, OFF
        <5>9. RcvdSubsetSent'
          BY <5>6, <5>7, <2>tok, <2>rss, RcvdExtendOne
        <5>. QED
          BY <5>8, <5>9 DEF Inv
      <4>4. CASE OnProposalWithPOL(p)
        <5>1. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
                /\ RExistsPrevoteQuorum(p, prop.value, prop.validRound)
                /\ prop.validRound \in Range(0, round[p])
                /\ Broadcast(p, Prevote(p, round[p],
                    IF Valid(prop.value) /\ (locked[p].round <= prop.validRound \/ locked[p].value = prop.value)
                    THEN prop.value ELSE nil))
          BY <4>4 DEF OnProposalWithPOL
        <5> DEFINE vid == IF Valid(prop.value) /\ (locked[p].round <= prop.validRound \/ locked[p].value = prop.value)
                          THEN prop.value ELSE nil
        <5> DEFINE m == Prevote(p, round[p], vid)
        <5>5. m \in Message
          BY <5>1, RcvdProposalValue, MsgPrevote DEF ValuesOrNil
        <5>6. /\ sentTime' = [sentTime EXCEPT ![m] = now]
              /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
          BY <5>1 DEF Broadcast
        <5>8. TypeOK'
          BY <4>4, <5>5, <5>6, <2>tok DEF OnProposalWithPOL, TypeOK, Step, OFF
        <5>9. RcvdSubsetSent'
          BY <5>5, <5>6, <2>tok, <2>rss, SentExtend, RcvdExtendOne
        <5>. QED
          BY <5>8, <5>9 DEF Inv
      <4>5. CASE OnPrevoteQuorumValueFirstTime(p)
        <5>1. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
                /\ Valid(prop.value)
                /\ locked' = [locked EXCEPT ![p] = [value |-> prop.value, round |-> round[p]]]
                /\ Broadcast(p, Precommit(p, round[p], prop.value))
                /\ step' = [step EXCEPT ![p] = "precommit"]
                /\ valid' = [valid EXCEPT ![p] = [value |-> prop.value, round |-> round[p]]]
          BY <4>5 DEF OnPrevoteQuorumValueFirstTime
        <5> DEFINE m == Precommit(p, round[p], prop.value)
        <5>4. m \in Message
          BY <5>1, RcvdProposalValue, MsgPrecommit DEF ValuesOrNil
        <5>5. /\ sentTime' = [sentTime EXCEPT ![m] = now]
              /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
          BY <5>1 DEF Broadcast
        <5>7. [value |-> prop.value, round |-> round[p]] \in LockState
          BY <5>1, RcvdProposalValue DEF LockState, ValuesOrNil, Rounds
        <5>8. TypeOK'
          BY <2>tok, <4>5, <5>1, <5>4, <5>5, <5>7 DEFS OnPrevoteQuorumValueFirstTime, Step, TypeOK
        <5>9. RcvdSubsetSent'
          BY <2>tok, <2>rss, <5>4, <5>5, SentExtend, RcvdExtendOne
        <5>. QED
          BY <5>8, <5>9 DEF Inv
      <4>6. CASE OnPrevoteQuorumNil(p)
        BY <2>rss, <2>tok, <4>6, MsgPrecommit, RcvdExtendOne, SentExtend
        DEFS Broadcast, Inv, OnPrevoteQuorumNil, Step, TypeOK, ValuesOrNil
      <4>7. CASE OnTimeoutPrevote(p)
        BY <2>rss, <2>tok, <4>7, MsgPrecommit, RcvdExtendOne, SentExtend
        DEFS Broadcast, Inv, OFF, OnTimeoutPrevote, Step, TypeOK, ValuesOrNil
      <4>8. CASE ScheduleTimeoutPrevote(p)
        BY <2>rss, <2>tok, <4>8, T0PrevoteType, TDeltaType
        DEFS Inv, RcvdSubsetSent, Rounds, ScheduleTimeoutPrevote, sent, TimeoutPrevote, TimerType, TypeOK
      <4>9. CASE OnPrevoteQuorumValueLateUpdate(p)
        BY <2>rss, <2>tok, <4>9
        DEFS Inv, LockState, Message, OnPrevoteQuorumValueLateUpdate, PrecommitMsg, PrevoteMsg, ProposalMsg, RcvdSubsetSent, Rounds, RProposals, RProposalsFromProposerAt, sent, TypeOK, ValuesOrNil
      <4>10. CASE ScheduleTimeoutPrecommit(p)
        BY <2>rss, <2>tok, <4>10, T0PrecommitType, TDeltaType
        DEFS Inv, RcvdSubsetSent, Rounds, ScheduleTimeoutPrecommit, sent, TimeoutPrecommit, TimerType, TypeOK
      <4>11. CASE OnPrecommitQuorumValue(p)
        BY <2>rss, <2>tok, <4>11
        DEFS Inv, Message, OnPrecommitQuorumValue, PrecommitMsg, PrevoteMsg, ProposalMsg, RcvdSubsetSent, Rounds, RProposals, RProposalsFromProposerAt, sent, Step, TypeOK, ValuesOrNil
      <4>12. CASE OnTimeoutPrecommit(p)
        BY <2>rss, <2>tok, <4>12, T0ProposeType, TDeltaType
        DEFS Inv, OFF, OnTimeoutPrecommit, RcvdSubsetSent, ResetTimersFor, Rounds, sent, Step, TimeoutPropose, TimerType, TypeOK
      <4>13. CASE \E r \in Rounds : SkipRound(p, r)
        BY <2>rss, <2>tok, <4>13, T0ProposeType, TDeltaType
        DEFS Inv, OFF, RcvdSubsetSent, ResetTimersFor, Rounds, sent, SkipRound, Step, TimeoutPropose, TimerType, TypeOK
      <4>14. CASE Deliver(p)
        BY <2>rss, <2>tok, <4>14, SentSubMessage DEFS Available, Deliver, Inv, sent, TypeOK, RcvdSubsetSent
      <4>. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10,
          <4>11, <4>12, <4>13, <4>14 DEF HonestNext, HonestStep
    <3>2. CASE \E p \in Faulty : FaultyStep(p)
      <4> SUFFICES ASSUME NEW p \in Faulty, FaultyStep(p) PROVE Inv'
        BY <3>2
      <4> QED
        BY <2>rss, <2>tok, RcvdExtendOne, SentExtend DEFS FaultyStep, Inv, TypeOK
    <3>3. CASE Tick
      <4>1. /\ sentTime' = sentTime
            /\ rcvd' = rcvd
            /\ now' = now + 1
            /\ UNCHANGED << round, step, locked, valid, decision, timer,
                            enteredAt, decidedRound >>
        BY <3>3 DEF Tick
      <4>2. sent' = sent
        BY <4>1 DEF sent
      <4>3. TypeOK'
        BY <4>1, <2>tok DEF TypeOK
      <4>4. RcvdSubsetSent'
        BY <4>1, <4>2, <2>rss DEF RcvdSubsetSent
      <4>. QED
        BY <4>3, <4>4 DEF Inv
    <3>4. QED
      BY <2>1, <3>1, <3>2, <3>3 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <2>2, <2>tok, <2>rss DEF Inv, vars, TypeOK, RcvdSubsetSent, sent
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeOKInv == Spec => []TypeOK
BY InvProof, PTL DEF Inv

THEOREM TypeOKBothStates == ASSUME Spec PROVE [](TypeOK /\ TypeOK')
BY TypeOKInv, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The refinement theorem: every TendermintPartialSync behavior is a       *)
(* TendermintByzantine behavior under the mapping. The step simulation     *)
(* runs under the invariant Inv (so rcvd[p] \subseteq sent is available    *)
(* for the guard-side Mono* lemmas).                                       *)
(***************************************************************************)
THEOREM Refinement == Spec => B!Spec
<1>1. Init => B!Init
  \* The five mapped variables start identically; sent = {} maps to
  \* B!sent = {}. The clock/timer/delivery conjuncts of Init (sentTime,
  \* rcvd, timer, now) are projected away. nil and Honest coincide.
  BY NilCo, HonestCo DEF Init, B!Init, sent, OFF
<1>2. ASSUME Inv, [Next]_vars
      PROVE  [B!Next]_(B!vars)
  <2> USE NilCo, HonestCo, RoundsCo, getValueCo, RangeCo,
          ProposalCo, PrevoteCo, PrecommitCo, MessageCo
      DEF B!Next, B!vars
  <2>tok. TypeOK
    BY <1>2 DEF Inv
  <2>rss. RcvdSubsetSent
    BY <1>2 DEF Inv
  <2>1. CASE UNCHANGED vars
    BY <2>1 DEF vars, sent
  <2>2. CASE Next
    <3>1. CASE \E p \in Honest : HonestNext(p)
      <4> SUFFICES ASSUME NEW p \in Honest, HonestNext(p)
                   PROVE  [B!Next]_(B!vars)
        BY <3>1
      <4> p \in Validators
        BY HonestSubValidators
      <4>sub. rcvd[p] \subseteq sent
        BY <2>rss DEF RcvdSubsetSent
      <4> round[p] \in Rounds /\ valid[p] \in LockState
        BY <2>tok DEF TypeOK
      <4>1. CASE Propose(p)
        BY <2>tok, <4>1, MsgProposal, SentExtend
        DEFS B!ProposalsAt, B!Propose, B!SentProposals, Propose, Broadcast, getValue, LockState, ValuesOrNil
      <4>2. CASE OnTimeoutPropose(p)
        BY <2>tok, <4>2, MsgPrevote, SentExtend DEFS OnTimeoutPropose, B!PrevoteNil, Broadcast, ValuesOrNil
      <4>3. CASE OnProposalNoPOL(p)
        BY <2>tok, <4>3, <4>sub, MonoProposals, MsgPrevote, SentExtend, SentSubMessage
        DEFS B!OnProposalNoPOL, OnProposalNoPOL, Broadcast, Message, PrecommitMsg, PrevoteMsg, ProposalMsg, 
          RProposals, RProposalsFromProposerAt, ValuesOrNil
      <4>4. CASE OnProposalWithPOL(p)
        BY <2>tok, <4>4, <4>sub, MonoExistsPrevoteQuorum, MonoProposals, MsgPrevote, SentExtend, SentSubMessage
        DEFS B!OnProposalWithPOL, OnProposalWithPOL, Broadcast, Message, PrecommitMsg, PrevoteMsg, ProposalMsg, 
          RProposals, RProposalsFromProposerAt, ValuesOrNil
      <4>5. CASE OnPrevoteQuorumValueFirstTime(p)
        BY <2>tok, <4>5, <4>sub, MonoExistsPrevoteQuorum, MonoProposals, MsgPrecommit, SentExtend, SentSubMessage
        DEFS B!OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueFirstTime, Broadcast, Message, PrecommitMsg, PrevoteMsg, ProposalMsg, 
          RProposals, RProposalsFromProposerAt, ValuesOrNil
      <4>6. CASE OnPrevoteQuorumValueLateUpdate(p)
        BY <4>6, <4>sub, MonoExistsPrevoteQuorum, MonoProposals
        DEFS B!OnPrevoteQuorumValueLateUpdate, OnPrevoteQuorumValueLateUpdate, sent
      <4>7. CASE OnPrevoteQuorumNil(p)
        BY <2>tok, <4>7, <4>sub, MonoExistsPrevoteQuorum, MsgPrecommit, SentExtend
        DEFS B!OnPrevoteQuorumNil, Broadcast, OnPrevoteQuorumNil, ValuesOrNil
      <4>8. CASE OnTimeoutPrevote(p)
        BY <2>tok, <4>8, MsgPrecommit, SentExtend DEFS B!PrecommitNil, Broadcast, OnTimeoutPrevote, ValuesOrNil
      <4>9. CASE OnPrecommitQuorumValue(p)
        BY <4>9, <4>sub, MonoExistsPrecommitQuorum, MonoProposals
        DEFS B!OnPrecommitQuorumValue, OnPrecommitQuorumValue, sent
      <4>10. CASE OnTimeoutPrecommit(p)
        BY <4>10 DEFS B!AdvanceRound, OnTimeoutPrecommit, ResetTimersFor, sent
      <4>11. CASE \E r \in Rounds : SkipRound(p, r)
        BY <4>11, <4>sub, MonoSendersOfAny DEFS B!SkipRound, ResetTimersFor, sent, SkipRound
      <4>12. CASE ScheduleTimeoutPrevote(p)
        BY <4>12 DEF ScheduleTimeoutPrevote, sent
      <4>13. CASE ScheduleTimeoutPrecommit(p)
        BY <4>13 DEF ScheduleTimeoutPrecommit, sent
      <4>14. CASE Deliver(p)
        BY <4>14 DEF Deliver, sent
      <4>. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF HonestNext, HonestStep
    <3>2. CASE \E p \in Faulty : FaultyStep(p)
      BY <2>tok, <3>2, SentExtend DEFS B!FaultyStep, FaultyStep
    <3>3. CASE Tick
      BY <3>3 DEF Tick, sent
    <3>. QED
      BY <2>2, <3>1, <3>2, <3>3 DEF Next
  \* Combine the two [Next]_vars cases. Hide B!Next first so the goal stays
  \* an opaque atom -- otherwise the huge B!Next disjunction blows up the prover.
  <2> HIDE DEF B!Next
  <2>3. QED
    BY <1>2, <2>1, <2>2
<1>3. QED
  <2>1. Spec => [](Inv /\ [Next]_vars)
    BY InvProof, PTL DEF Spec
  <2>2. Spec => [][B!Next]_(B!vars)
    BY <1>2, <2>1, PTL
  <2>. QED
    BY <1>1, <2>2, PTL DEF Spec, B!Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* End-to-end safety transfer. TendermintByzantine's honest-scoped         *)
(* Agreement / Validity / Integrity (already proved in                     *)
(* TendermintByzantineRefinement, drawn from TendermintVoting) carry back  *)
(* unchanged: each mentions only decision (mapped by identity) over        *)
(* B!Honest = Honest, with B!nil = nil. Using the imported theorems        *)
(* requires discharging TendermintByzantine's constant assumptions under   *)
(* the mapping (the quorum facts and nonemptiness lemmas above, plus the   *)
(* TendermintPartialSync ASSUMEs cited by name).                           *)
(***************************************************************************)
THEOREM AgreementInv == Spec => []Agreement
<1>1. Spec => B!Spec
  BY Refinement
<1>2. B!Spec => []B!Agreement
  BY B!AgreementInv, HonestCo,
     ValidatorsNonEmptyL, HonestNonEmptyL, ByzQuorumTypeL, WeakQuorumTypeL,
     ValidIsBoolean, ValidNonEmpty, FaultyType, ProposerType,
     ByzQuorumIntersection, WeakQuorumHasHonest, PTL
  DEF B!Honest, Honest
<1>3. QED
  BY <1>1, <1>2, PTL DEF Agreement, B!Agreement, B!Honest, Honest, B!nil, nil

THEOREM ValidityInv == Spec => []Validity
<1>1. Spec => B!Spec
  BY Refinement
<1>2. B!Spec => []B!Validity
  BY B!ValidityInv, HonestCo,
     ValidatorsNonEmptyL, HonestNonEmptyL, ByzQuorumTypeL, WeakQuorumTypeL,
     ValidIsBoolean, ValidNonEmpty, FaultyType, ProposerType,
     ByzQuorumIntersection, WeakQuorumHasHonest, PTL
  DEF B!Honest, Honest
<1>3. QED
  BY <1>1, <1>2, PTL DEF Validity, B!Validity, B!Honest, Honest, B!nil, nil

THEOREM IntegrityInv == Spec => []IntegrityStep
<1>1. Spec => B!Spec
  BY Refinement
<1>2. B!Spec => []B!IntegrityStep
  BY B!IntegrityInv, HonestCo,
     ValidatorsNonEmptyL, HonestNonEmptyL, ByzQuorumTypeL, WeakQuorumTypeL,
     ValidIsBoolean, ValidNonEmpty, FaultyType, ProposerType,
     ByzQuorumIntersection, WeakQuorumHasHonest, PTL
  DEF B!Honest, Honest
<1>3. QED
  BY <1>1, <1>2, PTL DEF IntegrityStep, B!IntegrityStep, B!Honest, Honest, B!nil, nil

=============================================================================
\* Modification History
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)
