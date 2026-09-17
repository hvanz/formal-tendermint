--------------- MODULE TendermintPartialSyncTerminationCascadeInvariants -------
(***************************************************************************)
(*  The vocabulary of the cascade of paper Lemma 5. This module also holds *)
(*  the global safety invariants, the state split into Case A and Case B,  *)
(*  the decide step, and the entry window.                                 *)
(*                                                                         *)
(*  Every link below reads the vocabulary, so this module sits at the head *)
(*  of the chain. The vocabulary is CascadeDurable, CascadeDeadline,       *)
(*  ProposalStage, ProposalMilestone, DecideEvidence, CaseA, EarlyPolka,   *)
(*  DecideReady, CInv, CStep, DelivRegion and DecideRegion. The global     *)
(*  invariants are PrecommitOncePerRound, HonestProposalUnique,            *)
(*  ProposalValidRoundGap, ValidValueFromProposal, ValidStrictAtPropose,   *)
(*  ValidRoundFloor, ProposalJustified, PrecommitTimerLE, EntryWindowCore, *)
(*  PrecommitDeadlineNotPassed, ProposeTimerValue,                         *)
(*  PrevoteNeedsProposalOrTimeout and StepPastProposeHasPrevote. The two   *)
(*  temporal exports are QuorumDecides and Lemma5HypSplitBox.              *)
(*                                                                         *)
(* ...WithinRound extends ...Base only, and ...RoundProgress extends       *)
(* ...NonZeno, which also extends ...Base. The two modules are             *)
(* SIBLINGS. The cascade needs the within-round safety support AND the     *)
(* post-GST timing apparatus, so it is provable in neither one. This       *)
(* link extends both, and every link below inherits the pair through it.   *)
(*                                                                         *)
(* THE CHAIN. Link 1 of 4. Above: ...WithinRound and ...RoundProgress.     *)
(* Below: ...CascadeRegion.                                                *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationWithinRound,
        TendermintPartialSyncTerminationRoundProgress

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants that only this module can state.                      *)
(***************************************************************************)

\* ---- One precommit per correct validator per round ------------------------
\* Item 2 of the pair count of ...LockRetry, and a hypothesis of the cascade
\* ceiling below. It sits HERE, and not beside its prevote sibling
\* PrevoteOncePerRound in ...RoundProgress, because that module is checked
\* separately and is not edited by this work. This module sees everything the
\* proof needs: FreshHonestPrecommitEmitter for the round of a fresh correct
\* precommit, and SentInv for the old message.
PrecommitOncePerRound ==
  \A c \in Honest, r \in Rounds, v1 \in ValuesOrNil, v2 \in ValuesOrNil :
    (Precommit(c, r, v1) \in sent /\ Precommit(c, r, v2) \in sent) => v1 = v2

\*   The step half of the emitter. The FreshHonestPrecommitEmitter of
\*   ...RoundProgress carries the ROUND of a fresh correct precommit, and it
\*   does not carry the STEP. The step is the whole content of the count. All
\*   three broadcasters of a precommit are guarded by step = "prevote", and
\*   they are OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumNil and
\*   OnTimeoutPrevote. SentInv also forces a validator that already has a
\*   precommit out at its CURRENT round into step "precommit" or step
\*   "decided". The emitting action has to be NAMED, exactly as in
\*   FreshHonestPrevoteEmitter. Only its guard carries the equality on the
\*   step, and a bundled leaf over Next does not discharge it.
LEMMA FreshHonestPrecommitStep ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Precommit", mm.sender \in Honest
  PROVE  step[mm.sender] = "prevote"
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
\* A slot that was OFF and is now set PINS the activated message: any EXCEPT
\* that misses mm's slot would leave it OFF.
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now] => mm = m0
  BY <1>0 DEF TypeOK
<1>1. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>1, <1>pin DEFS FaultyStep, Honest
<1>2. CASE \E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                \/ OnTimeoutPrevote(p))
  BY <1>2, <1>pin DEFS Broadcast, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote, Precommit
<1>3. CASE \E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p) \/ OnProposalWithPOL(p))
  BY <1>3, <1>pin DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, Precommit, Prevote
<1>4. CASE \E p \in Honest : Propose(p)
  BY <1>4, <1>pin DEFS Broadcast, Precommit, Proposal, Propose
<1>5. CASE /\ ~(\E p \in Faulty : FaultyStep(p))
           /\ ~(\E p \in Honest : (OnPrevoteQuorumValueFirstTime(p) \/ OnPrevoteQuorumNil(p)
                                     \/ OnTimeoutPrevote(p)))
           /\ ~(\E p \in Honest : (OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                                     \/ OnProposalWithPOL(p)))
           /\ ~(\E p \in Honest : Propose(p))
  BY <1>0, <1>5 DEFS Deliver, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
    OnPrevoteQuorumValueLateUpdate, OnTimeoutPrecommit, ScheduleTimeoutPrecommit,
    ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA PrecommitOncePerRoundStepL ==
  ASSUME TypeOK, SentInv, [Next]_vars, PrecommitOncePerRound
  PROVE  PrecommitOncePerRound'
BY FreshHonestPrecommitEmitter, FreshHonestPrecommitStep, SentTimeStep
DEFS Honest, HonestSentOK, Message, Precommit, PrecommitMsg, PrecommitOncePerRound, sent, SentInv, TypeOK

THEOREM PrecommitOncePerRoundInv == ASSUME Spec PROVE []PrecommitOncePerRound
<1>1. PrecommitOncePerRound
  BY DEFS Init, OFF, PrecommitOncePerRound, sent, Spec
<1>2. [](TypeOK /\ SentInv /\ [Next]_vars)
  BY InvProof, SentInvInv, PTL DEF Spec, Inv
<1>3. [](PrecommitOncePerRound => PrecommitOncePerRound')
  BY <1>2, PrecommitOncePerRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proposal bookkeeping for the cascade.                                   *)
(*                                                                         *)
(*   Three safety invariants about the proposals of an HONEST proposer,    *)
(*   and the emitter lemma they share. Uniqueness gives lr < r on the      *)
(*   refusal branch of the cascade. Round r carries one proposal, so a     *)
(*   lock AT r holds the proposed value, and it cannot refuse that value.  *)
(*   The other two bound the staleness of a proposal's validRound. Propose *)
(*   broadcasts vr = valid[q].round at the propose instant. The proposer   *)
(*   can raise valid[q].round after that, inside the same clock instant.   *)
(*   vr can therefore lag the valid round that a later state reads.        *)
(***************************************************************************)

\* ---- An honest proposer sends at most one proposal per round -------------
HonestProposalUnique ==
  \A q \in Honest, rr \in Rounds, v1 \in Values, v2 \in Values,
     vr1 \in Rounds \cup {-1}, vr2 \in Rounds \cup {-1} :
    (Proposal(q, rr, v1, vr1) \in sent /\ Proposal(q, rr, v2, vr2) \in sent)
      => v1 = v2 /\ vr1 = vr2

\* ---- The validRound of a proposal, against the proposer's valid round ----
ProposalValidRoundGap ==
  \A q \in Honest, rr \in Rounds, v \in Values, vr \in Rounds \cup {-1} :
    Proposal(q, rr, v, vr) \in sent =>
      valid[q].round <= vr \/ valid[q].round >= rr

\* A nonempty valid record was read off a proposal from that round's
\* proposer. Both writers guard on prop \in RProposalsFromProposerAt(c,
\* round[c]), and rcvd[c] \subseteq sent.
ValidValueFromProposal ==
  \A c \in Honest : valid[c].round >= 0 =>
    \E vr2 \in Rounds \cup {-1} :
      Proposal(Proposer[valid[c].round], valid[c].round, valid[c].value, vr2)
        \in sent

-----------------------------------------------------------------------------
LEMMA FreshHonestProposalEmitter ==
  ASSUME TypeOK, [Next]_vars, NEW mm \in Message,
         mm \in sent', mm \notin sent,
         mm.type = "Proposal", mm.sender \in Honest
  PROVE  /\ mm.round = round[mm.sender]
         /\ mm.validRound = valid[mm.sender].round
         /\ step[mm.sender] = "propose"
         /\ (valid[mm.sender].value # nil
                => mm.value = valid[mm.sender].value)
         /\ sentTime'[mm] = now
         /\ ~ \E msg \in sent : /\ msg.type = "Proposal"
                                /\ msg.round = mm.round
                                /\ msg.sender = mm.sender
<1>0. sentTime[mm] = OFF /\ sentTime'[mm] # OFF
  BY DEF sent
<1>pin. \A m0 : sentTime' = [sentTime EXCEPT ![m0] = now] => mm = m0
  BY <1>0 DEF TypeOK
<1>1. CASE \E q \in Faulty : FaultyStep(q)
  <2>1. PICK q \in Faulty, m0 \in Message :
          m0.sender = q /\ sentTime' = [sentTime EXCEPT ![m0] = now]
    BY <1>1 DEF FaultyStep
  <2> QED
    BY <1>pin, <2>1 DEF Honest
<1>2. CASE \E q \in Honest : Propose(q)
  <2> PICK q \in Honest : Propose(q)
    BY <1>2
  <2>1. PICK v \in (IF valid[q].value # nil THEN {valid[q].value} ELSE getValue) :
          /\ sentTime' = [sentTime EXCEPT
                            ![Proposal(q, round[q], v, valid[q].round)] = now]
    BY DEFS Broadcast, Propose
  <2>2. mm = Proposal(q, round[q], v, valid[q].round)
    BY <1>pin, <2>1
  <2>3. mm.sender = q /\ mm.round = round[q] /\ mm.validRound = valid[q].round
          /\ mm.value = v
    BY <2>2 DEF Proposal
  <2>4. ~ \E msg \in sent : /\ msg.type = "Proposal"
                            /\ msg.round = round[q]
                            /\ msg.sender = q
    BY DEF Propose
  <2>5. step[q] = "propose"
    BY DEF Propose
  \* Propose reads the value out of valid[q] whenever that record is set.
  <2>6. valid[q].value # nil => v = valid[q].value
    BY <2>1
  <2>7. sentTime'[mm] = now
    BY <2>1, <2>2 DEF TypeOK
  <2> QED
    BY <2>3, <2>4, <2>5, <2>6, <2>7
\* The three prevote broadcasters and the three precommit broadcasters activate
\* a message whose `type` field is not "Proposal", and <1>pin pins mm to that
\* message. Every remaining action leaves sentTime fixed, against <1>0. The
\* cases stay SPLIT, as in FreshHonestPrecommitStep above: one bundled leaf
\* over all eleven actions exhausts the backend's search space.
<1>3. CASE \E q \in Honest : (OnTimeoutPropose(q) \/ OnProposalNoPOL(q)
                                \/ OnProposalWithPOL(q))
  BY <1>3, <1>pin
  DEFS Broadcast, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose,
       Precommit, Prevote
<1>4. CASE \E q \in Honest : (OnPrevoteQuorumValueFirstTime(q)
                                \/ OnPrevoteQuorumNil(q) \/ OnTimeoutPrevote(q))
  BY <1>4, <1>pin
  DEFS Broadcast, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
       OnTimeoutPrevote, Precommit, Prevote
<1>5. CASE /\ ~(\E q \in Faulty : FaultyStep(q))
           /\ ~(\E q \in Honest : Propose(q))
           /\ ~(\E q \in Honest : (OnTimeoutPropose(q) \/ OnProposalNoPOL(q)
                                     \/ OnProposalWithPOL(q)))
           /\ ~(\E q \in Honest : (OnPrevoteQuorumValueFirstTime(q)
                                     \/ OnPrevoteQuorumNil(q)
                                     \/ OnTimeoutPrevote(q)))
  BY <1>0, <1>5
  DEFS Deliver, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
       OnPrevoteQuorumValueLateUpdate, OnTimeoutPrecommit,
       ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

-----------------------------------------------------------------------------
LEMMA HonestProposalUniqueStepL ==
  ASSUME TypeOK, [Next]_vars, HonestProposalUnique
  PROVE  HonestProposalUnique'
<1> SUFFICES ASSUME NEW q \in Honest, NEW rr \in Rounds,
                    NEW v1 \in Values, NEW v2 \in Values,
                    NEW vr1 \in Rounds \cup {-1},
                    NEW vr2 \in Rounds \cup {-1},
                    Proposal(q, rr, v1, vr1) \in sent',
                    Proposal(q, rr, v2, vr2) \in sent'
             PROVE  v1 = v2 /\ vr1 = vr2
  BY DEF HonestProposalUnique
<1>m1. Proposal(q, rr, v1, vr1) \in Message
  BY HonestSubValidators, MsgProposal
<1>m2. Proposal(q, rr, v2, vr2) \in Message
  BY HonestSubValidators, MsgProposal
<1>f1. Proposal(q, rr, v1, vr1).type = "Proposal"
         /\ Proposal(q, rr, v1, vr1).sender = q
         /\ Proposal(q, rr, v1, vr1).round = rr
  BY DEF Proposal
<1>f2. Proposal(q, rr, v2, vr2).type = "Proposal"
         /\ Proposal(q, rr, v2, vr2).sender = q
         /\ Proposal(q, rr, v2, vr2).round = rr
  BY DEF Proposal
<1>1. CASE Proposal(q, rr, v1, vr1) \in sent /\ Proposal(q, rr, v2, vr2) \in sent
  BY <1>1 DEF HonestProposalUnique
<1>2. CASE Proposal(q, rr, v1, vr1) \notin sent
  <2>g. ~ \E msg \in sent : /\ msg.type = "Proposal"
                            /\ msg.round = rr
                            /\ msg.sender = q
    BY <1>2, <1>m1, <1>f1, FreshHonestProposalEmitter
  <2>2. Proposal(q, rr, v2, vr2) \notin sent
    BY <1>f2, <2>g
  <2>0. sentTime[Proposal(q, rr, v1, vr1)] = OFF
          /\ sentTime'[Proposal(q, rr, v1, vr1)] # OFF
          /\ sentTime[Proposal(q, rr, v2, vr2)] = OFF
          /\ sentTime'[Proposal(q, rr, v2, vr2)] # OFF
    BY <1>2, <2>2 DEF sent
  <2>3. sentTime' # sentTime
    BY <2>0
  <2>4. PICK m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
    BY <2>3, SentTimeStep
  <2>5. Proposal(q, rr, v1, vr1) = m0 /\ Proposal(q, rr, v2, vr2) = m0
    BY <1>m1, <1>m2, <2>0, <2>4 DEF TypeOK
  <2> QED
    BY <2>5 DEF Proposal
<1>3. CASE Proposal(q, rr, v2, vr2) \notin sent
  <2>g. ~ \E msg \in sent : /\ msg.type = "Proposal"
                            /\ msg.round = rr
                            /\ msg.sender = q
    BY <1>3, <1>m2, <1>f2, FreshHonestProposalEmitter
  <2>2. Proposal(q, rr, v1, vr1) \notin sent
    BY <1>f1, <2>g
  <2>0. sentTime[Proposal(q, rr, v1, vr1)] = OFF
          /\ sentTime'[Proposal(q, rr, v1, vr1)] # OFF
          /\ sentTime[Proposal(q, rr, v2, vr2)] = OFF
          /\ sentTime'[Proposal(q, rr, v2, vr2)] # OFF
    BY <1>3, <2>2 DEF sent
  <2>3. sentTime' # sentTime
    BY <2>0
  <2>4. PICK m0 : sentTime' = [sentTime EXCEPT ![m0] = now]
    BY <2>3, SentTimeStep
  <2>5. Proposal(q, rr, v1, vr1) = m0 /\ Proposal(q, rr, v2, vr2) = m0
    BY <1>m1, <1>m2, <2>0, <2>4 DEF TypeOK
  <2> QED
    BY <2>5 DEF Proposal
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM HonestProposalUniqueInv == ASSUME Spec PROVE []HonestProposalUnique
<1>1. HonestProposalUnique
  BY DEF Init, HonestProposalUnique, sent, Spec, OFF
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](HonestProposalUnique => HonestProposalUnique')
  BY <1>2, HonestProposalUniqueStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* Only the two OnPrevoteQuorumValue actions write valid[q], and each sets
\* valid[q].round to round[q]. Neither activates a proposal.
LEMMA ValidWriteRaisesToRound ==
  ASSUME TypeOK, [Next]_vars, NEW q \in Honest, valid'[q] # valid[q]
  PROVE  /\ valid'[q].round = round[q]
         /\ \A mm \in Message : mm.type = "Proposal" /\ mm \in sent' => mm \in sent
<1>1. CASE OnPrevoteQuorumValueFirstTime(q)
  <2>1. PICK prop \in RProposalsFromProposerAt(q, round[q]) :
          /\ valid' = [valid EXCEPT
                         ![q] = [value |-> prop.value, round |-> round[q]]]
          /\ sentTime' = [sentTime EXCEPT
                            ![Precommit(q, round[q], prop.value)] = now]
    BY <1>1 DEFS Broadcast, OnPrevoteQuorumValueFirstTime
  <2>2. valid'[q].round = round[q]
    BY <2>1 DEF TypeOK
  <2>3. \A mm \in Message : mm.type = "Proposal" /\ mm \in sent' => mm \in sent
    BY <2>1 DEFS Precommit, sent, TypeOK
  <2> QED
    BY <2>2, <2>3
<1>2. CASE OnPrevoteQuorumValueLateUpdate(q)
  <2>1. PICK prop \in RProposalsFromProposerAt(q, round[q]) :
          valid' = [valid EXCEPT
                      ![q] = [value |-> prop.value, round |-> round[q]]]
    BY <1>2 DEF OnPrevoteQuorumValueLateUpdate
  <2>2. sentTime' = sentTime
    BY <1>2 DEF OnPrevoteQuorumValueLateUpdate
  <2> QED
    BY <2>1, <2>2 DEFS sent, TypeOK
<1>3. CASE ~OnPrevoteQuorumValueFirstTime(q) /\ ~OnPrevoteQuorumValueLateUpdate(q)
  <2>1. valid'[q] = valid[q]
    BY <1>3
    DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next,
         OnPrecommitQuorumValue, OnPrevoteQuorumNil,
         OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
         OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
         OnTimeoutPrevote, OnTimeoutPropose, Propose,
         ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick,
         TypeOK, vars
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA ProposalValidRoundGapStepL ==
  ASSUME TypeOK, SentInv, [Next]_vars, ProposalValidRoundGap
  PROVE  ProposalValidRoundGap'
<1> SUFFICES ASSUME NEW q \in Honest, NEW rr \in Rounds, NEW v \in Values,
                    NEW vr \in Rounds \cup {-1},
                    Proposal(q, rr, v, vr) \in sent'
             PROVE  valid'[q].round <= vr \/ valid'[q].round >= rr
  BY DEF ProposalValidRoundGap
<1>m. Proposal(q, rr, v, vr) \in Message
        /\ Proposal(q, rr, v, vr).type = "Proposal"
        /\ Proposal(q, rr, v, vr).sender = q
        /\ Proposal(q, rr, v, vr).round = rr
        /\ Proposal(q, rr, v, vr).validRound = vr
  BY HonestSubValidators, MsgProposal DEF Proposal
\* Case 1: valid[q] is untouched. Either the proposal is old, and the
\* induction hypothesis applies unchanged, or it is fresh, and the emitter
\* gives vr = valid[q].round, the first disjunct.
<1>1. CASE valid'[q] = valid[q]
  <2>1. CASE Proposal(q, rr, v, vr) \in sent
    BY <1>1, <2>1 DEF ProposalValidRoundGap
  <2>2. CASE Proposal(q, rr, v, vr) \notin sent
    <3>1. vr = valid[q].round
      BY <1>m, <2>2, FreshHonestProposalEmitter
    <3>2. valid'[q].round = vr
      BY <1>1, <3>1
    <3>3. vr \in Int
      BY DEF Rounds
    <3>4. valid'[q].round <= vr
      BY <3>2, <3>3
    <3> QED
      BY <3>4
  <2> QED
    BY <2>1, <2>2
\* Case 2: valid[q] is written. The writer sets valid'[q].round = round[q]
\* and cannot activate a proposal, so the proposal is old and SentInv dates
\* its round below round[q]. That is the second disjunct.
<1>2. CASE valid'[q] # valid[q]
  <2>1. valid'[q].round = round[q]
    BY <1>2, ValidWriteRaisesToRound
  <2>2. Proposal(q, rr, v, vr) \in sent
    BY <1>m, <1>2, ValidWriteRaisesToRound
  <2>3. rr <= round[q]
    BY <1>m, <2>2 DEFS HonestSentOK, SentInv
  <2> QED
    BY <2>1, <2>3
<1> QED
  BY <1>1, <1>2

THEOREM ProposalValidRoundGapInv == ASSUME Spec PROVE []ProposalValidRoundGap
<1>1. ProposalValidRoundGap
  BY DEF Init, ProposalValidRoundGap, sent, Spec, OFF
<1>2. [](TypeOK /\ SentInv /\ [Next]_vars)
  BY InvProof, SentInvInv, PTL DEF Spec, Inv
<1>3. [](ProposalValidRoundGap => ProposalValidRoundGap')
  BY <1>2, ProposalValidRoundGapStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* A proposal record in the pool is an application of its own constructor.
\* ProposalMsg has five fields and PrevoteMsg / PrecommitMsg have four, so
\* the type field alone puts the record in ProposalMsg.
LEMMA ProposalRecordRebuild ==
  ASSUME NEW prop \in Message, prop.type = "Proposal"
  PROVE  /\ prop.value \in Values
         /\ prop.validRound \in Rounds \cup {-1}
         /\ prop.round \in Rounds
         /\ prop = Proposal(prop.sender, prop.round, prop.value,
                            prop.validRound)
BY DEFS Message, PrecommitMsg, PrevoteMsg, Proposal, ProposalMsg

\* The proposal witness behind a write to valid[c]. Sibling of
\* ValidWriteRaisesToRound, which reports the round only.
LEMMA ValidWriteReadsProposal ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, valid'[c] # valid[c]
  PROVE  \E prop \in RProposalsFromProposerAt(c, round[c]) :
           valid' = [valid EXCEPT
                       ![c] = [value |-> prop.value, round |-> round[c]]]
<1>1. CASE OnPrevoteQuorumValueFirstTime(c)
  BY <1>1 DEF OnPrevoteQuorumValueFirstTime
<1>2. CASE OnPrevoteQuorumValueLateUpdate(c)
  BY <1>2 DEF OnPrevoteQuorumValueLateUpdate
<1>3. CASE ~OnPrevoteQuorumValueFirstTime(c)
           /\ ~OnPrevoteQuorumValueLateUpdate(c)
  <2>1. valid'[c] = valid[c]
    BY <1>3
    DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next,
         OnPrecommitQuorumValue, OnPrevoteQuorumNil,
         OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
         OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit,
         OnTimeoutPrevote, OnTimeoutPropose, Propose,
         ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick,
         TypeOK, vars
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA ValidValueFromProposalStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, ValidValueFromProposal
  PROVE  ValidValueFromProposal'
<1> SUFFICES ASSUME NEW c \in Honest, valid'[c].round >= 0
             PROVE  \E vr2 \in Rounds \cup {-1} :
                      Proposal(Proposer[valid'[c].round], valid'[c].round,
                               valid'[c].value, vr2) \in sent'
  BY DEF ValidValueFromProposal
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>1. CASE valid'[c] = valid[c]
  <2>1. PICK vr2 \in Rounds \cup {-1} :
          Proposal(Proposer[valid[c].round], valid[c].round,
                   valid[c].value, vr2) \in sent
    BY <1>1 DEF ValidValueFromProposal
  <2> QED
    BY <1>1, <1>mono, <2>1
<1>2. CASE valid'[c] # valid[c]
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          valid' = [valid EXCEPT
                      ![c] = [value |-> prop.value, round |-> round[c]]]
    BY <1>2, ValidWriteReadsProposal
  <2>2. valid'[c].value = prop.value /\ valid'[c].round = round[c]
    BY <2>1 DEF TypeOK
  <2>3. /\ prop \in sent
        /\ prop.type = "Proposal"
        /\ prop.round = round[c]
        /\ prop.sender = Proposer[round[c]]
    BY DEFS RcvdSubsetSent, RProposals, RProposalsFromProposerAt
  <2>4. prop \in Message
    BY <2>3 DEF sent
  <2>5. /\ prop.validRound \in Rounds \cup {-1}
        /\ prop = Proposal(prop.sender, prop.round, prop.value,
                           prop.validRound)
    BY <2>3, <2>4, ProposalRecordRebuild
  <2>6. Proposal(Proposer[round[c]], round[c], prop.value, prop.validRound)
          \in sent
    BY <2>3, <2>5
  <2> QED
    BY <1>mono, <2>2, <2>5, <2>6
<1> QED
  BY <1>1, <1>2

THEOREM ValidValueFromProposalInv == ASSUME Spec PROVE []ValidValueFromProposal
<1>1. ValidValueFromProposal
  BY DEF Init, ValidValueFromProposal, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ValidValueFromProposal => ValidValueFromProposal')
  BY <1>2, ValidValueFromProposalStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* An honest proposal carries its own justification.                       *)
(*                                                                         *)
(*  Justified(rr, v, t) names the dated evidence behind a correct prevote  *)
(*  for a value. That evidence is the round-rr proposal for v. When the    *)
(*  proposal carries a proof of lock, it also holds the polka at the valid *)
(*  round of the proposal. Propose reads both out of valid[q].             *)
(*  ValidPrevoteBacked holds that polka in rcvd[q], so RcvdSubsetSent and  *)
(*  SentTimeLeNow date the whole justification at or below the propose     *)
(*  instant.                                                               *)
(*                                                                         *)
(*  Range(0, rr) is STRICT, and LockState types the valid round at Int.    *)
(*  The branch for the proof of lock therefore needs two bounds on         *)
(*  valid[q].round that TypeOK does not give. The valid round is below     *)
(*  round[q] at a propose step, and it is never below -1.                  *)
(***************************************************************************)

\*  No correct validator is at step "propose" with valid already written at
\*  its current round. The two writers of valid leave step outside "propose".
\*  Two actions ENTER step "propose", and they are OnTimeoutPrecommit and
\*  SkipRound. Both strictly raise the round, and both leave valid alone.
ValidStrictAtPropose ==
  \A c \in Honest : step[c] = "propose" => valid[c].round < round[c]

LEMMA ValidStrictAtProposeStepL ==
  ASSUME TypeOK, ValidBelowRound, [Next]_vars, ValidStrictAtPropose
  PROVE  ValidStrictAtPropose'
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, LockState,
  Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, ValidBelowRound,
  ValidStrictAtPropose, vars

THEOREM ValidStrictAtProposeInv == ASSUME Spec PROVE []ValidStrictAtPropose
<1>1. ValidStrictAtPropose
  BY DEFS Init, Spec, ValidStrictAtPropose
<1>2. [](TypeOK /\ ValidBelowRound /\ [Next]_vars)
  BY InvProof, ValidBelowRoundInv, PTL DEF Spec, Inv
<1>3. [](ValidStrictAtPropose => ValidStrictAtPropose')
  BY <1>2, ValidStrictAtProposeStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* The floor. Init sets -1, and the two writers set round[c] \in Nat. The
\* locked twin of this fact is LockRoundFloor in ...Dominator.
ValidRoundFloor == \A c \in Honest : valid[c].round >= -1

LEMMA ValidRoundFloorStepL ==
  ASSUME TypeOK, [Next]_vars, ValidRoundFloor
  PROVE  ValidRoundFloor'
BY DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, LockState,
  Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit,
  ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, ValidRoundFloor, vars

THEOREM ValidRoundFloorInv == ASSUME Spec PROVE []ValidRoundFloor
<1>1. ValidRoundFloor
  BY DEFS Init, Spec, ValidRoundFloor
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ValidRoundFloor => ValidRoundFloor')
  BY <1>2, ValidRoundFloorStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
ProposalJustified ==
  \A rr \in Rounds, v \in Values, vr \in Rounds \cup {-1}, t \in Nat :
    (  Proposer[rr] \in Honest
       /\ Proposal(Proposer[rr], rr, v, vr) \in sent
       /\ sentTime[Proposal(Proposer[rr], rr, v, vr)] <= t  )
      => Justified(rr, v, t)

\*   The fresh half. This lemma cannot be stated in the PRE-state, and its
\*   prevote counterpart FreshValuePrevoteEvidence can. The justification of a
\*   proposal IS the proposal, and the message is not in sent yet. The POLKA
\*   is already in the pre-state. It therefore travels by PolkaWeaken and then
\*   by PolkaMove, and only the outer Justified is built at the primed state.
LEMMA FreshProposalJustified ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, ValidStrictAtPropose,
         ValidRoundFloor, ValidPrevoteBacked, ValidValueFromProposal,
         [Next]_vars,
         NEW rr \in Rounds, NEW v \in Values,
         NEW vr \in Rounds \cup {-1}, NEW t \in Nat,
         Proposer[rr] \in Honest,
         Proposal(Proposer[rr], rr, v, vr) \in sent',
         Proposal(Proposer[rr], rr, v, vr) \notin sent,
         sentTime'[Proposal(Proposer[rr], rr, v, vr)] <= t
  PROVE  Justified(rr, v, t)'
<1> DEFINE q == Proposer[rr]
<1> DEFINE prop == Proposal(q, rr, v, vr)
<1>q. q \in Honest /\ q \in Validators
  BY HonestSubValidators
<1>m. /\ prop \in Message
      /\ prop.type = "Proposal"
      /\ prop.sender = q
      /\ prop.round = rr
      /\ prop.value = v
      /\ prop.validRound = vr
  BY <1>q, MsgProposal DEF Proposal
\* The emitter reports the round, the validRound, the propose step, the value
\* and the fresh timestamp of a correct proposal.
<1>e. /\ rr = round[q]
      /\ vr = valid[q].round
      /\ step[q] = "propose"
      /\ (valid[q].value # nil => v = valid[q].value)
      /\ sentTime'[prop] = now
  BY <1>m, <1>q, FreshHonestProposalEmitter
<1>n. now \in Nat /\ now <= t
  BY <1>e DEF TypeOK
<1>s. prop \in sent'
  OBVIOUS
<1>1. CASE vr = -1
  BY <1>1, <1>e, <1>m, <1>s DEF Justified
<1>2. CASE vr # -1
  <2>vr. vr \in Rounds
    BY <1>2
  <2>fl. vr >= 0
    BY <2>vr DEF Rounds
  <2>val. valid[q].round >= 0 /\ valid[q].round = vr
    BY <1>e, <2>fl
  \* Valid(valid[q].value) does NOT type the value: ValidIsBoolean constrains
  \* Valid on Values only. Read the type off the proposal behind the record.
  <2>vv. valid[q].value \in Values
    <3>1. PICK vr2 \in Rounds \cup {-1} :
            Proposal(Proposer[valid[q].round], valid[q].round,
                     valid[q].value, vr2) \in sent
      BY <1>q, <2>val DEF ValidValueFromProposal
    <3> QED
      BY <3>1
      DEFS Message, PrecommitMsg, PrevoteMsg, Proposal, ProposalMsg, sent
  <2>v. v = valid[q].value
    BY <1>e, <2>vv, NilNotInValues
  <2>pk. PolkaDated(vr, v, now)
    <3>1. RExistsPrevoteQuorum(q, valid[q].value, valid[q].round)
      BY <1>q, <2>val DEF ValidPrevoteBacked
    <3> QED
      BY <1>q, <2>v, <2>val, <2>vr, <2>vv, <3>1, ViewPolkaDated
      DEF ValuesOrNil
  <2>pkt. PolkaDated(vr, v, t)
    BY <1>n, <2>pk, <2>vr, PolkaWeaken DEF ValuesOrNil
  <2>pkp. PolkaDated(vr, v, t)'
    BY <2>pkt, PolkaMove
  <2>rng. vr \in B!Range(0, rr)
    <3>1. valid[q].round < round[q]
      BY <1>e, <1>q DEF ValidStrictAtPropose
    <3>2. vr < rr
      BY <1>e, <3>1
    <3>3. vr \in Int
      BY <2>vr DEF Rounds
    \* Range by NAME aborts tlapm with an arity error in this lattice. Unfold
    \* the instance operator B!Range instead, as ...RoundProgress does.
    <3> QED
      BY <2>fl, <3>2, <3>3 DEF B!Range
  <2> QED
    BY <1>e, <1>m, <1>s, <2>pkp, <2>rng DEF Justified
<1> QED
  BY <1>1, <1>2

LEMMA ProposalJustifiedStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, ValidStrictAtPropose,
         ValidRoundFloor, ValidPrevoteBacked, ValidValueFromProposal,
         [Next]_vars, ProposalJustified
  PROVE  ProposalJustified'
<1> SUFFICES ASSUME NEW rr \in Rounds, NEW v \in Values,
                    NEW vr \in Rounds \cup {-1},
                    NEW t \in Nat, Proposer[rr] \in Honest,
                    Proposal(Proposer[rr], rr, v, vr) \in sent',
                    sentTime'[Proposal(Proposer[rr], rr, v, vr)] <= t
             PROVE  Justified(rr, v, t)'
  BY DEF ProposalJustified
<1>m. Proposal(Proposer[rr], rr, v, vr) \in Message
  BY HonestSubValidators, MsgProposal
\* An old proposal keeps its timestamp, so the induction hypothesis applies and
\* JustifiedMove carries its conclusion across the step.
<1>1. CASE Proposal(Proposer[rr], rr, v, vr) \in sent
  <2>1. sentTime'[Proposal(Proposer[rr], rr, v, vr)]
          = sentTime[Proposal(Proposer[rr], rr, v, vr)]
    BY <1>1, <1>m, SentTimeFrozenStepL
    DEFS SentTimeFrozenPred, sent, vars
  <2>2. Justified(rr, v, t)
    BY <1>1, <2>1 DEF ProposalJustified
  <2> QED
    BY <2>2, JustifiedMove
<1>2. CASE Proposal(Proposer[rr], rr, v, vr) \notin sent
  BY <1>2, FreshProposalJustified
<1> QED
  BY <1>1, <1>2

THEOREM ProposalJustifiedInv == ASSUME Spec PROVE []ProposalJustified
<1>1. ProposalJustified
  BY DEFS Init, OFF, ProposalJustified, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
           /\ ValidStrictAtPropose /\ ValidRoundFloor /\ ValidPrevoteBacked
           /\ ValidValueFromProposal /\ [Next]_vars  )
  BY InvProof, SentInvInv, SentTimeLeNowInv, ValidStrictAtProposeInv,
     ValidRoundFloorInv, ValidPrevoteBackedInv, ValidValueFromProposalInv,
     PTL DEF Spec, Inv
<1>3. [](ProposalJustified => ProposalJustified')
  BY <1>2, ProposalJustifiedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The milestones of the cascade.                                          *)
(*                                                                         *)
(*  Each stage below is stated at ONE date expression, CascadeDeadline,    *)
(*  and never at a quantified date. A theorem with a ~> conclusion cites   *)
(*  at identity only, so a stage stated as ASSUME NEW T ... PROVE M(T) ~>  *)
(*  ... could not be used at two dates. Justified and PolkaDated grow with *)
(*  the date, and JustifiedWeaken and PolkaWeaken do the lifting. One      *)
(*  expression is therefore enough. The Case B leg gives its evidence at   *)
(*  the entry instant, and it weakens upwards. The Case A leg gives that   *)
(*  evidence at the deadline.                                              *)
(*                                                                         *)
(* RoundOrigin freezes enteredAt[p][r], so CascadeDeadline is an ordinary  *)
(* state expression that the milestone carries with it.                    *)
(***************************************************************************)

CascadeDurable(p, r) == RoundOrigin(p, r) /\ WRDurable(r)

CascadeDeadline(p, r) ==
  enteredAt[p][r] + 2 * Delta + TimeoutPrecommit(r - 1)

\* M1. Justified already carries the proposal, its date, its sender, its round,
\* its value and its proof-of-lock polka, so no separate ProposalDated operator
\* is needed here.
ProposalStage(p, r, T) ==
  /\ CascadeDurable(p, r)
  /\ \E v \in Values : Valid(v) /\ Justified(r, v, T)

\* M2. M1 plus a dated polka for the same value.
PolkaStage(p, r, T) ==
  /\ CascadeDurable(p, r)
  /\ \E v \in Values : /\ Valid(v)
                       /\ Justified(r, v, T)
                       /\ PolkaDated(r, v, T)

\*  The two milestones AT THE ONE DATE the cascade uses. Every temporal atom
\*  of the stages below is then an application to CONSTANTS. A boxed lemma,
\*  and a leads-to lemma, cite only at identity. A compound argument for the
\*  date under [] or <> does not match.
ProposalMilestone(p, r) == ProposalStage(p, r, CascadeDeadline(p, r))
PolkaMilestone(p, r)    == PolkaStage(p, r, CascadeDeadline(p, r))

\* M3. A latch, and it holds no clock conjunct. OnPrecommitQuorumValue has no
\* round guard: it reads \E rr \in Rounds : \E prop \in
\* RProposalsFromProposerAt(p, rr), so every correct process decides once the
\* quorum and the proposal reach it, whatever round it is in, and even if it
\* never precommitted at r itself.
DecideEvidence(r) ==
  \E v \in Values :
    /\ Valid(v)
    /\ \E vr \in Rounds \cup {-1} :
         Proposal(Proposer[r], r, v, vr) \in sent
    /\ \E Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent

-----------------------------------------------------------------------------
(***************************************************************************)
(* S0. The Case A and Case B state split.                                  *)
(*                                                                         *)
(*   Clause (3) of Lemma5Hyp bounds every correct lock by                  *)
(*   valid[Proposer[r]].round. The refusal branch of the cascade instead   *)
(*   needs that bound at the validRound vr of the round-r proposal. The    *)
(*   transfer fails in general. Propose broadcasts vr = valid[q].round at  *)
(*   the propose instant, and FirstToEnter orders the entries by the clock *)
(*   only. The proposer can therefore enter r, propose, and then raise     *)
(*   valid[q].round, all inside one clock instant and all before the       *)
(*   hypothesis state.                                                     *)
(*                                                                         *)
(* The staleness is BOUNDED. ProposalValidRoundGap gives                   *)
(* valid[q].round <= vr or valid[q].round >= r, and at a Lemma5Hyp state   *)
(* FirstToEnter and ValidBelowRound cap valid[q].round at r. So a stale vr *)
(* forces valid[q].round = r EXACTLY, and then ValidPrevoteBacked already  *)
(* holds a round-r polka for valid[q].value in rcvd[q]. Round r is past    *)
(* its prevote stage, and the cascade is already at its second milestone.  *)
(***************************************************************************)

CaseA(p, r) ==
  \A v \in Values, vr \in Rounds \cup {-1} :
    Proposal(Proposer[r], r, v, vr) \in sent => valid[Proposer[r]].round <= vr

\*  Case B's residue. The polka is dated at or below the entry of p, and not
\*  at the deadline. Every anchor of the argument has to sit at or below every
\*  correct round-r vote, and RoundOrigin dates those votes at or after the
\*  entry.
EarlyPolka(p, r) ==
  /\ CascadeDurable(p, r)
  /\ \E v \in Values, T \in Nat :
       /\ Valid(v)
       /\ T >= GST
       /\ T <= enteredAt[p][r]
       /\ PolkaDated(r, v, T)
       /\ Justified(r, v, T)

LEMMA CascadeDeadlineType ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, r > 0,
         enteredAt[p][r] # OFF
  PROVE  /\ CascadeDeadline(p, r) \in Nat
         /\ enteredAt[p][r] <= CascadeDeadline(p, r)
<1>1. enteredAt[p][r] \in Nat
  BY DEFS OFF, TypeOK
<1>2. r - 1 \in Nat
  BY DEF Rounds
<1>3. TimeoutPrecommit(r - 1) \in Nat
  BY <1>2, T0PrecommitType, TDeltaType DEF TimeoutPrecommit
<1> QED
  BY <1>1, <1>3, DeltaType DEF CascadeDeadline

LEMMA Lemma5HypDurable ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, Lemma5Hyp(p, r)
  PROVE  CascadeDurable(p, r)
<1>1. RoundOrigin(p, r)
  BY Lemma5HypImpliesRoundOrigin
<1>2. WRDurable(r)
  BY DEFS Lemma5Hyp, Lemma5Timeouts, WRDurable
<1> QED
  BY <1>1, <1>2 DEF CascadeDurable

\* THE SOUNDNESS STATEMENT of the split. Either clause (3) of Lemma5Hyp
\* transfers to the validRound of every round-r proposal, or the round already
\* carries a dated polka for the proposed value.
LEMMA Lemma5HypSplit ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, HonestProposalUnique,
         ProposalValidRoundGap, ProposalJustified, ValidBelowRound,
         ValidPrevoteBacked, ValidValueFromProposal,
         NEW p \in Honest, NEW r \in Rounds, Lemma5Hyp(p, r)
  PROVE  CaseA(p, r) \/ EarlyPolka(p, r)
<1> DEFINE q == Proposer[r]
<1>q. q \in Honest /\ q \in Validators
  BY HonestSubValidators DEF Lemma5Hyp
<1>d. CascadeDurable(p, r)
  BY Lemma5HypDurable
<1>now. /\ now \in Nat
        /\ enteredAt[p][r] = now
        /\ CascadeDeadline(p, r) \in Nat
        /\ now <= CascadeDeadline(p, r)
  <2>1. enteredAt[p][r] = now
    BY DEFS FirstToEnter, Lemma5Hyp
  <2>2. r > 0 /\ enteredAt[p][r] # OFF
    BY <2>1 DEFS Lemma5Hyp, OFF, TypeOK
  <2> QED
    BY <2>1, <2>2, CascadeDeadlineType DEF TypeOK
<1> SUFFICES ASSUME ~CaseA(p, r)
             PROVE  EarlyPolka(p, r)
  OBVIOUS
<1>1. PICK v \in Values, vr \in Rounds \cup {-1} :
        Proposal(q, r, v, vr) \in sent /\ ~(valid[q].round <= vr)
  BY DEF CaseA
\* The gap invariant turns the stale validRound into valid[q].round >= r, and
\* FirstToEnter with ValidBelowRound caps it at r.
<1>2. valid[q].round = r
  <2>1. valid[q].round >= r
    BY <1>1, <1>q DEF ProposalValidRoundGap
  <2>2. round[q] <= r
    BY <1>q DEFS FirstToEnter, Lemma5Hyp
  <2>3. valid[q].round <= round[q]
    BY <1>q DEF ValidBelowRound
  <2>ty. valid[q].round \in Int /\ round[q] \in Nat /\ r \in Nat
    BY <1>q DEFS LockState, Rounds, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, <2>ty
<1>3. valid[q].round >= 0
  BY <1>2 DEFS Lemma5Hyp, Rounds
<1>4. Valid(valid[q].value) /\ RExistsPrevoteQuorum(q, valid[q].value, r)
  BY <1>2, <1>3, <1>q DEF ValidPrevoteBacked
\* Uniqueness of the round-r proposal identifies the valid value with v. The
\* type of that value is read off the proposal record, not out of Valid.
<1>5. valid[q].value = v
  <2>1. PICK vr2 \in Rounds \cup {-1} :
          Proposal(Proposer[valid[q].round], valid[q].round,
                   valid[q].value, vr2) \in sent
    BY <1>3, <1>q DEF ValidValueFromProposal
  <2>2. Proposal(q, r, valid[q].value, vr2) \in sent
    BY <1>2, <2>1
  <2>3. valid[q].value \in Values
    BY <2>1
    DEFS Message, PrecommitMsg, PrevoteMsg, Proposal, ProposalMsg, sent
  <2> QED
    BY <1>1, <1>q, <2>2, <2>3 DEF HonestProposalUnique
<1>6. PolkaDated(r, v, now)
  BY <1>4, <1>5, <1>q, ViewPolkaDated DEF ValuesOrNil
<1>7. Justified(r, v, now)
  <2>1. Proposal(q, r, v, vr) \in Message
    BY <1>1, <1>q, MsgProposal
  <2>2. sentTime[Proposal(q, r, v, vr)] <= now
    BY <1>1, <2>1 DEFS sent, SentTimeLeNow
  <2> QED
    BY <1>1, <1>now, <2>2 DEFS Lemma5Hyp, ProposalJustified
\* The date of the polka is the entry of p, and it is NOT weakened up. Every
\* anchor of the Case B argument has to sit at or below every correct round-r
\* vote, and the deadline does not.
<1>8. now >= GST /\ now <= enteredAt[p][r]
  BY <1>now DEF Lemma5Hyp
<1> QED
  BY <1>4, <1>5, <1>6, <1>7, <1>8, <1>d, <1>now DEF EarlyPolka

\* Kept in a Spec-free context so PTL can necessitate it. Inside the temporal
\* assembly the hypothesis Spec is in scope and necessitation is refused there.
LEMMA Lemma5HypSplitBox ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow
              /\ HonestProposalUnique /\ ProposalValidRoundGap
              /\ ProposalJustified /\ ValidBelowRound /\ ValidPrevoteBacked
              /\ ValidValueFromProposal /\ Lemma5Hyp(p, r)
                => (CaseA(p, r) \/ EarlyPolka(p, r))  )
<1>1. TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow
      /\ HonestProposalUnique /\ ProposalValidRoundGap
      /\ ProposalJustified /\ ValidBelowRound /\ ValidPrevoteBacked
      /\ ValidValueFromProposal /\ Lemma5Hyp(p, r)
        => (CaseA(p, r) \/ EarlyPolka(p, r))
  BY Lemma5HypSplit
<1> QED
  BY <1>1, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* S4. A round-r decide certificate leads to a correct decision.           *)
(*                                                                         *)
(*  Two WF1 stages on one fixed correct process c. Deliver(c) absorbs      *)
(*  EVERY available message in one step. One step therefore carries the    *)
(*  proposal, and the whole precommit quorum, into rcvd[c] at once. The    *)
(*  finite conjunction over the quorum never has to be lifted through a    *)
(*  leads-to. OnPrecommitQuorumValue(c) then decides.                      *)
(*                                                                         *)
(*  This stage carries no clock conjunct. OnPrecommitQuorumValue has no    *)
(*  guard on the round. A correct process therefore decides on the         *)
(*  certificate whatever round it is in, and even if it never precommitted *)
(*  at r itself.                                                           *)
(***************************************************************************)

\* The guard of OnPrecommitQuorumValue at a NAMED round. The action's own
\* guard carries a round existential, and PTL must never read it.
DecideReady(c, r) ==
  \E prop \in RProposalsFromProposerAt(c, r) :
    /\ RExistsPrecommitQuorum(c, prop.value, r)
    /\ Valid(prop.value)

\*  The always-true invariant bundle, and the WF1 "next" action, as
\*  MODULE-LEVEL operators. A primed local DEFINE action trips the anonymizer
\*  in RuleWF1. To prime a real operator is fine.
CInv  == TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow
CStep == CInv /\ Next /\ CInv'

DelivRegion(c, r)  == DecideEvidence(r) /\ ~DecideReady(c, r)
DecideRegion(c, r) == DecideReady(c, r) /\ ~HasDecided(c)

\* CInv reads only the variables of `vars`, so a stuttering step preserves it.
\* The WF1 stability legs need this: [CStep]_vars admits UNCHANGED vars, and in
\* that disjunct the CInv' conjunct of CStep is not available.
LEMMA CInvStutters ==
  ASSUME CInv, UNCHANGED vars
  PROVE  CInv'
BY DEFS CInv, RcvdSubsetSent, sent, SentTimeLeNow, TypeOK, vars

\* ---- Stage one: one Deliver(c) step absorbs the whole certificate --------
\* Every sent message is available to c unless c already holds it, because
\* SentTimeLeNow dates it at or below the clock. Deliver(c) takes the whole
\* available set in one step, so rcvd'[c] holds every message of `sent`.
LEMMA DeliverAbsorbsSent ==
  ASSUME CInv, NEW c \in Honest, Deliver(c), NEW m \in Message, m \in sent
  PROVE  m \in rcvd'[c]
BY DEFS Available, CInv, Deliver, sent, SentTimeLeNow, TypeOK

LEMMA DelivRegionDelivers ==
  ASSUME CInv, NEW c \in Honest, NEW r \in Rounds, DelivRegion(c, r),
         Deliver(c)
  PROVE  DecideReady(c, r)'
<1>1. PICK v \in Values, vr \in Rounds \cup {-1}, Q \in ByzQuorum :
        /\ Valid(v)
        /\ Proposal(Proposer[r], r, v, vr) \in sent
        /\ \A s \in Q : Precommit(s, r, v) \in sent
  BY DEFS DecideEvidence, DelivRegion
<1>pt. Proposer[r] \in Validators
  BY ProposerType DEF Rounds
<1>p. /\ Proposal(Proposer[r], r, v, vr) \in Message
      /\ Proposal(Proposer[r], r, v, vr) \in rcvd'[c]
  BY <1>1, <1>pt, DeliverAbsorbsSent, MsgProposal
<1>2. Proposal(Proposer[r], r, v, vr) \in RProposalsFromProposerAt(c, r)'
  BY <1>p DEFS Proposal, RProposals, RProposalsFromProposerAt
<1>3. Q \subseteq RPrecommitSendersFor(c, v, r)'
  <2> SUFFICES ASSUME NEW s \in Q
               PROVE  s \in RPrecommitSendersFor(c, v, r)'
    OBVIOUS
  <2>1. s \in Validators
    BY DEF ByzQuorum
  <2>2. Precommit(s, r, v) \in Message /\ Precommit(s, r, v) \in rcvd'[c]
    BY <1>1, <2>1, DeliverAbsorbsSent, MsgPrecommit DEF ValuesOrNil
  <2> QED
    BY <2>2 DEFS Precommit, RPrecommits, RPrecommitSendersFor
<1>4. RExistsPrecommitQuorum(c, v, r)'
  BY <1>3 DEF RExistsPrecommitQuorum
<1> QED
  BY <1>1, <1>2, <1>4 DEFS DecideReady, Proposal

\* The enabledness leg, by contraposition: if c already held every sent
\* message, the certificate of DecideEvidence would be its own decide guard.
LEMMA DelivRegionEnabled ==
  ASSUME CInv, NEW c \in Honest, NEW r \in Rounds, DelivRegion(c, r)
  PROVE  ENABLED <<Deliver(c)>>_vars
<1> SUFFICES ASSUME \A m \in Message : m \in sent => m \in rcvd[c]
             PROVE  FALSE
  BY EnabledDeliver DEFS CInv, sent
<1>1. PICK v \in Values, vr \in Rounds \cup {-1}, Q \in ByzQuorum :
        /\ Valid(v)
        /\ Proposal(Proposer[r], r, v, vr) \in sent
        /\ \A s \in Q : Precommit(s, r, v) \in sent
  BY DEFS DecideEvidence, DelivRegion
<1>pt. Proposer[r] \in Validators
  BY ProposerType DEF Rounds
<1>p. Proposal(Proposer[r], r, v, vr) \in rcvd[c]
  BY <1>1, <1>pt, MsgProposal
<1>2. Proposal(Proposer[r], r, v, vr) \in RProposalsFromProposerAt(c, r)
  BY <1>p DEFS Proposal, RProposals, RProposalsFromProposerAt
<1>3. Q \subseteq RPrecommitSendersFor(c, v, r)
  <2> SUFFICES ASSUME NEW s \in Q
               PROVE  s \in RPrecommitSendersFor(c, v, r)
    OBVIOUS
  <2>1. s \in Validators
    BY DEF ByzQuorum
  <2>2. Precommit(s, r, v) \in Message /\ Precommit(s, r, v) \in rcvd[c]
    BY <1>1, <2>1, MsgPrecommit DEF ValuesOrNil
  <2> QED
    BY <2>2 DEFS Precommit, RPrecommits, RPrecommitSendersFor
<1>4. DecideReady(c, r)
  BY <1>1, <1>2, <1>3 DEFS DecideReady, Proposal, RExistsPrecommitQuorum
<1> QED
  BY <1>4 DEF DelivRegion

\* The stability leg. DecideEvidence reads `sent` and the constant Valid only,
\* so it is a latch.
LEMMA DelivRegionStable ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW r \in Rounds,
         DelivRegion(c, r)
  PROVE  (DelivRegion(c, r) \/ DecideReady(c, r))'
<1>1. DecideEvidence(r)'
  BY SentMonotoneStep DEFS DecideEvidence, DelivRegion
<1> QED
  BY <1>1 DEF DelivRegion

\* ---- Stage two: the decide action ----------------------------------------
LEMMA DecideRegionDecides ==
  ASSUME CInv, NEW c \in Honest, NEW r \in Rounds, DecideRegion(c, r),
         OnPrecommitQuorumValue(c)
  PROVE  HasDecided(c)'
\* The two binds are SPLIT: prop's range depends on rr, and a dependent
\* multi-bind is rejected before the proof is even read.
<1>0. PICK rr \in Rounds :
        \E prop \in RProposalsFromProposerAt(c, rr) :
          /\ Valid(prop.value)
          /\ decision' = [decision EXCEPT ![c] = prop.value]
  BY DEF OnPrecommitQuorumValue
<1>1. PICK prop \in RProposalsFromProposerAt(c, rr) :
        /\ Valid(prop.value)
        /\ decision' = [decision EXCEPT ![c] = prop.value]
  BY <1>0
<1>2. prop.value \in Values
  BY <1>1, RProposalValueType DEF CInv
<1> QED
  BY <1>1, <1>2, NilNotInValues DEFS CInv, HasDecided, TypeOK

LEMMA DecideRegionEnabled ==
  ASSUME CInv, NEW c \in Honest, NEW r \in Rounds, DecideRegion(c, r)
  PROVE  ENABLED <<OnPrecommitQuorumValue(c)>>_vars
<1>1. PICK prop \in RProposalsFromProposerAt(c, r) :
        RExistsPrecommitQuorum(c, prop.value, r) /\ Valid(prop.value)
  BY DEFS DecideReady, DecideRegion
<1> QED
  BY <1>1, EnabledDecide DEFS CInv, DecideRegion, HasDecided

\* The stability leg. rcvd[c] only grows, so the decide guard is a latch too.
LEMMA DecideRegionStable ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW r \in Rounds,
         DecideRegion(c, r)
  PROVE  (DecideRegion(c, r) \/ HasDecided(c))'
<1>1. DecideReady(c, r)'
  BY RcvdMonotoneStep
  DEFS DecideReady, DecideRegion, RExistsPrecommitQuorum, RPrecommits,
       RPrecommitSendersFor, RProposals, RProposalsFromProposerAt
<1> QED
  BY <1>1 DEF DecideRegion

-----------------------------------------------------------------------------
\* The six legs, BOXED in clean top-level lemmas. The WF1 rule needs them as
\* [] facts, and boxing them inline under Spec fails, because the Init
\* conjunct pollutes the PTL abstraction.
LEMMA BoxDelivAct ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DelivRegion(c, r) /\ <<Deliver(c)>>_vars
                => DecideReady(c, r)'  )
BY DelivRegionDelivers, PTL DEF vars

LEMMA BoxDelivEnabled ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](CInv /\ DelivRegion(c, r) => ENABLED <<Deliver(c)>>_vars)
BY DelivRegionEnabled, PTL

LEMMA BoxDelivStab ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DelivRegion(c, r) /\ [CStep]_vars
                => ((CInv /\ DelivRegion(c, r))' \/ DecideReady(c, r)')  )
<1>1. CInv /\ DelivRegion(c, r) /\ [CStep]_vars
        => ((CInv /\ DelivRegion(c, r))' \/ DecideReady(c, r)')
  BY CInvStutters, DelivRegionStable DEFS CInv, CStep, DelivRegion, vars
<1> QED
  BY <1>1, PTL

LEMMA BoxDecideAct ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DecideRegion(c, r) /\ <<OnPrecommitQuorumValue(c)>>_vars
                => HasDecided(c)'  )
BY DecideRegionDecides, PTL DEF vars

LEMMA BoxDecideEnabled ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DecideRegion(c, r)
                => ENABLED <<OnPrecommitQuorumValue(c)>>_vars  )
BY DecideRegionEnabled, PTL

LEMMA BoxDecideStab ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DecideRegion(c, r) /\ [CStep]_vars
                => ((CInv /\ DecideRegion(c, r))' \/ HasDecided(c)')  )
<1>1. CInv /\ DecideRegion(c, r) /\ [CStep]_vars
        => ((CInv /\ DecideRegion(c, r))' \/ HasDecided(c)')
  BY CInvStutters, DecideRegionStable DEFS CInv, CStep, DecideRegion, vars
<1> QED
  BY <1>1, PTL

\* The two region entries, boxed: outside the region the goal already holds.
LEMMA BoxDelivEntry ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DecideEvidence(r)
                => ((CInv /\ DelivRegion(c, r)) \/ DecideReady(c, r))  )
<1>1. CInv /\ DecideEvidence(r)
        => ((CInv /\ DelivRegion(c, r)) \/ DecideReady(c, r))
  BY DEF DelivRegion
<1> QED
  BY <1>1, PTL

LEMMA BoxDecideEntry ==
  ASSUME NEW c \in Honest, NEW r \in Rounds
  PROVE  [](  CInv /\ DecideReady(c, r)
                => ((CInv /\ DecideRegion(c, r)) \/ HasDecided(c))  )
<1>1. CInv /\ DecideReady(c, r)
        => ((CInv /\ DecideRegion(c, r)) \/ HasDecided(c))
  BY DEF DecideRegion
<1> QED
  BY <1>1, PTL

LEMMA BoxDecidedIsSome ==
  ASSUME NEW c \in Honest
  PROVE  [](HasDecided(c) => SomeCorrectDecided)
<1>1. HasDecided(c) => SomeCorrectDecided
  BY DEF SomeCorrectDecided
<1> QED
  BY <1>1, PTL

-----------------------------------------------------------------------------
\* At least one correct process exists: a Byzantine quorum is available, and
\* every Byzantine quorum meets Honest.
LEMMA HonestNonEmpty == \E c : c \in Honest
<1>1. PICK Q \in ByzQuorum : Q \subseteq Honest
  BY QuorumAvailable
<1>2. PICK s \in Q : s \in Honest
  BY <1>1, ByzHasHonest
<1> QED
  BY <1>2

THEOREM QuorumDecides ==
  ASSUME NEW r \in Rounds, Spec
  PROVE  DecideEvidence(r) ~> SomeCorrectDecided
<1>c. PICK c : c \in Honest
  BY HonestNonEmpty
<1>g. []CInv
  BY InvProof, SentTimeLeNowInv, PTL DEFS CInv, Inv
<1>s. [][CStep]_vars
  BY <1>g, PTL DEFS CStep, Spec
\* WF1 on Deliver(c): the pending region leads to the delivered certificate.
<1>1. CInv /\ DelivRegion(c, r) ~> DecideReady(c, r)
  <2>1. [](  CInv /\ DelivRegion(c, r) /\ <<Deliver(c)>>_vars
               => DecideReady(c, r)'  )
    BY <1>c, BoxDelivAct
  <2>2. [](CInv /\ DelivRegion(c, r) => ENABLED <<Deliver(c)>>_vars)
    BY <1>c, BoxDelivEnabled
  <2>3. WF_vars(Deliver(c))
    BY <1>c DEFS Fairness, Spec
  <2>4. [](  CInv /\ DelivRegion(c, r) /\ [CStep]_vars
               => ((CInv /\ DelivRegion(c, r))' \/ DecideReady(c, r)')  )
    BY <1>c, BoxDelivStab
  <2> QED
    BY <1>s, <2>1, <2>2, <2>3, <2>4, PTL
\* WF1 on OnPrecommitQuorumValue(c): the decide guard leads to the decision.
<1>2. CInv /\ DecideRegion(c, r) ~> HasDecided(c)
  <2>1. [](  CInv /\ DecideRegion(c, r)
               /\ <<OnPrecommitQuorumValue(c)>>_vars => HasDecided(c)'  )
    BY <1>c, BoxDecideAct
  <2>2. [](  CInv /\ DecideRegion(c, r)
               => ENABLED <<OnPrecommitQuorumValue(c)>>_vars  )
    BY <1>c, BoxDecideEnabled
  <2>3. WF_vars(OnPrecommitQuorumValue(c))
    BY <1>c DEFS Fairness, Spec
  <2>4. [](  CInv /\ DecideRegion(c, r) /\ [CStep]_vars
               => ((CInv /\ DecideRegion(c, r))' \/ HasDecided(c)')  )
    BY <1>c, BoxDecideStab
  <2> QED
    BY <1>s, <2>1, <2>2, <2>3, <2>4, PTL
<1>3. [](  CInv /\ DecideEvidence(r)
             => ((CInv /\ DelivRegion(c, r)) \/ DecideReady(c, r))  )
  BY <1>c, BoxDelivEntry
<1>4. [](  CInv /\ DecideReady(c, r)
             => ((CInv /\ DecideRegion(c, r)) \/ HasDecided(c))  )
  BY <1>c, BoxDecideEntry
<1>5. [](HasDecided(c) => SomeCorrectDecided)
  BY <1>c, BoxDecidedIsSome
<1> QED
  BY <1>g, <1>1, <1>2, <1>3, <1>4, <1>5, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The entry window: a dated precommit quorum at round lr pins the clock.  *)
(*                                                                         *)
(*  The precommit twin of LockWindowCore in ...RoundProgress. Take an      *)
(*  any-value precommit quorum at round lr, dated at a T that is after     *)
(*  GST. Once the clock passes T + Delta, no correct validator can still   *)
(*  be below lr. None can sit at lr with the precommit timer unarmed       *)
(*  either. The delivered quorum leaves SkipRound or                       *)
(*  ScheduleTimeoutPrecommit enabled, and Tick is gated on the absence of  *)
(*  a computation step.                                                    *)
(*                                                                         *)
(* Stated at lr itself, not at rr with rr - 1 everywhere. The consumer     *)
(* instantiates lr := r - 1 from the certificate CrossingBacked dates      *)
(* behind the entry of p, and the arithmetic-free form keeps every leaf    *)
(* small.                                                                  *)
(*                                                                         *)
(* One joint induction over the three clauses. Clause 1 supplies clause 2, *)
(* and clause 2 supplies clause 3: each round entry and each timer arming  *)
(* starts in the state of the previous clause.                             *)
(***************************************************************************)

\* The shape the witness of CrossingBacked has.
AnyPrecommitDated(lr, T) ==
  \E Q \in ByzQuorum : \A s \in Q : \E vv \in ValuesOrNil :
    /\ Precommit(s, lr, vv) \in sent
    /\ sentTime[Precommit(s, lr, vv)] <= T

LEMMA PrecommitInMessage ==
  ASSUME NEW Q \in ByzQuorum, NEW s \in Q, NEW lr \in Rounds,
         NEW vv \in ValuesOrNil
  PROVE  Precommit(s, lr, vv) \in Message
BY DEFS ByzQuorum, Message, Precommit, PrecommitMsg

\* Transport backwards, the direction the induction runs on. The twin of
\* AnyPrevoteBack in ...RoundProgress.
LEMMA AnyPrecommitBack ==
  ASSUME TypeOK, [Next]_vars, NEW lr \in Rounds, NEW t, ~(now <= t),
         AnyPrecommitDated(lr, t)'
  PROVE  AnyPrecommitDated(lr, t)
BY PrecommitInMessage, SentByBack DEF AnyPrecommitDated

\* Every member of a dated any-value precommit quorum has reached c's view.
LEMMA PrecommitQuorumDeliveredSenders ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW lr \in Rounds,
         NEW T \in Int, T >= GST, AnyPrecommitDated(lr, T), now >= T + Delta
  PROVE  \E Q \in ByzQuorum : Q \subseteq RSendersOfTypeAtRound(c, "Precommit", lr)
BY DeliveredByDeadline, PrecommitInMessage
DEFS AnyPrecommitDated, Precommit, RSendersOfTypeAtRound

\* (1) c cannot lag BELOW lr: the delivered quorum is f+1 senders at lr, so
\* SkipRound(c, lr) is enabled (thirteenth CanCompute disjunct).
LEMMA SkipEnabledFromPrecommitQuorum ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW lr \in Rounds,
         NEW T \in Int, T >= GST, AnyPrecommitDated(lr, T), now >= T + Delta,
         step[c] # "decided", round[c] < lr
  PROVE  CanCompute(c)
BY ByzIsWeak, PrecommitQuorumDeliveredSenders
DEFS CanCompute, RSendersOfAnyMessageAt

\* (2) c cannot sit at lr with the precommit timer OFF: the delivered quorum
\* enables ScheduleTimeoutPrecommit(c) (tenth CanCompute disjunct).
LEMMA ArmPrecommitEnabledFromQuorum ==
  ASSUME TypeOK, GossipDeadline, NEW c \in Honest, NEW lr \in Rounds,
         NEW T \in Int, T >= GST, AnyPrecommitDated(lr, T), now >= T + Delta,
         round[c] = lr, step[c] # "decided", timer[c]["precommit"] = OFF
  PROVE  CanCompute(c)
BY PrecommitQuorumDeliveredSenders DEFS CanCompute, RExistsAnyPrecommitQuorum

\* ---- Frame lemmas for the round raise and the precommit timer -------------
\* Both round writers raise strictly, are guarded by step # "decided", freeze
\* the clock, and clear the precommit slot through ResetTimersFor.
LEMMA RoundRaiseFrame ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, round'[c] # round[c]
  PROVE  /\ round[c] < round'[c]
         /\ step[c] # "decided"
         /\ now' = now
         /\ timer'[c]["precommit"] = OFF
BY RoundEnteredStep
DEFS OnTimeoutPrecommit, ResetTimersFor, Rounds, SkipRound, TimerType, TypeOK

\* With the round fixed, the only writer of the precommit slot is the arming
\* action, and its value dates the arming instant.
LEMMA PrecommitTimerWriteFrame ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, round'[c] = round[c],
         timer'[c]["precommit"] # timer[c]["precommit"]
  PROVE  /\ now' = now
         /\ step[c] # "decided"
         /\ timer[c]["precommit"] = OFF
         /\ timer'[c]["precommit"] = now + TimeoutPrecommit(round[c])
BY TimerWriterStep
DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
     OnTimeoutPropose, ResetTimersFor, Rounds, ScheduleTimeoutPrecommit,
     ScheduleTimeoutPrevote, SkipRound, TimerType, TypeOK

\* ---- The armed precommit deadline is never more than one timeout out ------
\* The twin of PrevoteTimerLE, read at the POST-state in the branch where the
\* dated evidence only becomes datable at this very step. A round change cannot
\* break it, because ResetTimersFor clears the precommit slot on the way.
PrecommitTimerLE ==
  \A c \in Honest :
    timer[c]["precommit"] # OFF
      => timer[c]["precommit"] <= now + TimeoutPrecommit(round[c])

LEMMA PrecommitTimerLEStepL ==
  ASSUME TypeOK, [Next]_vars, PrecommitTimerLE
  PROVE  PrecommitTimerLE'
BY NowShape, RoundEnteredStep, T0PrecommitType, TDeltaType, TimerWriterStep
DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, PrecommitTimerLE, ResetTimersFor, Rounds,
  ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound,
  TimeoutPrecommit, TimerType, TypeOK

THEOREM PrecommitTimerLEInv == ASSUME Spec PROVE []PrecommitTimerLE
<1>1. PrecommitTimerLE
  BY DEFS Init, OFF, PrecommitTimerLE, Spec, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](PrecommitTimerLE => PrecommitTimerLE')
  BY <1>2, PrecommitTimerLEStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

THEOREM PrecommitTimerLEBothStates ==
  ASSUME Spec PROVE [](PrecommitTimerLE /\ PrecommitTimerLE')
BY PrecommitTimerLEInv, PTL

-----------------------------------------------------------------------------
EntryWindowCore ==
  \A c \in Honest, lr \in Rounds, T \in Nat :
    ( /\ T >= GST
      /\ AnyPrecommitDated(lr, T) )
    => /\ (step[c] # "decided" /\ round[c] < lr => now <= T + Delta)
       /\ (step[c] # "decided" /\ round[c] = lr
             /\ timer[c]["precommit"] = OFF => now <= T + Delta)
       /\ (step[c] # "decided" /\ round[c] = lr
             /\ timer[c]["precommit"] # OFF
             => timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr))

LEMMA EntryWindowCoreStepL ==
  ASSUME TypeOK, TypeOK', GossipDeadline, PrecommitTimerLE', [Next]_vars,
         EntryWindowCore
  PROVE  EntryWindowCore'
<1> SUFFICES ASSUME NEW c \in Honest, NEW lr \in Rounds, NEW T \in Nat,
                    T >= GST, AnyPrecommitDated(lr, T)'
             PROVE  /\ (step'[c] # "decided" /\ round'[c] < lr
                          => now' <= T + Delta)
                    /\ (step'[c] # "decided" /\ round'[c] = lr
                          /\ timer'[c]["precommit"] = OFF
                          => now' <= T + Delta)
                    /\ (step'[c] # "decided" /\ round'[c] = lr
                          /\ timer'[c]["precommit"] # OFF
                          => timer'[c]["precommit"]
                               <= T + Delta + TimeoutPrecommit(lr))
  BY DEF EntryWindowCore
<1>ty. /\ now \in Nat /\ now' \in Nat /\ T \in Nat /\ GST \in Nat
       /\ Delta \in Nat /\ Delta > 1
       /\ round[c] \in Nat /\ round'[c] \in Nat
       /\ timer[c]["precommit"] \in Int /\ timer'[c]["precommit"] \in Int
       /\ TimeoutPrecommit(lr) \in Nat
  BY DeltaType, GSTType, T0PrecommitType, TDeltaType
  DEFS Rounds, TimeoutPrecommit, TimerType, TypeOK
<1>n. now' = now \/ now' = now + 1
  BY NowShape
\* BRANCH A. The evidence only becomes datable at this step, so the date T is
\* at or above the clock and every bound is slack.
<1>A. CASE now <= T
  BY <1>A, <1>n, <1>ty DEF PrecommitTimerLE
<1>B. CASE ~(now <= T)
  <2>ev. AnyPrecommitDated(lr, T)
    BY <1>B, AnyPrecommitBack
  <2>1. step[c] # "decided" /\ round[c] < lr => now <= T + Delta
    BY <2>ev DEF EntryWindowCore
  <2>2. step[c] # "decided" /\ round[c] = lr
          /\ timer[c]["precommit"] = OFF => now <= T + Delta
    BY <2>ev DEF EntryWindowCore
  <2>3. step[c] # "decided" /\ round[c] = lr
          /\ timer[c]["precommit"] # OFF
          => timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr)
    BY <2>ev DEF EntryWindowCore
  \*  CLAUSE 1. Rounds only grow, and "decided" is absorbing, so the
  \*  hypothesis held before the step. A Tick at the deadline would find
  \*  SkipRound enabled.
  <2>c1. step'[c] # "decided" /\ round'[c] < lr => now' <= T + Delta
    BY <1>n, <1>ty, <2>1, <2>ev, DecidedStays, NowStaysUnlessTick,
       RoundGrowsStep, SkipEnabledFromPrecommitQuorum, TickNeedsQuiet
    DEFS Rounds, TypeOK
  \*  CLAUSE 2. Either c was already at lr with the slot unarmed, and a Tick
  \*  at the deadline would find ScheduleTimeoutPrecommit enabled. Or c
  \*  entered lr at this step, and the raise of the round freezes the clock
  \*  while clause 1 bounds it.
  <2>c2. step'[c] # "decided" /\ round'[c] = lr
           /\ timer'[c]["precommit"] = OFF => now' <= T + Delta
    BY <1>n, <1>ty, <2>1, <2>2, <2>ev, ArmPrecommitEnabledFromQuorum,
       DecidedStays, NowStaysUnlessTick, PrecommitTimerWriteFrame,
       RoundRaiseFrame, TickNeedsQuiet
    DEFS Rounds, TypeOK
  \* CLAUSE 3. The armed value dates the arming instant, which clause 2 bounds
  \* by T + Delta. A round raise clears the slot, so it cannot reach here.
  <2>c3. step'[c] # "decided" /\ round'[c] = lr
           /\ timer'[c]["precommit"] # OFF
           => timer'[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr)
    BY <1>ty, <2>2, <2>3, DecidedStays, PrecommitTimerWriteFrame,
       RoundRaiseFrame
    DEFS Rounds, TypeOK
  <2> QED
    BY <2>c1, <2>c2, <2>c3
<1> QED
  BY <1>A, <1>B

THEOREM EntryWindowCoreInv == ASSUME Spec PROVE []EntryWindowCore
\* Init has an empty pool, and no Byzantine quorum is empty, so the dated
\* any-value precommit quorum is already unsatisfiable.
<1>1. EntryWindowCore
  BY ByzNonEmpty DEFS AnyPrecommitDated, EntryWindowCore, Init, sent, Spec
<1>2. [](  TypeOK /\ TypeOK' /\ GossipDeadline /\ PrecommitTimerLE'
           /\ [Next]_vars  )
  BY GossipDeadlineInv, PrecommitTimerLEBothStates, TypeOKBothStates, PTL
     DEF Spec
<1>3. [](EntryWindowCore => EntryWindowCore')
  BY <1>2, EntryWindowCoreStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The entry deadline, and the propose-absence bridge.                     *)
(*                                                                         *)
(*   EntryWindowCore bounds an ARMED precommit timer at the certificate    *)
(*   round lr. To turn that into "every correct process has LEFT lr", the  *)
(*   clock must be tied to the timer. PrecommitDeadlineNotPassed does      *)
(*   that. An armed precommit timer is never in the past for an undecided  *)
(*   validator. OnTimeoutPrecommit would be a computation step, and Tick   *)
(*   is gated on the absence of one.                                       *)
(*                                                                         *)
(* ProposeEnabledFromAbsence is the fifth CanCompute bridge, beside the    *)
(* four of ...RoundProgress. It is the whole content of "an honest         *)
(* proposer that has not proposed pins the clock".                         *)
(***************************************************************************)

\*  An armed precommit timer is never in the past, unless its owner decided. A
\*  decided validator keeps its armed timers, and nothing fires them. The
\*  guard on the step is therefore necessary.
PrecommitDeadlineNotPassed ==
  \A c \in Honest :
    (step[c] # "decided" /\ timer[c]["precommit"] # OFF)
      => now <= timer[c]["precommit"]

\* The twelfth CanCompute disjunct, as its own bridge.
LEMMA TimeoutPrecommitEnabled ==
  ASSUME NEW c \in Honest, step[c] # "decided", timer[c]["precommit"] # OFF,
         now >= timer[c]["precommit"]
  PROVE  CanCompute(c)
BY DEF CanCompute

LEMMA PrecommitDeadlineNotPassedStepL ==
  ASSUME TypeOK, TypeOK', [Next]_vars, PrecommitDeadlineNotPassed
  PROVE  PrecommitDeadlineNotPassed'
<1> SUFFICES ASSUME NEW c \in Honest, step'[c] # "decided",
                    timer'[c]["precommit"] # OFF
             PROVE  now' <= timer'[c]["precommit"]
  BY DEF PrecommitDeadlineNotPassed
<1>ty. /\ now \in Nat /\ now' \in Nat /\ round[c] \in Nat
       /\ timer[c]["precommit"] \in Int /\ timer'[c]["precommit"] \in Int
       /\ TimeoutPrecommit(round[c]) \in Nat /\ TimeoutPrecommit(round[c]) > 0
  BY T0PrecommitType, TDeltaType
  DEFS Rounds, TimeoutPrecommit, TimerType, TypeOK
<1>nd. step[c] # "decided"
  BY DecidedStays
<1>a. CASE now' = now
  <2>1. CASE timer'[c]["precommit"] = timer[c]["precommit"]
    <3>1. now <= timer[c]["precommit"]
      BY <1>nd, <2>1 DEF PrecommitDeadlineNotPassed
    <3> QED
      BY <1>a, <1>ty, <2>1, <3>1, SMT
  <2>2. CASE timer'[c]["precommit"] # timer[c]["precommit"]
    <3>1. CASE round'[c] = round[c]
      <4>1. timer'[c]["precommit"] = now + TimeoutPrecommit(round[c])
        BY <2>2, <3>1, PrecommitTimerWriteFrame
      <4> QED
        BY <1>a, <1>ty, <4>1, SMT
    <3>2. CASE round'[c] # round[c]
      BY <3>2, RoundRaiseFrame
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1, <2>2
\* Only Tick moves the clock, and a fired precommit timer is a computation
\* step, so Tick cannot cross the deadline.
<1>b. CASE now' # now
  <2>tk. Tick
    BY <1>b, NowStaysUnlessTick
  <2>1. now' = now + 1 /\ timer' = timer
    BY <2>tk DEF Tick
  <2>2. now <= timer[c]["precommit"]
    BY <1>nd, <2>1 DEF PrecommitDeadlineNotPassed
  <2>3. now # timer[c]["precommit"]
    <3> SUFFICES ASSUME now = timer[c]["precommit"]
                 PROVE  FALSE
      OBVIOUS
    \* <2>1 carries timer' = timer, which is where the unarmed-slot guard of
    \* the bridge comes from: the ASSUME names the PRIMED slot.
    <3>1. CanCompute(c)
      BY <1>nd, <1>ty, <2>1, TimeoutPrecommitEnabled
    <3> QED
      BY <2>tk, <3>1, TickNeedsQuiet
  <2> QED
    BY <1>ty, <2>1, <2>2, <2>3, SMT
<1> QED
  BY <1>a, <1>b

THEOREM PrecommitDeadlineNotPassedInv ==
  ASSUME Spec PROVE []PrecommitDeadlineNotPassed
<1>1. PrecommitDeadlineNotPassed
  BY DEFS Init, OFF, PrecommitDeadlineNotPassed, Spec, TimerType
<1>2. [](TypeOK /\ TypeOK' /\ [Next]_vars)
  BY TypeOKBothStates, PTL DEF Spec
<1>3. [](PrecommitDeadlineNotPassed => PrecommitDeadlineNotPassed')
  BY <1>2, PrecommitDeadlineNotPassedStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Arithmetic in a MINIMAL context --------------------------------------
\* Inside EntryReachedFromWindow the hypotheses EntryWindowCore,
\* PrecommitDeadlineNotPassed and AnyPrecommitDated are in scope. Their SMT
\* encoding defeats the solver on inequalities it closes in milliseconds on its
\* own, so both contradictions are hoisted here. Each parameter is bound to a
\* term that the call site's hypotheses already type, so no closure fact such
\* as T + Delta \in Nat is needed at the call site.
LEMMA DeadlineBelowGap ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Nat, NEW k \in Nat,
         x <= y + d, x > y + d + k
  PROVE  FALSE
BY SMT

LEMMA DeadlineTimerGap ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Nat, NEW k \in Nat,
         NEW m \in Int, x <= m, m <= y + d + k, x > y + d + k
  PROVE  FALSE
BY SMT

\* The entry deadline. Once the clock passes the ceiling of EntryWindowCore,
\* every undecided correct validator is ABOVE the certificate round. A state
\* lemma: no induction of its own.
LEMMA EntryReachedFromWindow ==
  ASSUME TypeOK, EntryWindowCore, PrecommitDeadlineNotPassed,
         NEW c \in Honest, NEW lr \in Rounds, NEW T \in Nat,
         T >= GST, AnyPrecommitDated(lr, T),
         now > T + Delta + TimeoutPrecommit(lr),
         step[c] # "decided"
  PROVE  round[c] > lr
<1>ty. /\ now \in Nat /\ T \in Nat /\ GST \in Nat /\ Delta \in Nat
       /\ round[c] \in Nat /\ lr \in Nat
       /\ timer[c]["precommit"] \in Int
       /\ TimeoutPrecommit(lr) \in Nat
  BY DeltaType, GSTType, T0PrecommitType, TDeltaType
  DEFS Rounds, TimeoutPrecommit, TimerType, TypeOK
<1>w. /\ (round[c] < lr => now <= T + Delta)
      /\ (round[c] = lr /\ timer[c]["precommit"] = OFF => now <= T + Delta)
      /\ (round[c] = lr /\ timer[c]["precommit"] # OFF
            => timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr))
  BY DEF EntryWindowCore
\* Each case instantiates <1>w FIRST and does the arithmetic SECOND. One leaf
\* that does both leaves the backend to guess the instantiation.
<1>1. CASE round[c] < lr
  <2>1. now <= T + Delta
    BY <1>1, <1>w
  <2> QED
    BY <1>ty, <2>1, DeadlineBelowGap
<1>2. CASE round[c] = lr
  <2>1. CASE timer[c]["precommit"] = OFF
    <3>1. now <= T + Delta
      BY <1>2, <1>w, <2>1
    <3> QED
      BY <1>ty, <3>1, DeadlineBelowGap
  <2>2. CASE timer[c]["precommit"] # OFF
    <3>1. now <= timer[c]["precommit"]
      BY <2>2 DEF PrecommitDeadlineNotPassed
    <3>2. timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr)
      BY <1>2, <1>w, <2>2
    <3> QED
      BY <1>ty, <3>1, <3>2, DeadlineTimerGap
  <2> QED
    BY <2>1, <2>2
<1>3. CASE round[c] > lr
  BY <1>3
<1> QED
  BY <1>1, <1>2, <1>3, <1>ty

-----------------------------------------------------------------------------
\*  A record in the pool with the fields of a proposal IS an application of
\*  the constructor. The absence of every instance of the constructor is
\*  therefore the absence of any such record. This is the form the first
\*  CanCompute disjunct reads.
LEMMA NoProposalRebuild ==
  ASSUME TypeOK, NEW q \in Validators, NEW rr \in Rounds,
         \A v \in Values, vr \in Rounds \cup {-1} :
           Proposal(q, rr, v, vr) \notin sent
  PROVE  ~ \E msg \in sent : /\ msg.type = "Proposal"
                             /\ msg.round = rr
                             /\ msg.sender = q
<1> SUFFICES ASSUME NEW msg \in sent, msg.type = "Proposal",
                    msg.round = rr, msg.sender = q
             PROVE  FALSE
  OBVIOUS
<1>1. msg \in Message
  BY DEF sent
<1>2. /\ msg.value \in Values
      /\ msg.validRound \in Rounds \cup {-1}
      /\ msg = Proposal(msg.sender, msg.round, msg.value, msg.validRound)
  BY <1>1, ProposalRecordRebuild
<1> QED
  BY <1>2

\*  The fifth bridge to CanCompute. An honest proposer at its own round, in
\*  step "propose", with no proposal of its own in the pool, has a computation
\*  step.
LEMMA ProposeEnabledFromAbsence ==
  ASSUME TypeOK, NEW q \in Honest, NEW rr \in Rounds, Proposer[rr] = q,
         round[q] = rr, step[q] = "propose",
         \A v \in Values, vr \in Rounds \cup {-1} :
           Proposal(q, rr, v, vr) \notin sent
  PROVE  CanCompute(q)
<1>1. q \in Validators
  BY HonestSubValidators
<1>2. ~ \E msg \in sent : /\ msg.type = "Proposal"
                          /\ msg.round = rr
                          /\ msg.sender = q
  BY <1>1, NoProposalRebuild
<1> QED
  BY <1>2 DEF CanCompute

-----------------------------------------------------------------------------
(***************************************************************************)
(* Why no correct validator acts early at a good round.                    *)
(*                                                                         *)
(* The cascade's ceilings all rest on one chain of backing:                *)
(*                                                                         *)
(*   a correct validator ABOVE rr                                          *)
(*     needs a correct PRECOMMIT at rr        (CrossingBacked)             *)
(*       needs a correct PREVOTE at rr        (PrecommitBacked)            *)
(*         needs the round-rr PROPOSAL, or the propose timeout at rr.      *)
(*                                                                         *)
(*  Each arrow drops through a Byzantine quorum, and every Byzantine       *)
(*  quorum meets Honest, so the correct witness at each level is free. The *)
(*  last arrow is the only new induction. The first two are wrappers.      *)
(***************************************************************************)

\* Arithmetic in a minimal context, as for the entry deadline above.
LEMMA LeMinusNat ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW k \in Nat, a <= b - k
  PROVE  a <= b
BY SMT

\* Being above rr is backed by a correct precommit at rr, a full
\* TimeoutPrecommit(rr) before the current instant.
LEMMA AboveNeedsCorrectPrecommit ==
  ASSUME TypeOK, EnteredAtLeNow, EnteredCurrentRound, CrossingBacked,
         NEW c \in Honest, NEW rr \in Rounds, rr < round[c]
  PROVE  \E h \in Honest, w \in ValuesOrNil :
           /\ Precommit(h, rr, w) \in sent
           /\ sentTime[Precommit(h, rr, w)] <= now - TimeoutPrecommit(rr)
<1>1. \E Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, rr, v) \in sent
        /\ sentTime[Precommit(s, rr, v)] <= now - TimeoutPrecommit(rr)
  BY CrossingFromEarlierEntry
<1>2. PICK Q \in ByzQuorum : \A s \in Q : \E v \in ValuesOrNil :
        /\ Precommit(s, rr, v) \in sent
        /\ sentTime[Precommit(s, rr, v)] <= now - TimeoutPrecommit(rr)
  BY <1>1
<1>3. PICK h \in Q : h \in Honest
  BY <1>2, ByzHasHonest
<1> QED
  BY <1>2, <1>3

\* A correct precommit at rr is backed by a correct PREVOTE at rr, no later.
\* All three disjuncts of Backing are quorums of round-rr prevotes.
LEMMA PrecommitNeedsCorrectPrevote ==
  ASSUME TypeOK, PrecommitBacked, NEW x \in Honest, NEW rr \in Rounds,
         NEW v \in ValuesOrNil, NEW t \in Nat,
         Precommit(x, rr, v) \in sent,
         sentTime[Precommit(x, rr, v)] <= t
  PROVE  \E h \in Honest, w \in ValuesOrNil :
           /\ Prevote(h, rr, w) \in sent
           /\ sentTime[Prevote(h, rr, w)] <= t
<1>b. Backing(rr, v, t)
  BY DEF PrecommitBacked
<1>tp. TimeoutPrevote(rr) \in Nat
  BY T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
\* A dated polka for any value gives its honest member directly.
<1>pk. ASSUME NEW vv \in ValuesOrNil, PolkaDated(rr, vv, t)
       PROVE  \E h \in Honest, w \in ValuesOrNil :
                /\ Prevote(h, rr, w) \in sent
                /\ sentTime[Prevote(h, rr, w)] <= t
  <2>1. PICK Q \in ByzQuorum :
          \A s \in Q : Prevote(s, rr, vv) \in sent
                         /\ sentTime[Prevote(s, rr, vv)] <= t
    BY <1>pk DEF PolkaDated
  <2>2. PICK h \in Q : h \in Honest
    BY <2>1, ByzHasHonest
  <2> QED
    BY <2>1, <2>2
<1>1. CASE v \in Values /\ Valid(v) /\ PolkaDated(rr, v, t)
  BY <1>1, <1>pk DEF ValuesOrNil
<1>2. CASE v = nil /\ PolkaDated(rr, nil, t)
  BY <1>2, <1>pk DEF ValuesOrNil
<1>3. CASE v = nil /\ AnyPrevoteDated(rr, t - TimeoutPrevote(rr))
  <2>1. PICK Q \in ByzQuorum :
          \A s \in Q : \E vv \in ValuesOrNil :
            /\ Prevote(s, rr, vv) \in sent
            /\ sentTime[Prevote(s, rr, vv)] <= t - TimeoutPrevote(rr)
    BY <1>3 DEF AnyPrevoteDated
  <2>2. PICK h \in Q : h \in Honest
    BY <2>1, ByzHasHonest
  <2>3. PICK w \in ValuesOrNil :
          /\ Prevote(h, rr, w) \in sent
          /\ sentTime[Prevote(h, rr, w)] <= t - TimeoutPrevote(rr)
    BY <2>1, <2>2
  <2>ty. sentTime[Prevote(h, rr, w)] \in Int /\ t \in Int
    BY <2>2, <2>3, PrevoteInMessage DEFS OFF, sent, TypeOK
  <2>4. sentTime[Prevote(h, rr, w)] <= t
    BY <1>tp, <2>3, <2>ty, LeMinusNat
  <2> QED
    BY <2>2, <2>3, <2>4
<1> QED
  BY <1>1, <1>2, <1>3, <1>b DEF Backing

-----------------------------------------------------------------------------
\*  The propose timer's VALUE, which ProposeTimerArmedOp does not give. Both
\*  writers of the round arm it through ResetTimersFor, in the same step that
\*  records the entry. An armed propose timer therefore always reads the entry
\*  instant of the current round, plus the timeout of that round.
ProposeTimerValue ==
  \A c \in Honest :
    timer[c]["propose"] # OFF
      => timer[c]["propose"]
           = enteredAt[c][round[c]] + TimeoutPropose(round[c])

LEMMA ProposeTimerValueStepL ==
  ASSUME TypeOK, [Next]_vars, ProposeTimerValue
  PROVE  ProposeTimerValue'
BY RoundEnteredStep, TimerWriterStep
DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, ProposeTimerValue, ResetTimersFor, Rounds,
  ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, TimerType,
  TypeOK

THEOREM ProposeTimerValueInv == ASSUME Spec PROVE []ProposeTimerValue
\* At Init the propose timer is already armed at TimeoutPropose(0), and round
\* 0 was entered at instant 0, so the equality is 0 + x = x.
<1>1. ProposeTimerValue
  BY T0ProposeType, TDeltaType
  DEFS Init, OFF, ProposeTimerValue, Rounds, Spec, TimeoutPropose, TimerType
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](ProposeTimerValue => ProposeTimerValue')
  BY <1>2, ProposeTimerValueStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  The last arrow of the backing chain. A correct prevote at rr needs the
\*  round-rr proposal, or the propose timeout of rr. All three prevote
\*  emitters read step "propose". Two of them read a proposal out of rcvd. The
\*  third reads the propose timer that fired, and ProposeTimerValue pins the
\*  value of that timer to the entry instant of the round. The entry conjunct
\*  makes the invariant carry its own frozen-entry hypothesis, so the
\*  induction needs no outside fact.
PrevoteNeedsProposalOrTimeout ==
  \A c \in Honest, rr \in Rounds, w \in ValuesOrNil :
    Prevote(c, rr, w) \in sent =>
      /\ enteredAt[c][rr] # OFF
      /\ \/ \E mm \in sent : /\ mm.type = "Proposal"
                             /\ mm.round = rr
                             /\ mm.sender = Proposer[rr]
                             /\ sentTime[mm] <= sentTime[Prevote(c, rr, w)]
         \/ sentTime[Prevote(c, rr, w)]
              >= enteredAt[c][rr] + TimeoutPropose(rr)

LEMMA PrevoteNeedsProposalOrTimeoutStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, RoundEntryHistory,
         ProposeTimerValue, [Next]_vars, PrevoteNeedsProposalOrTimeout
  PROVE  PrevoteNeedsProposalOrTimeout'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW c \in Honest, NEW rr \in Rounds, NEW w \in ValuesOrNil,
                    Prevote(c, rr, w) \in sent'
             PROVE  /\ enteredAt'[c][rr] # OFF
                    /\ \/ \E mm \in sent' :
                            /\ mm.type = "Proposal"
                            /\ mm.round = rr
                            /\ mm.sender = Proposer[rr]
                            /\ sentTime'[mm] <= sentTime'[Prevote(c, rr, w)]
                       \/ sentTime'[Prevote(c, rr, w)]
                            >= enteredAt'[c][rr] + TimeoutPropose(rr)
  BY DEF PrevoteNeedsProposalOrTimeout
<1>m. Prevote(c, rr, w) \in Message
  BY DEF sent
\* The prevote was already there: every reading is frozen.
<1>1. CASE Prevote(c, rr, w) \in sent
  <2>i. /\ enteredAt[c][rr] # OFF
        /\ \/ \E mm \in sent : /\ mm.type = "Proposal"
                               /\ mm.round = rr
                               /\ mm.sender = Proposer[rr]
                               /\ sentTime[mm] <= sentTime[Prevote(c, rr, w)]
           \/ sentTime[Prevote(c, rr, w)]
                >= enteredAt[c][rr] + TimeoutPropose(rr)
    BY <1>1 DEF PrevoteNeedsProposalOrTimeout
  <2>e. enteredAt'[c][rr] = enteredAt[c][rr]
    BY <2>i, EnteredAtFrozenStep
  <2>s. sentTime'[Prevote(c, rr, w)] = sentTime[Prevote(c, rr, w)]
    BY <1>1, <1>fz, <1>m DEF sent
  <2>d. CASE \E mm \in sent : /\ mm.type = "Proposal"
                              /\ mm.round = rr
                              /\ mm.sender = Proposer[rr]
                              /\ sentTime[mm] <= sentTime[Prevote(c, rr, w)]
    <3>1. PICK mm \in sent : /\ mm.type = "Proposal"
                             /\ mm.round = rr
                             /\ mm.sender = Proposer[rr]
                             /\ sentTime[mm] <= sentTime[Prevote(c, rr, w)]
      BY <2>d
    <3>2. mm \in sent' /\ sentTime'[mm] = sentTime[mm]
      BY <1>fz, <1>sub, <3>1 DEF sent
    <3> QED
      BY <2>e, <2>i, <2>s, <3>1, <3>2
  <2>t. CASE sentTime[Prevote(c, rr, w)]
               >= enteredAt[c][rr] + TimeoutPropose(rr)
    BY <2>e, <2>i, <2>s, <2>t
  <2> QED
    BY <2>d, <2>i, <2>t
\* The prevote is fresh: FreshPrevoteAction names the emitting action.
<1>2. CASE Prevote(c, rr, w) \notin sent
  <2>f. /\ rr = round[c]
        /\ sentTime'[Prevote(c, rr, w)] = now
        /\ \/ OnTimeoutPropose(c)
           \/ OnProposalNoPOL(c)
           \/ OnProposalWithPOL(c)
    BY <1>2, <1>m, FreshPrevoteAction DEF Prevote
  <2>ea. enteredAt' = enteredAt
    BY <2>f DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose
  <2>off. enteredAt[c][rr] # OFF
    BY <2>f DEF RoundEntryHistory
  <2>1. CASE OnTimeoutPropose(c)
    <3>1. timer[c]["propose"] # OFF /\ now >= timer[c]["propose"]
      BY <2>1 DEF OnTimeoutPropose
    <3>2. timer[c]["propose"]
            = enteredAt[c][round[c]] + TimeoutPropose(round[c])
      BY <3>1 DEF ProposeTimerValue
    <3> QED
      BY <2>ea, <2>f, <2>off, <3>1, <3>2
  <2>2. CASE OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
    <3>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) : TRUE
      BY <2>2 DEFS OnProposalNoPOL, OnProposalWithPOL
    <3>2. /\ prop \in rcvd[c]
          /\ prop.type = "Proposal"
          /\ prop.round = rr
          /\ prop.sender = Proposer[rr]
      BY <2>f, <3>1 DEFS RProposals, RProposalsFromProposerAt
    <3>3. prop \in sent
      BY <3>2 DEF RcvdSubsetSent
    <3>4. prop \in Message /\ sentTime[prop] # OFF
      BY <3>3 DEF sent
    <3>5. sentTime[prop] <= now
      BY <3>4 DEF SentTimeLeNow
    <3>6. prop \in sent' /\ sentTime'[prop] = sentTime[prop]
      BY <1>fz, <1>sub, <3>3, <3>4
    <3> QED
      BY <2>ea, <2>f, <2>off, <3>2, <3>5, <3>6
  <2> QED
    BY <2>1, <2>2, <2>f
<1> QED
  BY <1>1, <1>2

THEOREM PrevoteNeedsProposalOrTimeoutInv ==
  ASSUME Spec PROVE []PrevoteNeedsProposalOrTimeout
<1>1. PrevoteNeedsProposalOrTimeout
  BY DEFS Init, OFF, PrevoteNeedsProposalOrTimeout, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
             /\ RoundEntryHistory /\ ProposeTimerValue /\ [Next]_vars  )
  BY InvProof, ProposeTimerValueInv, PTL, RoundEntryHistoryInv, SentInvInv,
     SentTimeLeNowInv DEF Spec, Inv
<1>3. [](PrevoteNeedsProposalOrTimeout => PrevoteNeedsProposalOrTimeout')
  BY <1>2, PrevoteNeedsProposalOrTimeoutStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL


-----------------------------------------------------------------------------
\* Support for the propose ceiling: the step-to-prevote record, and the entry
\* deadline read AT the ceiling.

\* The value that a proposal-driven prevote exit reads is a Values element,
\* because the proposal it reads is a Message record.
LEMMA RProposalValueTyped ==
  ASSUME TypeOK, RcvdSubsetSent, NEW c \in Honest, NEW rr \in Rounds,
         NEW prop \in RProposalsFromProposerAt(c, rr)
  PROVE  prop.value \in Values
<1>1. prop \in sent /\ prop.type = "Proposal"
  BY DEFS RcvdSubsetSent, RProposals, RProposalsFromProposerAt
<1> QED
  BY <1>1, ProposalRecordRebuild DEF sent

\* Each step-"propose" exit broadcasts a TYPED prevote of the actor, at the
\* actor's own round. The type is nil in the timeout exit, and comes off the
\* proposal record in the two proposal-driven exits.
LEMMA PrevoteExitBroadcast ==
  ASSUME TypeOK, RcvdSubsetSent, NEW c \in Honest,
         OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
  PROVE  \E w \in ValuesOrNil :
           sentTime' = [sentTime EXCEPT ![Prevote(c, round[c], w)] = now]
<1>1. CASE OnTimeoutPropose(c)
  BY <1>1 DEFS Broadcast, OnTimeoutPropose, ValuesOrNil
<1>2. CASE OnProposalNoPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          LET v == prop.value
              voteValueID ==
                IF Valid(v) /\ (locked[c].round = -1 \/ locked[c].value = v)
                THEN v
                ELSE nil
          IN Broadcast(c, Prevote(c, round[c], voteValueID))
    BY <1>2 DEF OnProposalNoPOL
  <2>2. prop.value \in Values
    BY <2>1, RProposalValueTyped DEF TypeOK
  <2> QED
    BY <2>1, <2>2 DEFS Broadcast, ValuesOrNil
<1>3. CASE OnProposalWithPOL(c)
  <2>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
          LET v  == prop.value
              vr == prop.validRound
              voteValueID ==
                IF Valid(v) /\ (locked[c].round <= vr \/ locked[c].value = v)
                THEN v
                ELSE nil
          IN Broadcast(c, Prevote(c, round[c], voteValueID))
    BY <1>3 DEF OnProposalWithPOL
  <2>2. prop.value \in Values
    BY <2>1, RProposalValueTyped DEF TypeOK
  <2> QED
    BY <2>1, <2>2 DEFS Broadcast, ValuesOrNil
<1> QED
  BY <1>1, <1>2, <1>3

\*  A correct validator that is past step "propose" at its current round has
\*  already prevoted at that round. The three exits broadcast the prevote in
\*  the same step that moves the step. Both round writers reset the step to
\*  "propose", so a round change makes the clause vacuous again. Step
\*  "decided" is left out, because OnPrecommitQuorumValue reaches it from any
\*  step.
StepPastProposeHasPrevote ==
  \A c \in Honest :
    step[c] \in {"prevote", "precommit"}
      => \E w \in ValuesOrNil : Prevote(c, round[c], w) \in sent

LEMMA StepPastProposeHasPrevoteStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, StepPastProposeHasPrevote
  PROVE  StepPastProposeHasPrevote'
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW c \in Honest, step'[c] \in {"prevote", "precommit"}
             PROVE  \E w \in ValuesOrNil : Prevote(c, round'[c], w) \in sent'
  BY DEF StepPastProposeHasPrevote
\* The round is kept and c was already past "propose": carry the witness over.
<1>keep. ASSUME round'[c] = round[c], step[c] \in {"prevote", "precommit"}
         PROVE  \E w \in ValuesOrNil : Prevote(c, round'[c], w) \in sent'
  BY <1>keep, <1>sub DEF StepPastProposeHasPrevote
\* Group 1: no honest step and no honest round moves.
<1>1. CASE \/ (\E p \in Honest : Propose(p) \/ Deliver(p)
                 \/ ScheduleTimeoutPrecommit(p) \/ ScheduleTimeoutPrevote(p)
                 \/ OnPrevoteQuorumValueLateUpdate(p))
           \/ (\E p \in Faulty : FaultyStep(p))
           \/ Tick
           \/ vars' = vars
  <2>1. step' = step /\ round' = round
    BY <1>1
    DEFS Deliver, FaultyStep, OnPrevoteQuorumValueLateUpdate, Propose,
      ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, Tick, vars
  <2> QED
    BY <1>keep, <2>1
\* Group 2: a step-"propose" exit. Its own broadcast is the witness.
<1>2. CASE \E p \in Honest : OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                               \/ OnProposalWithPOL(p)
  <2> PICK p \in Honest : OnTimeoutPropose(p) \/ OnProposalNoPOL(p)
                            \/ OnProposalWithPOL(p)
    BY <1>2
  <2>r. round' = round
    BY DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose
  <2>1. CASE p # c
    <3>1. step'[c] = step[c]
      BY <2>1
      DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, TypeOK
    <3> QED
      BY <1>keep, <2>r, <3>1
  <2>2. CASE p = c
    <3>1. PICK w \in ValuesOrNil :
            sentTime' = [sentTime EXCEPT ![Prevote(c, round[c], w)] = now]
      BY <2>2, PrevoteExitBroadcast
    <3>2. Prevote(c, round[c], w) \in Message
      BY <3>1, HonestSubValidators, MsgPrevote DEF TypeOK
    <3>3. sentTime'[Prevote(c, round[c], w)] = now
      BY <3>1, <3>2 DEF TypeOK
    <3> QED
      BY <2>r, <3>1, <3>2, <3>3, NowNotOff DEF sent
  <2> QED
    BY <2>1, <2>2
\* Group 3: a step-"prevote" exit. The round is kept and c was at "prevote".
<1>3. CASE \E p \in Honest : OnPrevoteQuorumValueFirstTime(p)
                               \/ OnPrevoteQuorumNil(p) \/ OnTimeoutPrevote(p)
  <2> PICK p \in Honest : OnPrevoteQuorumValueFirstTime(p)
                            \/ OnPrevoteQuorumNil(p) \/ OnTimeoutPrevote(p)
    BY <1>3
  <2>r. round' = round
    BY DEFS OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote
  <2>1. CASE p # c
    <3>1. step'[c] = step[c]
      BY <2>1
      DEFS OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote,
        TypeOK
    <3> QED
      BY <1>keep, <2>r, <3>1
  <2>2. CASE p = c
    <3>1. step[c] = "prevote"
      BY <2>2
      DEFS OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnTimeoutPrevote
    <3> QED
      BY <1>keep, <2>r, <3>1
  <2> QED
    BY <2>1, <2>2
\* Group 4: the decision and the two round writers. Each makes the clause
\* vacuous at the actor, and leaves every other validator alone.
<1>4. CASE \E p \in Honest : OnPrecommitQuorumValue(p) \/ OnTimeoutPrecommit(p)
                               \/ (\E rr \in Rounds : SkipRound(p, rr))
  <2> PICK p \in Honest : OnPrecommitQuorumValue(p) \/ OnTimeoutPrecommit(p)
                            \/ (\E rr \in Rounds : SkipRound(p, rr))
    BY <1>4
  <2>1. CASE p # c
    <3>1. step'[c] = step[c] /\ round'[c] = round[c]
      BY <2>1
      DEFS OnPrecommitQuorumValue, OnTimeoutPrecommit, SkipRound, TypeOK
    <3> QED
      BY <1>keep, <3>1
  <2>2. CASE p = c
    <3>1. step'[c] \in {"decided", "propose"}
      BY <2>2
      DEFS OnPrecommitQuorumValue, OnTimeoutPrecommit, SkipRound, TypeOK
    <3> QED
      BY <3>1
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3, <1>4
  DEFS HonestNext, HonestStep, Next, vars

THEOREM StepPastProposeHasPrevoteInv ==
  ASSUME Spec PROVE []StepPastProposeHasPrevote
<1>1. StepPastProposeHasPrevote
  BY DEFS Init, StepPastProposeHasPrevote, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](StepPastProposeHasPrevote => StepPastProposeHasPrevote')
  BY <1>2, StepPastProposeHasPrevoteStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* Arithmetic in a minimal context, as for EntryReachedFromWindow above. The
\* clock sits ON the ceiling here, not above it, so the two shapes differ.
LEMMA DeadlineBelowGapAt ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Nat, NEW k \in Nat,
         k > 0, x <= y + d, x >= y + d + k
  PROVE  FALSE
BY SMT

LEMMA TimerAtOrBelowClock ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW d \in Nat, NEW k \in Nat,
         NEW m \in Int, m <= y + d + k, x >= y + d + k
  PROVE  x >= m
BY SMT

\*  The entry deadline, read AT the ceiling instead of above it. Maximal
\*  progress replaces PrecommitDeadlineNotPassed here. An armed precommit
\*  timer at or below the clock IS a computation step. A state that offers no
\*  computation step to c can therefore not hold one.
LEMMA EntryReachedAtCeiling ==
  ASSUME TypeOK, EntryWindowCore,
         NEW c \in Honest, NEW lr \in Rounds, NEW T \in Nat,
         T >= GST, AnyPrecommitDated(lr, T),
         now >= T + Delta + TimeoutPrecommit(lr),
         step[c] # "decided", ~ CanCompute(c)
  PROVE  round[c] > lr
<1>ty. /\ now \in Nat /\ T \in Nat /\ GST \in Nat /\ Delta \in Nat
       /\ round[c] \in Nat /\ lr \in Nat
       /\ timer[c]["precommit"] \in Int
       /\ TimeoutPrecommit(lr) \in Nat /\ TimeoutPrecommit(lr) > 0
  BY DeltaType, GSTType, T0PrecommitType, TDeltaType
  DEFS Rounds, TimeoutPrecommit, TimerType, TypeOK
<1>w. /\ (round[c] < lr => now <= T + Delta)
      /\ (round[c] = lr /\ timer[c]["precommit"] = OFF => now <= T + Delta)
      /\ (round[c] = lr /\ timer[c]["precommit"] # OFF
            => timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr))
  BY DEF EntryWindowCore
<1>1. CASE round[c] < lr
  <2>1. now <= T + Delta
    BY <1>1, <1>w
  <2> QED
    BY <1>ty, <2>1, DeadlineBelowGapAt
<1>2. CASE round[c] = lr
  <2>1. CASE timer[c]["precommit"] = OFF
    <3>1. now <= T + Delta
      BY <1>2, <1>w, <2>1
    <3> QED
      BY <1>ty, <3>1, DeadlineBelowGapAt
  <2>2. CASE timer[c]["precommit"] # OFF
    <3>1. timer[c]["precommit"] <= T + Delta + TimeoutPrecommit(lr)
      BY <1>2, <1>w, <2>2
    <3>2. now >= timer[c]["precommit"]
      BY <1>ty, <3>1, TimerAtOrBelowClock
    <3> QED
      BY <2>2, <3>2 DEF CanCompute
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>ty

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)