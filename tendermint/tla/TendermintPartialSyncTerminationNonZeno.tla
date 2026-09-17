------------------ MODULE TendermintPartialSyncTerminationNonZeno ------------------
(***************************************************************************)
(* Non-Zeno computation core.                                              *)
(*                                                                         *)
(* TendermintPartialSync assumes weak fairness for each honest computation    *)
(* action separately. This module derives the aggregate progress property  *)
(* that the clock proof needs. At a fixed clock value, if any honest       *)
(* computation is enabled, the well-founded measure ComputeWork eventually *)
(* decreases. No aggregate assumption WF_vars(HonestStep(p)) is added.     *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationBase, TLAPS

(***************************************************************************)
(* Named copies of the thirteen CanCompute guards.                         *)
(***************************************************************************)

GPropose(p) ==
  /\ step[p] = "propose"
  /\ Proposer[round[p]] = p
  /\ ~ \E msg \in sent :
       msg.type = "Proposal" /\ msg.round = round[p] /\ msg.sender = p

GTimeoutPropose(p) ==
  /\ step[p] = "propose"
  /\ timer[p]["propose"] # OFF /\ now >= timer[p]["propose"]

GProposalNoPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) : prop.validRound = -1

GProposalWithPOL(p) ==
  /\ step[p] = "propose"
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
       /\ RExistsPrevoteQuorum(p, prop.value, prop.validRound)
       /\ prop.validRound \in B!Range(0, round[p])

GSchedulePrevote(p) ==
  /\ step[p] = "prevote"
  /\ timer[p]["prevote"] = OFF
  /\ RExistsAnyPrevoteQuorum(p, round[p])

GPrevoteValueFirst(p) ==
  /\ step[p] = "prevote"
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
       /\ RExistsPrevoteQuorum(p, prop.value, round[p])
       /\ Valid(prop.value)

GPrevoteValueLate(p) ==
  /\ step[p] \in {"precommit", "decided"}
  /\ valid[p].round < round[p]
  /\ \E prop \in RProposalsFromProposerAt(p, round[p]) :
       /\ RExistsPrevoteQuorum(p, prop.value, round[p])
       /\ Valid(prop.value)

GPrevoteNil(p) ==
  /\ step[p] = "prevote"
  /\ RExistsPrevoteQuorum(p, nil, round[p])

GTimeoutPrevote(p) ==
  /\ step[p] = "prevote"
  /\ timer[p]["prevote"] # OFF /\ now >= timer[p]["prevote"]

GSchedulePrecommit(p) ==
  /\ step[p] # "decided"
  /\ timer[p]["precommit"] = OFF
  /\ RExistsAnyPrecommitQuorum(p, round[p])

GPrecommitValue(p) ==
  /\ decision[p] = nil
  /\ \E r \in Rounds : \E prop \in RProposalsFromProposerAt(p, r) :
       /\ RExistsPrecommitQuorum(p, prop.value, r)
       /\ Valid(prop.value)

GTimeoutPrecommit(p) ==
  /\ step[p] # "decided"
  /\ timer[p]["precommit"] # OFF /\ now >= timer[p]["precommit"]

GSkip(p, r) ==
  /\ step[p] # "decided"
  /\ \E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, r)
  /\ r > round[p]

ComputationGuard(p) ==
  \/ GPropose(p)
  \/ GTimeoutPropose(p)
  \/ GProposalNoPOL(p)
  \/ GProposalWithPOL(p)
  \/ GSchedulePrevote(p)
  \/ GPrevoteValueFirst(p)
  \/ GPrevoteValueLate(p)
  \/ GPrevoteNil(p)
  \/ GTimeoutPrevote(p)
  \/ GSchedulePrecommit(p)
  \/ GPrecommitValue(p)
  \/ GTimeoutPrecommit(p)
  \/ \E r \in Rounds : GSkip(p, r)

ComputeGroupA(p) ==
  GPropose(p) \/ GTimeoutPropose(p)
    \/ GProposalNoPOL(p) \/ GProposalWithPOL(p)

ComputeGroupB(p) ==
  GSchedulePrevote(p) \/ GPrevoteValueFirst(p)
    \/ GPrevoteValueLate(p) \/ GPrevoteNil(p)

ComputeGroupC(p) ==
  GTimeoutPrevote(p) \/ GSchedulePrecommit(p)
    \/ GPrecommitValue(p) \/ GTimeoutPrecommit(p)

GroupedComputationGuard(p) ==
  ComputeGroupA(p) \/ ComputeGroupB(p) \/ ComputeGroupC(p)
    \/ \E r \in Rounds : GSkip(p, r)

LEMMA ComputationGuardGrouped ==
  ASSUME NEW p
  PROVE ComputationGuard(p) <=> GroupedComputationGuard(p)
BY DEF ComputationGuard, GroupedComputationGuard,
       ComputeGroupA, ComputeGroupB, ComputeGroupC

LEMMA GroupedComputationGuardSplit ==
  ASSUME NEW p
  PROVE GroupedComputationGuard(p)
        <=> (ComputeGroupA(p) \/ ComputeGroupB(p) \/ ComputeGroupC(p)
              \/ \E r \in Rounds : GSkip(p, r))
BY DEF GroupedComputationGuard

LEMMA ComputationGuardIsCanCompute ==
  ASSUME NEW p
  PROVE ComputationGuard(p) <=> CanCompute(p)
BY RangeCo DEF ComputationGuard, CanCompute, GPropose, GTimeoutPropose,
       GProposalNoPOL, GProposalWithPOL, GSchedulePrevote,
       GPrevoteValueFirst, GPrevoteValueLate, GPrevoteNil,
       GTimeoutPrevote, GSchedulePrecommit, GPrecommitValue,
       GTimeoutPrecommit, GSkip

LEMMA NZRProposalValueType ==
  ASSUME TypeOK, RcvdSubsetSent,
         NEW p \in Honest, NEW r \in Rounds,
         NEW prop \in RProposalsFromProposerAt(p, r)
  PROVE prop.value \in Values
BY DEFS Message, PrecommitMsg, PrevoteMsg, ProposalMsg, RcvdSubsetSent,
        RProposals, RProposalsFromProposerAt, sent

NZDecideAt(p, r, prop) ==
  /\ decision[p] = nil
  /\ prop \in RProposalsFromProposerAt(p, r)
  /\ RExistsPrecommitQuorum(p, prop.value, r)
  /\ Valid(prop.value)
  /\ decision' = [decision EXCEPT ![p] = prop.value]
  /\ step' = [step EXCEPT ![p] = "decided"]
  /\ decidedRound' = [decidedRound EXCEPT ![p] = r]
  /\ UNCHANGED <<round, locked, valid, sentTime, rcvd, timer, now, enteredAt>>

NZProposeAt(p, v) ==
  /\ step[p] = "propose"
  /\ Proposer[round[p]] = p
  /\ ~ \E msg \in sent :
       msg.type = "Proposal" /\ msg.round = round[p] /\ msg.sender = p
  /\ v \in IF valid[p].value # nil THEN {valid[p].value} ELSE getValue
  /\ Broadcast(p, Proposal(p, round[p], v, valid[p].round))
  /\ UNCHANGED <<round, step, locked, valid, decision, timer, now, enteredAt, decidedRound>>

NZPrevoteValueFirstAt(p, prop) ==
  /\ step[p] = "prevote"
  /\ prop \in RProposalsFromProposerAt(p, round[p])
  /\ RExistsPrevoteQuorum(p, prop.value, round[p])
  /\ Valid(prop.value)
  /\ LET newRecord == [value |-> prop.value, round |-> round[p]]
     IN /\ locked' = [locked EXCEPT ![p] = newRecord]
        /\ Broadcast(p, Precommit(p, round[p], prop.value))
        /\ step' = [step EXCEPT ![p] = "precommit"]
        /\ valid' = [valid EXCEPT ![p] = newRecord]
  /\ UNCHANGED <<round, decision, timer, now, enteredAt, decidedRound>>

NZPrevoteValueLateAt(p, prop) ==
  /\ step[p] \in {"precommit", "decided"}
  /\ valid[p].round < round[p]
  /\ prop \in RProposalsFromProposerAt(p, round[p])
  /\ RExistsPrevoteQuorum(p, prop.value, round[p])
  /\ Valid(prop.value)
  /\ valid' = [valid EXCEPT ![p] =
                 [value |-> prop.value, round |-> round[p]]]
  /\ UNCHANGED <<round, step, locked, decision, sentTime, rcvd, timer, now,
                 enteredAt, decidedRound>>

(***************************************************************************)
(* Each guard enables its existing fair action.                            *)
(***************************************************************************)

LEMMA EnabledPropose ==
  ASSUME TypeOK, NEW p \in Honest, GPropose(p)
  PROVE ENABLED <<Propose(p)>>_vars
<1> PICK v \in Values : Valid(v)
  BY ValidNonEmpty
<1> DEFINE pv == IF valid[p].value # nil THEN valid[p].value ELSE v
<1>1. pv \in IF valid[p].value # nil THEN {valid[p].value} ELSE getValue
  BY DEF pv, getValue
<1>2. pv \in Values
  BY <1>1, NilNotInValues DEF pv, TypeOK, LockState, ValuesOrNil
<1>3. Proposal(p, round[p], pv, valid[p].round) \in Message
  BY <1>2 DEF Proposal, Message, ProposalMsg, TypeOK, Rounds, Honest, LockState
<1>4. sentTime[Proposal(p, round[p], pv, valid[p].round)] = OFF
  BY <1>3 DEFS GPropose, Proposal, sent
<1>5. [sentTime EXCEPT ![Proposal(p, round[p], pv, valid[p].round)] = now] # sentTime
  BY <1>3, <1>4 DEF TypeOK, OFF
<1>6. ENABLED <<NZProposeAt(p, pv)>>_vars
  BY <1>1, <1>5, ExpandENABLED DEFS NZProposeAt, Broadcast, vars, GPropose
<1>7. <<NZProposeAt(p, pv)>>_vars => <<Propose(p)>>_vars
  BY DEF NZProposeAt, Propose, vars
<1> QED
  BY <1>6, <1>7, AutoUSE, ExpandENABLED DEFS NZProposeAt, Propose, vars

LEMMA EnabledTimeoutPropose ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPropose(p)
  PROVE ENABLED <<OnTimeoutPropose(p)>>_vars
<1>1. [step EXCEPT ![p] = "prevote"] # step
  BY DEF GTimeoutPropose, TypeOK, Step
<1> QED
  BY <1>1, ExpandENABLED DEF OnTimeoutPropose, Broadcast, vars, GTimeoutPropose

LEMMA EnabledProposalNoPOL ==
  ASSUME TypeOK, NEW p \in Honest, GProposalNoPOL(p)
  PROVE ENABLED <<OnProposalNoPOL(p)>>_vars
<1>1. [step EXCEPT ![p] = "prevote"] # step
  BY DEF GProposalNoPOL, TypeOK, Step
<1> QED
  BY <1>1, AutoUSE, ExpandENABLED DEF OnProposalNoPOL, Broadcast, vars, GProposalNoPOL

LEMMA EnabledProposalWithPOL ==
  ASSUME TypeOK, NEW p \in Honest, GProposalWithPOL(p)
  PROVE ENABLED <<OnProposalWithPOL(p)>>_vars
<1>1. [step EXCEPT ![p] = "prevote"] # step
  BY DEF GProposalWithPOL, TypeOK, Step
<1> QED
  BY <1>1, RangeCo, AutoUSE, ExpandENABLED DEF OnProposalWithPOL, Broadcast, vars, GProposalWithPOL

LEMMA EnabledSchedulePrevote ==
  ASSUME TypeOK, NEW p \in Honest, GSchedulePrevote(p)
  PROVE ENABLED <<ScheduleTimeoutPrevote(p)>>_vars
BY T0PrevoteType, TDeltaType, ExpandENABLED
DEFS TypeOK, Rounds, TimeoutPrevote, OFF, GSchedulePrevote, TimerType, ScheduleTimeoutPrevote, vars

LEMMA EnabledPrevoteValueFirst ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteValueFirst(p)
  PROVE ENABLED <<OnPrevoteQuorumValueFirstTime(p)>>_vars
<1>pr. PICK prop \in RProposalsFromProposerAt(p, round[p]) :
       RExistsPrevoteQuorum(p, prop.value, round[p]) /\ Valid(prop.value)
  BY DEF GPrevoteValueFirst
<1>1. [step EXCEPT ![p] = "precommit"] # step
  BY DEF GPrevoteValueFirst, TypeOK, Step
<1>2. ENABLED <<OnPrevoteQuorumValueFirstTimeAt(p, prop)>>_vars
  BY <1>pr, <1>1, ExpandENABLED
  DEFS OnPrevoteQuorumValueFirstTimeAt, Broadcast, vars, GPrevoteValueFirst
<1>3. <<OnPrevoteQuorumValueFirstTimeAt(p, prop)>>_vars
       => <<OnPrevoteQuorumValueFirstTime(p)>>_vars
  BY DEF OnPrevoteQuorumValueFirstTimeAt, OnPrevoteQuorumValueFirstTime, vars
<1>ba. <<OnPrevoteQuorumValueFirstTimeAt(p, prop)>>_vars \in BOOLEAN
  BY DEF OnPrevoteQuorumValueFirstTimeAt, Broadcast, vars
<1>bb. <<OnPrevoteQuorumValueFirstTime(p)>>_vars \in BOOLEAN
  BY DEF OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueFirstTimeAt, Broadcast, vars
<1>4. ENABLED <<OnPrevoteQuorumValueFirstTimeAt(p, prop)>>_vars
       => ENABLED <<OnPrevoteQuorumValueFirstTime(p)>>_vars
  BY <1>ba, <1>bb, <1>3, ENABLEDaxioms
<1> QED
  BY <1>2, <1>4

LEMMA EnabledPrevoteValueLate ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteValueLate(p)
  PROVE ENABLED <<OnPrevoteQuorumValueLateUpdate(p)>>_vars
<1> PICK prop \in RProposalsFromProposerAt(p, round[p]) :
       /\ RExistsPrevoteQuorum(p, prop.value, round[p])
       /\ Valid(prop.value)
  BY DEF GPrevoteValueLate
<1>1. [valid EXCEPT ![p] = [value |-> prop.value, round |-> round[p]]] # valid
  BY DEFS GPrevoteValueLate, LockState, TypeOK
<1>2. ENABLED <<NZPrevoteValueLateAt(p, prop)>>_vars
  BY <1>1, ExpandENABLED DEFS NZPrevoteValueLateAt, vars, GPrevoteValueLate
<1>3. <<NZPrevoteValueLateAt(p, prop)>>_vars => <<OnPrevoteQuorumValueLateUpdate(p)>>_vars
  BY DEF NZPrevoteValueLateAt, OnPrevoteQuorumValueLateUpdate, vars
<1> QED
  BY <1>2, <1>3, AutoUSE, ExpandENABLED DEFS NZPrevoteValueLateAt, OnPrevoteQuorumValueLateUpdate, vars

LEMMA EnabledPrevoteNil ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteNil(p)
  PROVE ENABLED <<OnPrevoteQuorumNil(p)>>_vars
<1>1. [step EXCEPT ![p] = "precommit"] # step
  BY DEF GPrevoteNil, TypeOK, Step
<1> QED
  BY <1>1, ExpandENABLED DEF OnPrevoteQuorumNil, Broadcast, vars, GPrevoteNil

LEMMA EnabledTimeoutPrevote ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPrevote(p)
  PROVE ENABLED <<OnTimeoutPrevote(p)>>_vars
<1>1. [step EXCEPT ![p] = "precommit"] # step
  BY DEF GTimeoutPrevote, TypeOK, Step
<1> QED
  BY <1>1, ExpandENABLED DEF OnTimeoutPrevote, Broadcast, vars, GTimeoutPrevote

LEMMA EnabledSchedulePrecommit ==
  ASSUME TypeOK, NEW p \in Honest, GSchedulePrecommit(p)
  PROVE ENABLED <<ScheduleTimeoutPrecommit(p)>>_vars
<1>1. now + TimeoutPrecommit(round[p]) # OFF
  BY T0PrecommitType, TDeltaType DEF TypeOK, Rounds, TimeoutPrecommit, OFF
<1>2. [timer EXCEPT ![p]["precommit"] = now + TimeoutPrecommit(round[p])] # timer
  BY <1>1 DEF GSchedulePrecommit, TypeOK, TimerType
<1> QED
  BY <1>2, ExpandENABLED DEF ScheduleTimeoutPrecommit, vars, GSchedulePrecommit

LEMMA EnabledPrecommitValue ==
  ASSUME TypeOK, RcvdSubsetSent, NEW p \in Honest, GPrecommitValue(p)
  PROVE ENABLED <<OnPrecommitQuorumValue(p)>>_vars
<1>r. PICK r \in Rounds : \E prop \in RProposalsFromProposerAt(p, r) :
       RExistsPrecommitQuorum(p, prop.value, r) /\ Valid(prop.value)
  BY DEF GPrecommitValue
<1>pr. PICK prop \in RProposalsFromProposerAt(p, r) :
       RExistsPrecommitQuorum(p, prop.value, r) /\ Valid(prop.value)
  BY <1>r
<1>1. prop.value \in Values
  BY <1>pr, NZRProposalValueType
<1>2. prop.value # nil
  BY <1>1, NilNotInValues
<1>3. [decision EXCEPT ![p] = prop.value] # decision
  BY <1>2 DEF GPrecommitValue, TypeOK
<1>4. ENABLED <<NZDecideAt(p, r, prop)>>_vars
  BY <1>pr, <1>3, ExpandENABLED
  DEFS NZDecideAt, vars, GPrecommitValue
<1>5. <<NZDecideAt(p, r, prop)>>_vars => <<OnPrecommitQuorumValue(p)>>_vars
  BY DEF NZDecideAt, OnPrecommitQuorumValue, vars
<1> QED
  BY ONLY <1>4, <1>5, AutoUSE, ExpandENABLED
  DEFS NZDecideAt, OnPrecommitQuorumValue, vars, GPrecommitValue

LEMMA EnabledTimeoutPrecommit ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPrecommit(p)
  PROVE ENABLED <<OnTimeoutPrecommit(p)>>_vars
<1>1. [round EXCEPT ![p] = round[p] + 1] # round
  BY DEF TypeOK, Rounds
<1> QED
  BY <1>1, ExpandENABLED DEF OnTimeoutPrecommit, vars, GTimeoutPrecommit, ResetTimersFor

LEMMA EnabledSkip ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, GSkip(p, r)
  PROVE ENABLED <<SkipRound(p, r)>>_vars
<1>1. [round EXCEPT ![p] = r] # round
  BY DEF GSkip, TypeOK, Rounds
<1> QED
  BY <1>1, ExpandENABLED DEF SkipRound, vars, GSkip, ResetTimersFor

(***************************************************************************)
(* Network steps preserve every selected computation guard.                *)
(***************************************************************************)

NetworkStep ==
  \/ \E p \in Honest : Deliver(p)
  \/ \E p \in Faulty : FaultyStep(p)

LEMMA NetworkFrame ==
  ASSUME TypeOK, NetworkStep, NEW p \in Honest
  PROVE /\ round' = round /\ step' = step /\ locked' = locked
        /\ valid' = valid /\ decision' = decision /\ timer' = timer
        /\ now' = now /\ enteredAt' = enteredAt /\ decidedRound' = decidedRound
        /\ rcvd[p] \subseteq rcvd'[p]
<1>1. [Next]_vars
  BY DEF NetworkStep, Next, HonestNext, Deliver, FaultyStep, vars
<1>2. rcvd[p] \subseteq rcvd'[p]
  BY <1>1, RcvdMonotoneStep
<1> QED
  BY <1>2 DEF NetworkStep, Deliver, FaultyStep

LEMMA RProposalSetMono ==
  ASSUME NEW p, NEW r, rcvd[p] \subseteq rcvd'[p], round' = round
  PROVE RProposalsFromProposerAt(p, r) \subseteq RProposalsFromProposerAt(p, r)'
BY DEF RProposalsFromProposerAt, RProposals

LEMMA RPrevoteQuorumMono ==
  ASSUME NEW p, NEW v, NEW r, rcvd[p] \subseteq rcvd'[p]
  PROVE RExistsPrevoteQuorum(p, v, r) => RExistsPrevoteQuorum(p, v, r)'
BY DEFS RExistsPrevoteQuorum, RPrevoteSendersFor, RPrevotes

LEMMA RPrecommitQuorumMono ==
  ASSUME NEW p, NEW v, NEW r, rcvd[p] \subseteq rcvd'[p]
  PROVE RExistsPrecommitQuorum(p, v, r) => RExistsPrecommitQuorum(p, v, r)'
BY DEFS RExistsPrecommitQuorum, RPrecommitSendersFor, RPrecommits

LEMMA RAnyPrevoteQuorumMono ==
  ASSUME NEW p, NEW r, rcvd[p] \subseteq rcvd'[p]
  PROVE RExistsAnyPrevoteQuorum(p, r) => RExistsAnyPrevoteQuorum(p, r)'
BY DEFS RExistsAnyPrevoteQuorum, RSendersOfTypeAtRound

LEMMA RAnyMessageSendersMono ==
  ASSUME NEW p, NEW r, rcvd[p] \subseteq rcvd'[p]
  PROVE RSendersOfAnyMessageAt(p, r) \subseteq RSendersOfAnyMessageAt(p, r)'
BY DEFS RSendersOfAnyMessageAt, RSendersOfTypeAtRound

LEMMA GProposeNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GPropose(p), NetworkStep
  PROVE GPropose(p)'
<1>fr. round' = round /\ step' = step
  BY NetworkFrame
<1>1. CASE \E q \in Honest : Deliver(q)
  BY <1>1, <1>fr DEF GPropose, Deliver, NetworkStep, sent
<1>2. CASE \E q \in Faulty : FaultyStep(q)
  <2> PICK q \in Faulty : FaultyStep(q)
    BY <1>2
  <2>1. q \notin Honest
    BY DEF Honest
  <2> QED
    BY <2>1, <1>fr DEF GPropose, FaultyStep, NetworkStep, sent, TypeOK
<1> QED BY <1>1, <1>2 DEF NetworkStep

LEMMA GTimeoutProposeNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPropose(p), NetworkStep
  PROVE GTimeoutPropose(p)'
BY NetworkFrame DEF GTimeoutPropose

LEMMA GProposalNoPOLNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GProposalNoPOL(p), NetworkStep
  PROVE GProposalNoPOL(p)'
BY NetworkFrame, RProposalSetMono DEF GProposalNoPOL

LEMMA GProposalWithPOLNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GProposalWithPOL(p), NetworkStep
  PROVE GProposalWithPOL(p)'
BY NetworkFrame, RProposalSetMono, RPrevoteQuorumMono DEF GProposalWithPOL

LEMMA GSchedulePrevoteNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GSchedulePrevote(p), NetworkStep
  PROVE GSchedulePrevote(p)'
BY NetworkFrame, RAnyPrevoteQuorumMono DEF GSchedulePrevote

LEMMA GPrevoteValueFirstNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteValueFirst(p), NetworkStep
  PROVE GPrevoteValueFirst(p)'
BY NetworkFrame, RProposalSetMono, RPrevoteQuorumMono DEF GPrevoteValueFirst

LEMMA GPrevoteValueLateNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteValueLate(p), NetworkStep
  PROVE GPrevoteValueLate(p)'
BY NetworkFrame, RProposalSetMono, RPrevoteQuorumMono DEF GPrevoteValueLate

LEMMA GPrevoteNilNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GPrevoteNil(p), NetworkStep
  PROVE GPrevoteNil(p)'
BY NetworkFrame, RPrevoteQuorumMono DEF GPrevoteNil

LEMMA GTimeoutPrevoteNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPrevote(p), NetworkStep
  PROVE GTimeoutPrevote(p)'
BY NetworkFrame DEF GTimeoutPrevote

LEMMA GSchedulePrecommitNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GSchedulePrecommit(p), NetworkStep
  PROVE GSchedulePrecommit(p)'
BY NetworkFrame DEFS GSchedulePrecommit, RExistsAnyPrecommitQuorum, RSendersOfTypeAtRound

LEMMA GPrecommitValueNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GPrecommitValue(p), NetworkStep
  PROVE GPrecommitValue(p)'
BY NetworkFrame, RProposalSetMono, RPrecommitQuorumMono DEF GPrecommitValue

LEMMA GTimeoutPrecommitNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, GTimeoutPrecommit(p), NetworkStep
  PROVE GTimeoutPrecommit(p)'
BY NetworkFrame DEF GTimeoutPrecommit

LEMMA GSkipNetworkStable ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, GSkip(p, r), NetworkStep
  PROVE GSkip(p, r)'
BY NetworkFrame, RAnyMessageSendersMono DEF GSkip

(***************************************************************************)
(* Per-action WF1 rule over the shared ComputeWork ranking.                *)
(***************************************************************************)

NZCore ==
  /\ TypeOK
  /\ RcvdSubsetSent
  /\ SentInv
  /\ RoundBelowNow
  /\ DecidedStepOp
  /\ BurstFactsOp

NZNext == Next /\ NZCore /\ NZCore'

LEMMA GroupedAntecedentSplit ==
  ASSUME NEW n, NEW p
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GroupedComputationGuard(p))
        <=> \/ (NZCore /\ ComputeWork = n + 1
                 /\ (ComputeGroupA(p) \/ ComputeGroupB(p)))
            \/ (NZCore /\ ComputeWork = n + 1 /\ ComputeGroupC(p))
            \/ (\E r \in Rounds :
                  NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
BY DEF GroupedComputationGuard

LEMMA ComputeActionDropsWork ==
  ASSUME NZCore, NZCore', NEW p \in Honest, HonestStep(p)
  PROVE ComputeWork' < ComputeWork
BY ComputeWorkDecreasesStep DEF NZCore, RoundBelowNow, DecidedStepOp

LEMMA NetworkStepKeepsWork ==
  ASSUME NZCore, NetworkStep
  PROVE ComputeWork' = ComputeWork
<1>1. CASE \E p \in Honest : Deliver(p)
  BY <1>1, ComputeWorkUnchangedDeliverStep DEF NetworkStep, NZCore
<1>2. CASE \E p \in Faulty : FaultyStep(p)
  BY <1>2, ComputeWorkUnchangedFaultyStep DEF NetworkStep, NZCore
<1> QED BY <1>1, <1>2 DEF NetworkStep

LEMMA ComputeWorkNatPrime ==
  ASSUME BurstFactsOp'
  PROVE ComputeWork' \in Nat
BY BurstBoundNat DEFS BurstFactsOp, ComputeWork, BurstScalar

LEMMA WorkStepClass ==
  ASSUME NEW n \in Nat, NZCore, ComputeWork = n + 1,
         \E p \in Honest : CanCompute(p), [NZNext]_vars
  PROVE \/ (ComputeWork <= n)'
        \/ (NetworkStep /\ ComputeWork' = ComputeWork)
        \/ UNCHANGED vars
<1>1. CASE UNCHANGED vars
  BY <1>1
<1>2. CASE NZNext
  <2>core. NZCore'
    BY <1>2 DEF NZNext
  <2>1. CASE \E p \in Honest : HonestStep(p)
    <3> PICK p \in Honest : HonestStep(p)
      BY <2>1
    <3>1. ComputeWork' < ComputeWork
      BY <2>core, ComputeActionDropsWork DEF NZNext
    <3>2. ComputeWork' \in Nat
      BY <2>core, ComputeWorkNatPrime DEF NZCore
    <3> QED BY <3>1, <3>2, SMT
  <2>2. CASE NetworkStep
    BY <2>2, NetworkStepKeepsWork
  <2>3. CASE Tick
    BY <2>3 DEF Tick
  <2> QED
    BY <2>1, <2>2, <2>3
       DEF NZNext, Next, HonestNext, NetworkStep
<1> QED BY <1>1, <1>2 DEF NZNext

LEMMA NZCoreStutter ==
  ASSUME NZCore, UNCHANGED vars
  PROVE NZCore'
<1>1. TypeOK'
  BY DEF NZCore, TypeOK, vars
<1>2. RcvdSubsetSent'
  BY DEF NZCore, RcvdSubsetSent, sent, vars
<1>3. SentInv'
  BY DEF NZCore, SentInv, HonestSentOK, sent, vars
<1>4. RoundBelowNow'
  BY DEF NZCore, RoundBelowNow, vars
<1>5. DecidedStepOp'
  BY DEF NZCore, DecidedStepOp, vars
<1>6. BurstFactsOp'
  BY DEF NZCore, BurstFactsOp, RoundGap, RoundCeiling, StepWork, StepBudget,
         BurstBottom, ProposeOwed, OffLiveTimers, ValidStale, BurstBound,
         sent, vars
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF NZCore

LEMMA ComputeWorkStutter ==
  ASSUME UNCHANGED vars
  PROVE ComputeWork' = ComputeWork
BY DEFS ComputeWork, BurstScalar, BurstBound, RoundGap, RoundCeiling,
        StepWork, StepBudget, BurstBottom, ProposeOwed, OffLiveTimers,
        ValidStale, sent, vars

LEMMA NZCoreBracketPreserves ==
  ASSUME NZCore, [NZNext]_vars
  PROVE NZCore'
<1>1. CASE UNCHANGED vars
  BY <1>1, NZCoreStutter
<1>2. CASE NZNext
  BY <1>2 DEF NZNext
<1> QED BY <1>1, <1>2 DEF NZNext


LEMMA HonestStepDropsBelow ==
  ASSUME NEW n \in Nat, NZCore, NZCore', ComputeWork = n + 1,
         NEW p \in Honest, HonestStep(p)
  PROVE (ComputeWork <= n)'
<1>1. ComputeWork' < ComputeWork
  BY ComputeActionDropsWork
<1>2. ComputeWork' \in Nat
  BY ComputeWorkNatPrime DEF NZCore
<1> QED BY <1>1, <1>2, SMT

LEMMA BoxProposeStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GPropose(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GPropose(p))'
               \/ (ComputeWork <= n)')
<1>1. GPropose(p) => \E q \in Honest : CanCompute(q)
  BY DEF GPropose, CanCompute
<1>2. NZCore /\ GPropose(p) /\ NetworkStep => GPropose(p)'
  BY GProposeNetworkStable DEF NZCore
<1>3. GPropose(p) /\ UNCHANGED vars => GPropose(p)'
  BY DEF GPropose, sent, vars
<1>4. ASSUME NZCore, ComputeWork = n + 1, GPropose(p), [NZNext]_vars
      PROVE \/ (NZCore /\ ComputeWork = n + 1 /\ GPropose(p))'
            \/ (ComputeWork <= n)'
  BY <1>1, <1>2, <1>3, <1>4, ComputeWorkStutter, NZCoreBracketPreserves, NZCoreStutter, WorkStepClass
<1> QED BY <1>4, PTL

THEOREM ProposeComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(Propose(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GPropose(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GPropose(p)
          /\ <<NZNext /\ Propose(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPropose(p)
         /\ <<NZNext /\ Propose(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GPropose(p)
          => ENABLED <<Propose(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPropose(p)
         => ENABLED <<Propose(p)>>_vars
    BY EnabledPropose DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GPropose(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GPropose(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxProposeStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxTimeoutProposeStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p))'
               \/ (ComputeWork <= n)')
<1>1. GTimeoutPropose(p) => \E q \in Honest : CanCompute(q)
  BY DEF GTimeoutPropose, CanCompute
<1>2. NZCore /\ GTimeoutPropose(p) /\ NetworkStep => GTimeoutPropose(p)'
  BY GTimeoutProposeNetworkStable DEF NZCore
<1>3. GTimeoutPropose(p) /\ UNCHANGED vars => GTimeoutPropose(p)'
  BY DEFS GTimeoutPropose, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GTimeoutPropose(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
        \/ (NetworkStep /\ ComputeWork' = ComputeWork)
        \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GTimeoutPropose(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GTimeoutPropose(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM TimeoutProposeComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnTimeoutPropose(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)
          /\ <<NZNext /\ OnTimeoutPropose(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)
            /\ <<NZNext /\ OnTimeoutPropose(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)
          => ENABLED <<OnTimeoutPropose(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)
            => ENABLED <<OnTimeoutPropose(p)>>_vars
    BY EnabledTimeoutPropose DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxTimeoutProposeStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxProposalNoPOLStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p))'
               \/ (ComputeWork <= n)')
<1>1. GProposalNoPOL(p) => \E q \in Honest : CanCompute(q)
  BY DEF GProposalNoPOL, CanCompute
<1>2. NZCore /\ GProposalNoPOL(p) /\ NetworkStep => GProposalNoPOL(p)'
  BY GProposalNoPOLNetworkStable DEF NZCore
<1>3. GProposalNoPOL(p) /\ UNCHANGED vars => GProposalNoPOL(p)'
  BY DEFS GProposalNoPOL, RProposalsFromProposerAt, RProposals, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GProposalNoPOL(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GProposalNoPOL(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GProposalNoPOL(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM ProposalNoPOLComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnProposalNoPOL(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)
          /\ <<NZNext /\ OnProposalNoPOL(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)
            /\ <<NZNext /\ OnProposalNoPOL(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)
          => ENABLED <<OnProposalNoPOL(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)
            => ENABLED <<OnProposalNoPOL(p)>>_vars
    BY EnabledProposalNoPOL DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxProposalNoPOLStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxProposalWithPOLStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p))'
               \/ (ComputeWork <= n)')
<1>1. GProposalWithPOL(p) => \E q \in Honest : CanCompute(q)
  BY RangeCo DEF GProposalWithPOL, CanCompute
<1>2. NZCore /\ GProposalWithPOL(p) /\ NetworkStep => GProposalWithPOL(p)'
  BY GProposalWithPOLNetworkStable DEF NZCore
<1>3. GProposalWithPOL(p) /\ UNCHANGED vars => GProposalWithPOL(p)'
  BY DEFS GProposalWithPOL, RProposalsFromProposerAt, RProposals,
        RExistsPrevoteQuorum, RPrevoteSendersFor, RPrevotes, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GProposalWithPOL(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GProposalWithPOL(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GProposalWithPOL(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM ProposalWithPOLComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnProposalWithPOL(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)
          /\ <<NZNext /\ OnProposalWithPOL(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)
            /\ <<NZNext /\ OnProposalWithPOL(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)
          => ENABLED <<OnProposalWithPOL(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)
            => ENABLED <<OnProposalWithPOL(p)>>_vars
    BY EnabledProposalWithPOL DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxProposalWithPOLStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxSchedulePrevoteStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p))'
               \/ (ComputeWork <= n)')
<1>1. GSchedulePrevote(p) => \E q \in Honest : CanCompute(q)
  BY DEF GSchedulePrevote, CanCompute
<1>2. NZCore /\ GSchedulePrevote(p) /\ NetworkStep => GSchedulePrevote(p)'
  BY GSchedulePrevoteNetworkStable DEF NZCore
<1>3. GSchedulePrevote(p) /\ UNCHANGED vars => GSchedulePrevote(p)'
  BY DEFS GSchedulePrevote, RExistsAnyPrevoteQuorum,
        RSendersOfTypeAtRound, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GSchedulePrevote(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GSchedulePrevote(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GSchedulePrevote(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM SchedulePrevoteComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(ScheduleTimeoutPrevote(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)
          /\ <<NZNext /\ ScheduleTimeoutPrevote(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)
            /\ <<NZNext /\ ScheduleTimeoutPrevote(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)
          => ENABLED <<ScheduleTimeoutPrevote(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)
            => ENABLED <<ScheduleTimeoutPrevote(p)>>_vars
    BY EnabledSchedulePrevote DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxSchedulePrevoteStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxPrevoteValueFirstStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p))'
               \/ (ComputeWork <= n)')
<1>1. GPrevoteValueFirst(p) => \E q \in Honest : CanCompute(q)
  BY DEF GPrevoteValueFirst, CanCompute
<1>2. NZCore /\ GPrevoteValueFirst(p) /\ NetworkStep => GPrevoteValueFirst(p)'
  BY GPrevoteValueFirstNetworkStable DEF NZCore
<1>3. GPrevoteValueFirst(p) /\ UNCHANGED vars => GPrevoteValueFirst(p)'
  BY DEFS GPrevoteValueFirst, RProposalsFromProposerAt, RProposals,
        RExistsPrevoteQuorum, RPrevoteSendersFor, RPrevotes, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GPrevoteValueFirst(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GPrevoteValueFirst(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GPrevoteValueFirst(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM PrevoteValueFirstComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnPrevoteQuorumValueFirstTime(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)
          /\ <<NZNext /\ OnPrevoteQuorumValueFirstTime(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)
            /\ <<NZNext /\ OnPrevoteQuorumValueFirstTime(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)
          => ENABLED <<OnPrevoteQuorumValueFirstTime(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)
            => ENABLED <<OnPrevoteQuorumValueFirstTime(p)>>_vars
    BY EnabledPrevoteValueFirst DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxPrevoteValueFirstStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxPrevoteValueLateStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p))'
               \/ (ComputeWork <= n)')
<1>1. GPrevoteValueLate(p) => \E q \in Honest : CanCompute(q)
  BY DEF GPrevoteValueLate, CanCompute
<1>2. NZCore /\ GPrevoteValueLate(p) /\ NetworkStep => GPrevoteValueLate(p)'
  BY GPrevoteValueLateNetworkStable DEF NZCore
<1>3. GPrevoteValueLate(p) /\ UNCHANGED vars => GPrevoteValueLate(p)'
  BY DEFS GPrevoteValueLate, RProposalsFromProposerAt, RProposals,
        RExistsPrevoteQuorum, RPrevoteSendersFor, RPrevotes, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GPrevoteValueLate(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GPrevoteValueLate(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GPrevoteValueLate(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM PrevoteValueLateComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnPrevoteQuorumValueLateUpdate(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)
          /\ <<NZNext /\ OnPrevoteQuorumValueLateUpdate(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)
            /\ <<NZNext /\ OnPrevoteQuorumValueLateUpdate(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)
          => ENABLED <<OnPrevoteQuorumValueLateUpdate(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)
            => ENABLED <<OnPrevoteQuorumValueLateUpdate(p)>>_vars
    BY EnabledPrevoteValueLate DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxPrevoteValueLateStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxPrevoteNilStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p))'
               \/ (ComputeWork <= n)')
<1>1. GPrevoteNil(p) => \E q \in Honest : CanCompute(q)
  BY DEF GPrevoteNil, CanCompute
<1>2. NZCore /\ GPrevoteNil(p) /\ NetworkStep => GPrevoteNil(p)'
  BY GPrevoteNilNetworkStable DEF NZCore
<1>3. GPrevoteNil(p) /\ UNCHANGED vars => GPrevoteNil(p)'
  BY DEFS GPrevoteNil, RExistsPrevoteQuorum, RPrevoteSendersFor,
        RPrevotes, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GPrevoteNil(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GPrevoteNil(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GPrevoteNil(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM PrevoteNilComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnPrevoteQuorumNil(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)
          /\ <<NZNext /\ OnPrevoteQuorumNil(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)
            /\ <<NZNext /\ OnPrevoteQuorumNil(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)
          => ENABLED <<OnPrevoteQuorumNil(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)
            => ENABLED <<OnPrevoteQuorumNil(p)>>_vars
    BY EnabledPrevoteNil DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxPrevoteNilStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxTimeoutPrevoteStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p))'
               \/ (ComputeWork <= n)')
<1>1. GTimeoutPrevote(p) => \E q \in Honest : CanCompute(q)
  BY DEF GTimeoutPrevote, CanCompute
<1>2. NZCore /\ GTimeoutPrevote(p) /\ NetworkStep => GTimeoutPrevote(p)'
  BY GTimeoutPrevoteNetworkStable DEF NZCore
<1>3. GTimeoutPrevote(p) /\ UNCHANGED vars => GTimeoutPrevote(p)'
  BY DEFS GTimeoutPrevote, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GTimeoutPrevote(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GTimeoutPrevote(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GTimeoutPrevote(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM TimeoutPrevoteComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnTimeoutPrevote(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)
          /\ <<NZNext /\ OnTimeoutPrevote(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)
            /\ <<NZNext /\ OnTimeoutPrevote(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)
          => ENABLED <<OnTimeoutPrevote(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)
            => ENABLED <<OnTimeoutPrevote(p)>>_vars
    BY EnabledTimeoutPrevote DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxTimeoutPrevoteStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxSchedulePrecommitStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p))'
               \/ (ComputeWork <= n)')
<1>1. GSchedulePrecommit(p) => \E q \in Honest : CanCompute(q)
  BY DEF GSchedulePrecommit, CanCompute
<1>2. NZCore /\ GSchedulePrecommit(p) /\ NetworkStep => GSchedulePrecommit(p)'
  BY GSchedulePrecommitNetworkStable DEF NZCore
<1>3. GSchedulePrecommit(p) /\ UNCHANGED vars => GSchedulePrecommit(p)'
  BY DEFS GSchedulePrecommit, RExistsAnyPrecommitQuorum,
        RSendersOfTypeAtRound, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GSchedulePrecommit(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GSchedulePrecommit(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GSchedulePrecommit(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM SchedulePrecommitComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(ScheduleTimeoutPrecommit(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)
          /\ <<NZNext /\ ScheduleTimeoutPrecommit(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)
            /\ <<NZNext /\ ScheduleTimeoutPrecommit(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)
          => ENABLED <<ScheduleTimeoutPrecommit(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)
            => ENABLED <<ScheduleTimeoutPrecommit(p)>>_vars
    BY EnabledSchedulePrecommit DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxSchedulePrecommitStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxPrecommitValueStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p))'
               \/ (ComputeWork <= n)')
<1>1. GPrecommitValue(p) => \E q \in Honest : CanCompute(q)
  BY DEF GPrecommitValue, CanCompute
<1>2. NZCore /\ GPrecommitValue(p) /\ NetworkStep => GPrecommitValue(p)'
  BY GPrecommitValueNetworkStable DEF NZCore
<1>3. GPrecommitValue(p) /\ UNCHANGED vars => GPrecommitValue(p)'
  BY DEFS GPrecommitValue, RProposalsFromProposerAt, RProposals,
        RExistsPrecommitQuorum, RPrecommitSendersFor, RPrecommits, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GPrecommitValue(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GPrecommitValue(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GPrecommitValue(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM PrecommitValueComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnPrecommitQuorumValue(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)
          /\ <<NZNext /\ OnPrecommitQuorumValue(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)
            /\ <<NZNext /\ OnPrecommitQuorumValue(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)
          => ENABLED <<OnPrecommitQuorumValue(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)
            => ENABLED <<OnPrecommitQuorumValue(p)>>_vars
    BY EnabledPrecommitValue DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxPrecommitValueStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxTimeoutPrecommitStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p))'
               \/ (ComputeWork <= n)')
<1>1. GTimeoutPrecommit(p) => \E q \in Honest : CanCompute(q)
  BY DEF GTimeoutPrecommit, CanCompute
<1>2. NZCore /\ GTimeoutPrecommit(p) /\ NetworkStep => GTimeoutPrecommit(p)'
  BY GTimeoutPrecommitNetworkStable DEF NZCore
<1>3. GTimeoutPrecommit(p) /\ UNCHANGED vars => GTimeoutPrecommit(p)'
  BY DEFS GTimeoutPrecommit, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GTimeoutPrecommit(p), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GTimeoutPrecommit(p)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GTimeoutPrecommit(p)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM TimeoutPrecommitComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         WF_vars(OnTimeoutPrecommit(p)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)
          /\ <<NZNext /\ OnTimeoutPrecommit(p)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)
            /\ <<NZNext /\ OnTimeoutPrecommit(p)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)
          => ENABLED <<OnTimeoutPrecommit(p)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)
            => ENABLED <<OnTimeoutPrecommit(p)>>_vars
    BY EnabledTimeoutPrecommit DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxTimeoutPrecommitStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL

LEMMA BoxSkipStabilityLeg ==
  ASSUME NEW n \in Nat, NEW p \in Honest, NEW r \in Rounds
  PROVE [](NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r) /\ [NZNext]_vars
            => (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))'
               \/ (ComputeWork <= n)')
<1>1. GSkip(p, r) => \E q \in Honest : CanCompute(q)
  BY DEF GSkip, CanCompute
<1>2. NZCore /\ GSkip(p, r) /\ NetworkStep => GSkip(p, r)'
  BY GSkipNetworkStable DEF NZCore
<1>3. GSkip(p, r) /\ UNCHANGED vars => GSkip(p, r)'
  BY DEFS GSkip, RSendersOfAnyMessageAt, RSendersOfTypeAtRound, vars
<1>4. NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r) /\ [NZNext]_vars
       => (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))'
          \/ (ComputeWork <= n)'
  <2> SUFFICES ASSUME NZCore, ComputeWork = n + 1, GSkip(p, r), [NZNext]_vars
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))'
                     \/ (ComputeWork <= n)'
    OBVIOUS
  <2>c. \/ (ComputeWork <= n)'
         \/ (NetworkStep /\ ComputeWork' = ComputeWork)
         \/ UNCHANGED vars
    BY <1>1, WorkStepClass
  <2>1. CASE (ComputeWork <= n)'
    BY <2>1
  <2>2. CASE NetworkStep /\ ComputeWork' = ComputeWork
    <3>1. NZCore'
      BY NZCoreBracketPreserves
    <3>2. GSkip(p, r)'
      BY <2>2, <1>2
    <3> QED BY <2>2, <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    <3>1. NZCore'
      BY <2>3, NZCoreStutter
    <3>2. GSkip(p, r)'
      BY <2>3, <1>3
    <3>3. ComputeWork' = ComputeWork
      BY <2>3, ComputeWorkStutter
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>c, <2>1, <2>2, <2>3
<1> QED BY <1>4, PTL

THEOREM SkipComputeProgress ==
  ASSUME NEW n \in Nat, NEW p \in Honest, NEW r \in Rounds,
         WF_vars(SkipRound(p, r)), [][NZNext]_vars
  PROVE (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)) ~> (ComputeWork <= n)
<1>a. [](NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
          /\ <<NZNext /\ SkipRound(p, r)>>_vars => (ComputeWork <= n)')
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
            /\ <<NZNext /\ SkipRound(p, r)>>_vars => (ComputeWork <= n)'
    BY HonestStepDropsBelow DEF NZNext, HonestStep, vars
  <2> QED BY <2>1, PTL
<1>e. [](NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
          => ENABLED <<SkipRound(p, r)>>_vars)
  <2>1. NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
            => ENABLED <<SkipRound(p, r)>>_vars
    BY EnabledSkip DEF NZCore
  <2> QED BY <2>1, PTL
<1>s. [](NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r) /\ [NZNext]_vars
          => (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))'
             \/ (ComputeWork <= n)')
  BY ONLY BoxSkipStabilityLeg
<1> QED BY <1>a, <1>e, <1>s, PTL


(***************************************************************************)
(* Aggregate progress from the existing per-action fairness assumptions.   *)
(***************************************************************************)

THEOREM NZCoreInv == Spec => []NZCore
BY InvProof, SentInvInv, RoundBelowNowInv, DecidedStepInv, DecidedStepBox, BurstFactsInv, PTL
DEFS NZCore, Inv

THEOREM NZNextInv == Spec => [][NZNext]_vars
<1> SUFFICES ASSUME Spec PROVE [][NZNext]_vars
  OBVIOUS
<1>1. []NZCore
  BY NZCoreInv
<1>2. [][Next]_vars
  BY DEF Spec
<1> QED BY <1>1, <1>2, PTL DEF NZNext

LEMMA SkipProgressBoxFO ==
  ASSUME NEW n, NEW p
  PROVE [](  (\A r \in Rounds :
              (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
                => <>(ComputeWork <= n)))
           => ((\E r \in Rounds :
                  NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
                => <>(ComputeWork <= n))  )
<1>1. (\A r \in Rounds :
         (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
           => <>(ComputeWork <= n)))
       => ((\E r \in Rounds :
              NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
            => <>(ComputeWork <= n))
  OBVIOUS
<1> QED BY <1>1, PTL

LEMMA SkipProgressCommute ==
  ASSUME NEW n \in Nat, NEW p \in Honest,
         \A r \in Rounds :
           ((NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
             ~> (ComputeWork <= n))
  PROVE (\E r \in Rounds :
           NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
          ~> (ComputeWork <= n)
<1>0. \A r \in Rounds :
       [](NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
          => <>(ComputeWork <= n))
  BY PTL
<1>1. [](\A r \in Rounds :
       (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
          => <>(ComputeWork <= n)))
  BY <1>0
<1>2. [](  (\A r \in Rounds :
              (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)
                => <>(ComputeWork <= n)))
           => ((\E r \in Rounds :
                  NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
                => <>(ComputeWork <= n))  )
  BY SkipProgressBoxFO
<1> QED BY <1>1, <1>2, PTL

THEOREM ValidatorComputationProgress ==
  ASSUME Spec, NEW n \in Nat, NEW p \in Honest
  PROVE (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
          ~> (ComputeWork <= n)
<1>n. [][NZNext]_vars
  BY NZNextInv
<1>f.  /\ WF_vars(Propose(p))
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
  BY DEF Spec, Fairness
<1>1. (NZCore /\ ComputeWork = n + 1 /\ GPropose(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, ProposeComputeProgress
<1>2. (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPropose(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, TimeoutProposeComputeProgress
<1>3. (NZCore /\ ComputeWork = n + 1 /\ GProposalNoPOL(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, ProposalNoPOLComputeProgress
<1>4. (NZCore /\ ComputeWork = n + 1 /\ GProposalWithPOL(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, ProposalWithPOLComputeProgress
<1>5. (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrevote(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, SchedulePrevoteComputeProgress
<1>6. (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueFirst(p)) ~> (ComputeWork <= n)
  \*  Splitting the WF conjunct out of <1>f keeps this leaf from destructuring
  \*  a 13-way conjunction, and from instantiating a  ~>-shaped theorem, in
  \*  one obligation. The joint form was borderline for the solver, and it
  \*  failed about 1 run in 4.
  <2>1. WF_vars(OnPrevoteQuorumValueFirstTime(p))
    BY <1>f
  <2> QED BY <1>n, <2>1, PrevoteValueFirstComputeProgress
<1>7. (NZCore /\ ComputeWork = n + 1 /\ GPrevoteValueLate(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, PrevoteValueLateComputeProgress
<1>8. (NZCore /\ ComputeWork = n + 1 /\ GPrevoteNil(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, PrevoteNilComputeProgress
<1>9. (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrevote(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, TimeoutPrevoteComputeProgress
<1>10. (NZCore /\ ComputeWork = n + 1 /\ GSchedulePrecommit(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, SchedulePrecommitComputeProgress
<1>11. (NZCore /\ ComputeWork = n + 1 /\ GPrecommitValue(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, PrecommitValueComputeProgress
<1>12. (NZCore /\ ComputeWork = n + 1 /\ GTimeoutPrecommit(p)) ~> (ComputeWork <= n)
  BY <1>n, <1>f, TimeoutPrecommitComputeProgress
<1>13. \A r \in Rounds :
          ((NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
            ~> (ComputeWork <= n))
  <2> SUFFICES ASSUME NEW r \in Rounds
               PROVE (NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
                      ~> (ComputeWork <= n)
    OBVIOUS
  <2> QED BY <1>n, <1>f, SkipComputeProgress
<1>14. (\E r \in Rounds :
           NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r))
          ~> (ComputeWork <= n)
  BY <1>13, SkipProgressCommute
<1>a. (NZCore /\ ComputeWork = n + 1
         /\ ComputeGroupA(p))
        ~> (ComputeWork <= n)
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF ComputeGroupA
<1>b. (NZCore /\ ComputeWork = n + 1
         /\ ComputeGroupB(p))
        ~> (ComputeWork <= n)
  BY <1>5, <1>6, <1>7, <1>8, PTL DEF ComputeGroupB
<1>c. (NZCore /\ ComputeWork = n + 1
         /\ ComputeGroupC(p))
        ~> (ComputeWork <= n)
  BY <1>9, <1>10, <1>11, <1>12, PTL DEF ComputeGroupC
<1>d1. (NZCore /\ ComputeWork = n + 1
          /\ (ComputeGroupA(p) \/ ComputeGroupB(p)))
        ~> (ComputeWork <= n)
  BY <1>a, <1>b, PTL
<1>d2. (\/ (NZCore /\ ComputeWork = n + 1 /\ ComputeGroupC(p))
         \/ (\E r \in Rounds :
               NZCore /\ ComputeWork = n + 1 /\ GSkip(p, r)))
         ~> (ComputeWork <= n)
  BY <1>c, <1>14, PTL
<1>d3. (NZCore /\ ComputeWork = n + 1 /\ GroupedComputationGuard(p))
        ~> (ComputeWork <= n)
  BY <1>d1, <1>d2, GroupedAntecedentSplit, PTL
<1>e. (NZCore /\ ComputeWork = n + 1 /\ ComputationGuard(p))
        ~> (ComputeWork <= n)
  BY <1>d3, ComputationGuardGrouped, PTL
<1> QED BY <1>e, ComputationGuardIsCanCompute, PTL

LEMMA HonestProgressBoxFO ==
  ASSUME NEW n
  PROVE [](  (\A p \in Honest :
              (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p)
                => <>(ComputeWork <= n)))
           => ((\E p \in Honest :
                  NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
                => <>(ComputeWork <= n))  )
<1>1. (\A p \in Honest :
         (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p)
           => <>(ComputeWork <= n)))
       => ((\E p \in Honest :
              NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
            => <>(ComputeWork <= n))
  OBVIOUS
<1> QED BY <1>1, PTL

LEMMA HonestProgressCommute ==
  ASSUME NEW n \in Nat,
         \A p \in Honest :
           ((NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
             ~> (ComputeWork <= n))
  PROVE (\E p \in Honest :
           NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
          ~> (ComputeWork <= n)
<1>0. \A p \in Honest :
       [](NZCore /\ ComputeWork = n + 1 /\ CanCompute(p)
          => <>(ComputeWork <= n))
  BY PTL
<1>1. [](\A p \in Honest :
       (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p)
          => <>(ComputeWork <= n)))
  BY <1>0
<1>2. [](  (\A p \in Honest :
              (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p)
                => <>(ComputeWork <= n)))
           => ((\E p \in Honest :
                  NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
                => <>(ComputeWork <= n))  )
  BY HonestProgressBoxFO
<1> QED BY <1>1, <1>2, PTL

LEMMA AggregateAntecedentSplit ==
  ASSUME NEW n
  PROVE (NZCore /\ ComputeWork = n + 1
          /\ (\E p \in Honest : CanCompute(p)))
        <=> (\E p \in Honest :
              NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
OBVIOUS

THEOREM AggregateComputationFairness ==
  Spec => \A n \in Nat :
    (NZCore /\ ComputeWork = n + 1 /\ (\E p \in Honest : CanCompute(p)))
      ~> (ComputeWork <= n)
<1> SUFFICES ASSUME Spec, NEW n \in Nat
             PROVE (NZCore /\ ComputeWork = n + 1
                     /\ (\E p \in Honest : CanCompute(p)))
                     ~> (ComputeWork <= n)
  OBVIOUS
<1>1. \A p \in Honest :
       ((NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
         ~> (ComputeWork <= n))
  <2> SUFFICES ASSUME NEW p \in Honest
               PROVE (NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
                       ~> (ComputeWork <= n)
    OBVIOUS
  <2> QED BY ValidatorComputationProgress
<1>2. (\E p \in Honest :
         NZCore /\ ComputeWork = n + 1 /\ CanCompute(p))
        ~> (ComputeWork <= n)
  BY <1>1, HonestProgressCommute
<1> QED BY <1>2, AggregateAntecedentSplit, PTL

(***************************************************************************)
(* Every honest computation burst terminates.                              *)
(*                                                                         *)
(* Tick is disabled while an honest computation is enabled. The aggregate  *)
(* fairness lemma can therefore be iterated over ComputeWork, with no      *)
(* assumption of an aggregate fairness condition on the honest steps.      *)
(***************************************************************************)

LEMMA ComputeWorkZeroImpliesQuiescent ==
  ASSUME NZCore, ComputeWork <= 0
  PROVE HonestQuiescent
<1>1. ComputeWork \in Nat
  BY ComputeWorkType DEF NZCore
<1>2. ComputeWork = 0
  BY <1>1, SMT
<1>3. TypeOK
  BY DEF NZCore
<1>4. \A c \in Honest : decision[c] = nil => step[c] # "decided"
  BY DEF NZCore, DecidedStepOp
<1> QED BY <1>2, <1>3, <1>4, ComputeWorkZeroQuiescent DEF HonestQuiescent

LEMMA BoxComputeWorkZeroImpliesQuiescent ==
  []((NZCore /\ ComputeWork <= 0) => HonestQuiescent)
BY ComputeWorkZeroImpliesQuiescent, PTL

LEMMA BoxComputeWorkSplit ==
  ASSUME NEW n \in Nat
  PROVE []((NZCore /\ ComputeWork <= n + 1)
            => ((NZCore /\ ComputeWork <= n)
                \/ (NZCore /\ ComputeWork = n + 1)))
<1>1. (NZCore /\ ComputeWork <= n + 1)
       => ((NZCore /\ ComputeWork <= n)
           \/ (NZCore /\ ComputeWork = n + 1))
  BY ComputeWorkType DEF NZCore
<1> QED BY <1>1, PTL

LEMMA BoxRankProgressCase ==
  ASSUME NEW n \in Nat
  PROVE []((NZCore /\ ComputeWork = n + 1)
            => (HonestQuiescent
                \/ (NZCore /\ ComputeWork = n + 1
                    /\ (\E p \in Honest : CanCompute(p)))))
BY PTL DEF HonestQuiescent

THEOREM ComputeWorkRankProgress ==
  ASSUME Spec, NEW n \in Nat
  PROVE (NZCore /\ ComputeWork = n + 1)
          ~> ((NZCore /\ ComputeWork <= n) \/ HonestQuiescent)
<1>core. []NZCore
  BY NZCoreInv
<1>1. []((NZCore /\ ComputeWork = n + 1)
          => (HonestQuiescent
              \/ (NZCore /\ ComputeWork = n + 1
                  /\ (\E p \in Honest : CanCompute(p)))))
  BY BoxRankProgressCase
<1>2. (NZCore /\ ComputeWork = n + 1
        /\ (\E p \in Honest : CanCompute(p)))
       ~> (ComputeWork <= n)
  BY AggregateComputationFairness
<1>3. (ComputeWork <= n) ~> (NZCore /\ ComputeWork <= n)
  BY <1>core, PTL
<1>4. (NZCore /\ ComputeWork = n + 1
        /\ (\E p \in Honest : CanCompute(p)))
       ~> (NZCore /\ ComputeWork <= n)
  BY <1>2, <1>3, PTL
<1> QED BY <1>1, <1>4, PTL

THEOREM BoundedComputationTerminates ==
  ASSUME Spec
  PROVE \A n \in Nat :
          ((NZCore /\ ComputeWork <= n) ~> HonestQuiescent)
<1> DEFINE R(n) == (NZCore /\ ComputeWork <= n) ~> HonestQuiescent
<1>0. R(0)
  <2>1. []((NZCore /\ ComputeWork <= 0) => HonestQuiescent)
    BY BoxComputeWorkZeroImpliesQuiescent
  <2> QED BY <2>1, PTL DEF R
<1>step. \A n \in Nat : R(n) => R(n + 1)
  <2> TAKE n \in Nat
  <2> SUFFICES ASSUME R(n) PROVE R(n + 1)
    OBVIOUS
  <2>1. (NZCore /\ ComputeWork = n + 1)
         ~> ((NZCore /\ ComputeWork <= n) \/ HonestQuiescent)
    BY ComputeWorkRankProgress
  <2>2. []((NZCore /\ ComputeWork <= n + 1)
            => ((NZCore /\ ComputeWork <= n)
                \/ (NZCore /\ ComputeWork = n + 1)))
    BY BoxComputeWorkSplit
  <2> QED BY <2>1, <2>2, PTL DEF R
<1>all. \A n \in Nat : R(n)
  <2> HIDE DEF R
  <2> QED BY <1>0, <1>step, NatInduction, IsaM("blast")
<1> QED BY <1>all DEF R

LEMMA ComputeWorkBoundCommute ==
  ASSUME NEW TEMPORAL D,
         \A n \in Nat : []((NZCore /\ ComputeWork <= n) => D)
  PROVE [] (\A n \in Nat : ((NZCore /\ ComputeWork <= n) => D))
OBVIOUS

LEMMA ComputeWorkBoundBoxFO ==
  [](  (\A n \in Nat :
          ((NZCore /\ ComputeWork <= n) => <>HonestQuiescent))
     => ((\E n \in Nat : NZCore /\ ComputeWork <= n)
          => <>HonestQuiescent)  )
<1>1. (\A n \in Nat :
        ((NZCore /\ ComputeWork <= n) => <>HonestQuiescent))
       => ((\E n \in Nat : NZCore /\ ComputeWork <= n)
            => <>HonestQuiescent)
  OBVIOUS
<1> QED BY <1>1, PTL

THEOREM ComputeWorkExistsLT ==
  ASSUME \A n \in Nat :
          ((NZCore /\ ComputeWork <= n) ~> HonestQuiescent)
  PROVE (\E n \in Nat : NZCore /\ ComputeWork <= n) ~> HonestQuiescent
<1>0. \A n \in Nat :
       []((NZCore /\ ComputeWork <= n) => <>HonestQuiescent)
  BY PTL
<1>1. [](\A n \in Nat :
       ((NZCore /\ ComputeWork <= n) => <>HonestQuiescent))
  BY <1>0, ComputeWorkBoundCommute
<1>2. [](  (\A n \in Nat :
              ((NZCore /\ ComputeWork <= n) => <>HonestQuiescent))
           => ((\E n \in Nat : NZCore /\ ComputeWork <= n)
                => <>HonestQuiescent)  )
  BY ComputeWorkBoundBoxFO
<1> QED BY <1>1, <1>2, PTL

LEMMA BoxComputeWorkExN ==
  [](NZCore => (\E n \in Nat : NZCore /\ ComputeWork <= n))
<1>1. NZCore => (\E n \in Nat : NZCore /\ ComputeWork <= n)
  BY ComputeWorkType DEF NZCore
<1> QED BY <1>1, PTL

THEOREM ComputationBurstTerminates == Spec => <>HonestQuiescent
<1> SUFFICES ASSUME Spec PROVE <>HonestQuiescent
  OBVIOUS
<1>core. []NZCore
  BY NZCoreInv
<1>1. \A n \in Nat :
       ((NZCore /\ ComputeWork <= n) ~> HonestQuiescent)
  BY BoundedComputationTerminates
<1>2. (\E n \in Nat : NZCore /\ ComputeWork <= n) ~> HonestQuiescent
  BY <1>1, ComputeWorkExistsLT
<1>3. [](\E n \in Nat : NZCore /\ ComputeWork <= n)
  BY <1>core, BoxComputeWorkExN, PTL
<1> QED BY <1>2, <1>3, PTL

(***************************************************************************)
(* Quiescence transfers the control to the clock.                          *)
(*                                                                         *)
(* This is deliberately a bridge on ENABLED, and not a theorem about an    *)
(* eventual Tick. A Deliver action can enable an honest computation again  *)
(* before Tick occurs. The later clock proof must discharge that fair      *)
(* interleaving explicitly.                                                *)
(***************************************************************************)

LEMMA BoxPreGSTQuiescenceEnablesTick ==
  []((NZCore /\ now < GST /\ HonestQuiescent /\ TickUseful)
      => ENABLED <<Tick>>_vars)
<1>1. (NZCore /\ now < GST /\ HonestQuiescent /\ TickUseful) => TypeOK
  BY DEF NZCore
<1>2. (NZCore /\ now < GST /\ HonestQuiescent /\ TickUseful)
       => ENABLED <<Tick>>_vars
  <2> SUFFICES ASSUME NZCore, now < GST, HonestQuiescent, TickUseful
               PROVE ENABLED <<Tick>>_vars
    OBVIOUS
  <2>1. TypeOK
    BY DEF NZCore
  <2> QED BY <2>1, BurstBottomEnablesTick
<1> QED BY <1>2, PTL

THEOREM PreGSTQuiescenceEnablesTick ==
  Spec => []((now < GST /\ HonestQuiescent /\ TickUseful)
              => ENABLED <<Tick>>_vars)
<1> SUFFICES ASSUME Spec
             PROVE []((now < GST /\ HonestQuiescent /\ TickUseful)
                      => ENABLED <<Tick>>_vars)
  OBVIOUS
<1>core. []NZCore
  BY NZCoreInv
<1>1. []((NZCore /\ now < GST /\ HonestQuiescent /\ TickUseful)
          => ENABLED <<Tick>>_vars)
  BY BoxPreGSTQuiescenceEnablesTick
<1> QED BY <1>core, <1>1, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)