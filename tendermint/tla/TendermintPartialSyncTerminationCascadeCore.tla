--------------- MODULE TendermintPartialSyncTerminationCascadeCore -------------
(***************************************************************************)
(* The date facts of a correct vote, and the joint induction of            *)
(* CascadeCore.                                                            *)
(*                                                                         *)
(* Owns ProposeExitByDeadline, RoundVoteAfterEntry, NilPrevoteInWindow,    *)
(* CascadeAnchor, StepPrecommitHasPrecommit, PrecommitQuorumFor,           *)
(* CascadeEscape and CascadeCore. The one temporal export is               *)
(* CascadeCoreLatch.                                                       *)
(*                                                                         *)
(* CascadeCore is defined in this link, beside its own induction. This     *)
(* is the largest link by justification count. Cut it again at the         *)
(* header "Item 13. CascadeCore" if the edit cycle gets too slow.          *)
(*                                                                         *)
(* THE CHAIN. Link 3 of 4. Above: ...CascadeRegion. Below: ...Cascade.     *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationCascadeRegion

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 12a. The propose exit ceiling.                                     *)
(*                                                                         *)
(*  No correct validator sits at r in step "propose" after the cascade     *)
(*  deadline. ProposalDated puts the round-r proposal in the pool at or    *)
(*  below the ceiling. GossipDeadline delivers it one Delta later.         *)
(*  ProposeExitEnabled then reports a computation step for the validator.  *)
(*  The maximal progress guard of Tick forbids a tick while a computation  *)
(*  step exists, so the clock stops at the deadline.                       *)
(*                                                                         *)
(* The shape is the shape of ProposalDated: a GLOBAL invariant that        *)
(* carries the region facts in its antecedent, so it needs no latch. The   *)
(* cascade reads it wherever a validator has not prevoted at r yet,        *)
(* because step "propose" is the one step that carries no prevote.         *)
(***************************************************************************)

\* Only OnTimeoutPrecommit and SkipRound write step "propose", and both raise
\* the round in the same step. A step that keeps the round cannot enter step
\* "propose".
LEMMA ProposeStepEntered ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest,
         step'[c] = "propose", round'[c] = round[c]
  PROVE  step[c] = "propose"
BY StepWriterStep
DEFS OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Rounds, SkipRound, TypeOK

\* ---- Arithmetic in a MINIMAL context --------------------------------------
\* The deadline is the ceiling plus one gossip delay. Each helper returns
\* everything its call site needs, so the call site never searches.
LEMMA DeadlineAboveCeiling ==
  ASSUME NEW e \in Nat, NEW d \in Nat, NEW k \in Nat, NEW n \in Nat,
         NEW g \in Nat, d > 1, e >= g, n >= e + 2 * d + k
  PROVE  /\ e + d + k \in Nat
         /\ e + d + k >= g
         /\ n > e + d + k
         /\ n >= (e + d + k) + d
BY SMT

LEMMA ClockLeFreshDeadline ==
  ASSUME NEW n \in Nat, NEW np \in Int, NEW d \in Nat, NEW k \in Nat,
         d > 1, np = n \/ np = n + 1
  PROVE  np <= n + 2 * d + k
BY SMT

LEMMA SuccLeFromNe ==
  ASSUME NEW x \in Int, NEW y \in Int, x <= y, x # y
  PROVE  x + 1 <= y
BY SMT

LEMMA RoundBelowAndAbovePred ==
  ASSUME NEW x \in Int, NEW y \in Int, x > y - 1, x < y
  PROVE  FALSE
BY SMT

\* ---- The state content at the deadline ------------------------------------
LEMMA ProposeExitAtDeadline ==
  ASSUME TypeOK, GossipDeadline, ProposalDated, ProposalJustified,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         RoundOrigin(p, r), Proposer[r] \in Honest, ~ SomeCorrectDecided,
         now >= CascadeDeadline(p, r),
         round[c] = r, step[c] = "propose"
  PROVE  CanCompute(c)
BY DeadlineAboveCeiling, DeltaType, GSTType, ProposeExitEnabled, RoundTypes
DEFS CascadeCeiling, CascadeDeadline, OFF, ProposalDated, ProposalJustified, RoundOrigin, TypeOK

-----------------------------------------------------------------------------
ProposeExitByDeadline ==
  \A p \in Honest, r \in Rounds, c \in Honest :
    ( /\ RoundOrigin(p, r)
      /\ Proposer[r] \in Honest
      /\ round[c] = r
      /\ step[c] = "propose" )
    => \/ SomeCorrectDecided
       \/ now <= CascadeDeadline(p, r)

LEMMA ProposeExitByDeadlineStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentTimeLeNow, GossipDeadline,
         RoundEntryHistory, EnteredAtLeNow, EnteredCurrentRound,
         CrossingBacked, EntryWindowCore, PrecommitDeadlineNotPassed,
         ProposalDated, ProposalJustified, DecidedStepOp, [Next]_vars,
         ProposeExitByDeadline
  PROVE  ProposeExitByDeadline'
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
                    RoundOrigin(p, r)', Proposer[r] \in Honest,
                    round'[c] = r, step'[c] = "propose",
                    ~ SomeCorrectDecided'
             PROVE  now' <= CascadeDeadline(p, r)'
  BY DEF ProposeExitByDeadline
<1>nd. /\ ~ SomeCorrectDecided
       /\ \A x \in Honest : step[x] # "decided"
  <2>1. ~ SomeCorrectDecided
    BY DecidedLatchStep
  <2> QED
    BY <2>1 DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
<1>r0. /\ r \in Nat /\ r > 0 /\ r - 1 \in Rounds
       /\ Delta \in Nat /\ Delta > 1 /\ GST \in Nat
       /\ TimeoutPrecommit(r - 1) \in Nat /\ TimeoutPrecommit(r - 1) > 0
       /\ now \in Nat /\ now' \in Nat /\ round[c] \in Nat
  <2>1. r \in Nat /\ r > 0
    BY DEFS RoundOrigin, Rounds
  <2>2. /\ r - 1 \in Rounds /\ TimeoutPrecommit(r - 1) \in Nat
        /\ TimeoutPrecommit(r - 1) > 0
    BY <2>1, RoundTypes, TimeoutPrecommitPos
  <2>3. now \in Nat /\ now' \in Nat /\ round[c] \in Nat
    BY NowShape DEFS Rounds, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType, GSTType
\*  The entry is missing before the step, so it can be recorded only AT the
\*  clock. One tick cannot pass a deadline that is a positive offset above the
\*  clock.
<1>a. CASE enteredAt[p][r] = OFF
  <2>1. enteredAt'[p][r] = now
    BY <1>a, EntryUpdateDisciplineStep
    DEFS EntryUpdateDiscipline, RoundOrigin
  <2>2. now' = now \/ now' = now + 1
    BY NowShape
  <2>3. CascadeDeadline(p, r)' = now + 2 * Delta + TimeoutPrecommit(r - 1)
    BY <2>1 DEF CascadeDeadline
  <2> QED
    BY <1>r0, <2>2, <2>3, ClockLeFreshDeadline
<1>b. CASE enteredAt[p][r] # OFF
  <2>e. enteredAt'[p][r] = enteredAt[p][r]
    BY <1>b, EnteredAtFrozenStep
  <2>d. CascadeDeadline(p, r)' = CascadeDeadline(p, r)
    BY <2>e DEF CascadeDeadline
  <2>ro. RoundOrigin(p, r)
    <3>1. EntriesAtOrAfter(r, enteredAt[p][r])
      <4> SUFFICES ASSUME NEW x \in Honest, enteredAt[x][r] # OFF
                   PROVE  enteredAt[x][r] >= enteredAt[p][r]
        BY DEF EntriesAtOrAfter
      <4>1. enteredAt'[x][r] = enteredAt[x][r]
        BY EnteredAtFrozenStep
      <4> QED
        BY <2>e, <4>1 DEFS EntriesAtOrAfter, OFF, RoundOrigin
    <3> QED
      BY <1>b, <2>e, <3>1 DEF RoundOrigin
  <2>ge. enteredAt[p][r] \in Nat /\ enteredAt[p][r] >= GST
    <3>1. enteredAt[p][r] > GST
      BY <2>ro DEF RoundOrigin
    <3> QED
      BY <1>b, <3>1 DEFS OFF, TypeOK
  <2>dt. CascadeDeadline(p, r) \in Nat
    BY <1>b, <1>r0, CascadeDeadlineType
  <2>1. CASE round[c] = r
    <3>st. step[c] = "propose"
      BY <2>1, ProposeStepEntered
    <3>ih. now <= CascadeDeadline(p, r)
      BY <1>nd, <2>1, <2>ro, <3>st DEF ProposeExitByDeadline
    <3>2. CASE now' = now
      BY <2>d, <3>2, <3>ih
    <3>3. CASE now' = now + 1
      <4>q. ~ \E x \in Honest : CanCompute(x)
        BY <3>3, TickFromClockStep DEF Tick
      <4>ne. now # CascadeDeadline(p, r)
        <5> SUFFICES ASSUME now = CascadeDeadline(p, r)
                     PROVE  FALSE
          OBVIOUS
        <5>1. now >= CascadeDeadline(p, r)
          BY <1>r0, <2>dt, GeFromEq
        <5>2. CanCompute(c)
          BY <1>nd, <2>1, <2>ro, <3>st, <5>1, ProposeExitAtDeadline
        <5> QED
          BY <4>q, <5>2
      <4>1. now + 1 <= CascadeDeadline(p, r)
        BY <1>r0, <2>dt, <3>ih, <4>ne, SuccLeFromNe
      <4> QED
        BY <2>d, <3>3, <4>1
    <3> QED
      BY <3>2, <3>3, NowShape
\* c enters r at this step, so the clock is frozen and the entry deadline of
\* EntryWindowCore keeps it at or below the ceiling.
  <2>2. CASE round[c] # r
    <3>ne. round'[c] # round[c]
      BY <2>2
    <3>1. round[c] < r /\ now' = now
      BY <3>ne, RoundRaiseFrame
    <3>ct. CascadeCeiling(p, r) \in Nat
      BY <1>r0, <2>ge DEF CascadeCeiling
    <3>ap. AnyPrecommitDated(r - 1, enteredAt[p][r])
      BY <1>b, <1>r0, <2>ro, EntryCertificateDated
    <3>2. now <= CascadeCeiling(p, r)
      <4> SUFFICES ASSUME now > CascadeCeiling(p, r)
                   PROVE  FALSE
        BY <1>r0, <3>ct
\* The hypotheses of EntryReachedFromWindow, in its own shape, so that the
\* unifier has nothing to search for.
      <4>hy. /\ r - 1 \in Rounds
             /\ enteredAt[p][r] \in Nat
             /\ enteredAt[p][r] >= GST
             /\ AnyPrecommitDated(r - 1, enteredAt[p][r])
             /\ now > enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)
             /\ step[c] # "decided"
        BY <1>nd, <1>r0, <2>ge, <3>ap DEF CascadeCeiling
      <4>1. round[c] > r - 1
        BY <4>hy, EntryReachedFromWindow
      <4> QED
        BY <1>r0, <3>1, <4>1, RoundBelowAndAbovePred
    <3>3. CascadeCeiling(p, r) <= CascadeDeadline(p, r)
      BY <1>r0, <2>ge, CeilingBelowDeadline
      DEFS CascadeCeiling, CascadeDeadline
    <3> QED
      BY <1>r0, <2>d, <2>dt, <3>1, <3>2, <3>3, <3>ct
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>a, <1>b

THEOREM ProposeExitByDeadlineInv ==
  ASSUME Spec PROVE []ProposeExitByDeadline
<1>1. ProposeExitByDeadline
  BY DEFS Init, OFF, ProposeExitByDeadline, RoundOrigin, Spec
<1>ds. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentTimeLeNow /\ GossipDeadline
           /\ RoundEntryHistory /\ EnteredAtLeNow /\ EnteredCurrentRound
           /\ CrossingBacked /\ EntryWindowCore /\ PrecommitDeadlineNotPassed
           /\ ProposalDated /\ ProposalJustified /\ DecidedStepOp
           /\ [Next]_vars  )
  BY <1>ds, CrossingBackedInv, EnteredAtLeNowInv, EnteredCurrentRoundInv,
     EntryWindowCoreInv, GossipDeadlineInv, InvProof,
     PrecommitDeadlineNotPassedInv, ProposalDatedInv, ProposalJustifiedInv,
     PTL, RoundEntryHistoryInv, SentTimeLeNowInv
  DEFS Inv, Spec
<1>3. [](ProposeExitByDeadline => ProposeExitByDeadline')
  BY <1>2, ProposeExitByDeadlineStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 12b. Two facts about the DATE of a correct vote.                   *)
(*                                                                         *)
(* Every anchor of the cascade is a quorum date, and each one has to sit   *)
(* at or after the entry of p into r. RoundVoteAfterEntry gives the        *)
(* per-message half of that, and RoundOrigin gives the rest.               *)
(*                                                                         *)
(*  NilPrevoteInWindow carries the history that NilPrevoteBlocks needs.    *)
(*  Both producers of a correct nil prevote need step "propose". Item 12a  *)
(*  stops the clock at the deadline while any correct validator is in step *)
(*  "propose" at r. The timestamp of the nil prevote is therefore inside   *)
(*  the window at every LATER state, which an invariant can state and a    *)
(*  state lemma cannot.                                                    *)
(***************************************************************************)

RoundVoteAfterEntry ==
  \A c \in Honest, rr \in Rounds, w \in ValuesOrNil :
    /\ (  Prevote(c, rr, w) \in sent
          => /\ enteredAt[c][rr] # OFF
             /\ sentTime[Prevote(c, rr, w)] >= enteredAt[c][rr]  )
    /\ (  Precommit(c, rr, w) \in sent
          => /\ enteredAt[c][rr] # OFF
             /\ sentTime[Precommit(c, rr, w)] >= enteredAt[c][rr]  )

LEMMA RoundVoteAfterEntryStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory,
         EnteredAtLeNow, EnteredCurrentRound, [Next]_vars,
         RoundVoteAfterEntry
  PROVE  RoundVoteAfterEntry'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>ea. \A x \in Honest, rr \in Rounds :
         enteredAt[x][rr] # OFF => enteredAt'[x][rr] = enteredAt[x][rr]
  BY EnteredAtFrozenStep
<1> SUFFICES ASSUME NEW c \in Honest, NEW rr \in Rounds, NEW w \in ValuesOrNil
             PROVE  /\ (  Prevote(c, rr, w) \in sent'
                          => /\ enteredAt'[c][rr] # OFF
                             /\ sentTime'[Prevote(c, rr, w)]
                                  >= enteredAt'[c][rr]  )
                    /\ (  Precommit(c, rr, w) \in sent'
                          => /\ enteredAt'[c][rr] # OFF
                             /\ sentTime'[Precommit(c, rr, w)]
                                  >= enteredAt'[c][rr]  )
  BY DEF RoundVoteAfterEntry
\*  The entry of the sender into its CURRENT round is populated, and it is at
\*  or below the clock. A fresh vote carries the clock as its date. Packaged
\*  once, because the two halves differ only in the constructor.
<1>en. ASSUME round[c] = rr
       PROVE  /\ enteredAt[c][rr] # OFF
              /\ enteredAt[c][rr] <= now
              /\ enteredAt'[c][rr] = enteredAt[c][rr]
  <2>1. enteredAt[c][rr] # OFF
    BY <1>en DEF EnteredCurrentRound
  <2>2. enteredAt[c][rr] <= now
    BY <2>1 DEF EnteredAtLeNow
  <2> QED
    BY <1>ea, <2>1, <2>2
<1>1. ASSUME Prevote(c, rr, w) \in sent'
      PROVE  /\ enteredAt'[c][rr] # OFF
             /\ sentTime'[Prevote(c, rr, w)] >= enteredAt'[c][rr]
  <2>m. Prevote(c, rr, w) \in Message
    BY HonestSubValidators, MsgPrevote
  <2>1. CASE Prevote(c, rr, w) \in sent
    <3>1. /\ enteredAt[c][rr] # OFF
          /\ sentTime[Prevote(c, rr, w)] >= enteredAt[c][rr]
      BY <2>1 DEF RoundVoteAfterEntry
    <3>2. sentTime'[Prevote(c, rr, w)] = sentTime[Prevote(c, rr, w)]
      BY <1>fz, <2>1, <2>m DEF sent
    <3>3. enteredAt'[c][rr] = enteredAt[c][rr]
      BY <1>ea, <3>1
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE Prevote(c, rr, w) \notin sent
    <3>1. /\ Prevote(c, rr, w).round = round[Prevote(c, rr, w).sender]
          /\ sentTime'[Prevote(c, rr, w)] = now
      BY <1>1, <2>2, <2>m, FreshPrevoteAction DEF Prevote
    <3>2. round[c] = rr /\ sentTime'[Prevote(c, rr, w)] = now
      BY <3>1 DEF Prevote
    <3> QED
      BY <1>en, <3>2
  <2> QED
    BY <2>1, <2>2
<1>2. ASSUME Precommit(c, rr, w) \in sent'
      PROVE  /\ enteredAt'[c][rr] # OFF
             /\ sentTime'[Precommit(c, rr, w)] >= enteredAt'[c][rr]
  <2>m. Precommit(c, rr, w) \in Message
    BY HonestSubValidators, MsgPrecommit
  <2>1. CASE Precommit(c, rr, w) \in sent
    <3>1. /\ enteredAt[c][rr] # OFF
          /\ sentTime[Precommit(c, rr, w)] >= enteredAt[c][rr]
      BY <2>1 DEF RoundVoteAfterEntry
    <3>2. sentTime'[Precommit(c, rr, w)] = sentTime[Precommit(c, rr, w)]
      BY <1>fz, <2>1, <2>m DEF sent
    <3>3. enteredAt'[c][rr] = enteredAt[c][rr]
      BY <1>ea, <3>1
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE Precommit(c, rr, w) \notin sent
    <3>1. /\ Precommit(c, rr, w).round = round[Precommit(c, rr, w).sender]
          /\ sentTime'[Precommit(c, rr, w)] = now
      BY <1>2, <2>2, <2>m, FreshPrecommitAction DEF Precommit
    <3>2. round[c] = rr /\ sentTime'[Precommit(c, rr, w)] = now
      BY <3>1 DEF Precommit
    <3> QED
      BY <1>en, <3>2
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2

THEOREM RoundVoteAfterEntryInv ==
  ASSUME Spec PROVE []RoundVoteAfterEntry
<1>1. RoundVoteAfterEntry
  BY DEFS Init, OFF, RoundVoteAfterEntry, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
           /\ EnteredAtLeNow /\ EnteredCurrentRound /\ [Next]_vars  )
  BY EnteredAtLeNowInv, EnteredCurrentRoundInv, InvProof, PTL,
     RoundEntryHistoryInv, SentInvInv
  DEFS Inv, Spec
<1>3. [](RoundVoteAfterEntry => RoundVoteAfterEntry')
  BY <1>2, RoundVoteAfterEntryStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
NilPrevoteInWindow ==
  \A p \in Honest, r \in Rounds, c \in Honest :
    ( /\ RoundOrigin(p, r)
      /\ Proposer[r] \in Honest
      /\ Prevote(c, r, nil) \in sent )
    => \/ SomeCorrectDecided
       \/ sentTime[Prevote(c, r, nil)] <= CascadeDeadline(p, r)

LEMMA NilPrevoteInWindowStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory, SentTimeLeNow,
         ProposeExitByDeadline, [Next]_vars,
         NilPrevoteInWindow
  PROVE  NilPrevoteInWindow'
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1> SUFFICES ASSUME NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
                    RoundOrigin(p, r)', Proposer[r] \in Honest,
                    Prevote(c, r, nil) \in sent',
                    ~ SomeCorrectDecided'
             PROVE  sentTime'[Prevote(c, r, nil)] <= CascadeDeadline(p, r)'
  BY DEF NilPrevoteInWindow
<1>nd. ~ SomeCorrectDecided
  BY DecidedLatchStep
<1>m. Prevote(c, r, nil) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>r0. /\ r \in Nat /\ r > 0 /\ Delta \in Nat /\ Delta > 1
       /\ TimeoutPrecommit(r - 1) \in Nat
       /\ now \in Nat /\ now' \in Nat
  <2>1. r \in Nat /\ r > 0
    BY DEFS RoundOrigin, Rounds
  <2>2. TimeoutPrecommit(r - 1) \in Nat
    BY <2>1, RoundTypes
  <2>3. now \in Nat /\ now' \in Nat
    BY NowShape DEF TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType
\* The date is at or below the clock, whether the message is old or fresh.
<1>cl. /\ sentTime'[Prevote(c, r, nil)] \in Int
       /\ sentTime'[Prevote(c, r, nil)] <= now
  <2>1. CASE Prevote(c, r, nil) \in sent
    <3>1. sentTime[Prevote(c, r, nil)] \in Int
          /\ sentTime[Prevote(c, r, nil)] <= now
      BY <1>m, <2>1 DEFS OFF, sent, SentTimeLeNow, TypeOK
    <3>2. sentTime'[Prevote(c, r, nil)] = sentTime[Prevote(c, r, nil)]
      BY <1>fz, <1>m, <2>1 DEF sent
    <3> QED
      BY <3>1, <3>2
  <2>2. CASE Prevote(c, r, nil) \notin sent
    <3>1. sentTime'[Prevote(c, r, nil)] = now
      BY <1>m, <2>2, FreshPrevoteAction DEF Prevote
    <3> QED
      BY <1>r0, <3>1
  <2> QED
    BY <2>1, <2>2
\* A fresh entry pins the deadline at a non-negative offset above the clock.
<1>a. CASE enteredAt[p][r] = OFF
  <2>1. enteredAt'[p][r] = now
    BY <1>a, EntryUpdateDisciplineStep
    DEFS EntryUpdateDiscipline, RoundOrigin
  <2>2. CascadeDeadline(p, r)' = now + 2 * Delta + TimeoutPrecommit(r - 1)
    BY <2>1 DEF CascadeDeadline
  <2>3. /\ now + 2 * Delta + TimeoutPrecommit(r - 1) \in Int
        /\ now <= now + 2 * Delta + TimeoutPrecommit(r - 1)
    BY <1>r0, CeilingBelowDeadline, ClockLeFreshDeadline
  <2> QED
    BY <1>cl, <1>r0, <2>2, <2>3
<1>b. CASE enteredAt[p][r] # OFF
  <2>e. enteredAt'[p][r] = enteredAt[p][r]
    BY <1>b, EnteredAtFrozenStep
  <2>d. CascadeDeadline(p, r)' = CascadeDeadline(p, r)
    BY <2>e DEF CascadeDeadline
  <2>ro. RoundOrigin(p, r)
    <3>1. EntriesAtOrAfter(r, enteredAt[p][r])
      <4> SUFFICES ASSUME NEW x \in Honest, enteredAt[x][r] # OFF
                   PROVE  enteredAt[x][r] >= enteredAt[p][r]
        BY DEF EntriesAtOrAfter
      <4>1. enteredAt'[x][r] = enteredAt[x][r]
        BY EnteredAtFrozenStep
      <4> QED
        BY <2>e, <4>1 DEFS EntriesAtOrAfter, OFF, RoundOrigin
    <3> QED
      BY <1>b, <2>e, <3>1 DEF RoundOrigin
  <2>1. CASE Prevote(c, r, nil) \in sent
    <3>1. sentTime[Prevote(c, r, nil)] <= CascadeDeadline(p, r)
      BY <1>nd, <2>1, <2>ro DEF NilPrevoteInWindow
    <3>2. sentTime'[Prevote(c, r, nil)] = sentTime[Prevote(c, r, nil)]
      BY <1>fz, <1>m, <2>1 DEF sent
    <3> QED
      BY <2>d, <3>1, <3>2
\* A fresh nil prevote leaves step "propose" at the sender's own round, and
\* item 12a stops the clock at the deadline there.
  <2>2. CASE Prevote(c, r, nil) \notin sent
    <3>1. step[c] = "propose" /\ round[c] = r
      <4>1. step[Prevote(c, r, nil).sender] = "propose"
        BY <1>m, <2>2, FreshHonestPrevoteEmitter DEF Prevote
      <4>2. Prevote(c, r, nil).round = round[Prevote(c, r, nil).sender]
        BY <1>m, <2>2, FreshPrevoteAction DEF Prevote
      <4> QED
        BY <4>1, <4>2 DEF Prevote
    <3>2. now <= CascadeDeadline(p, r)
      BY <1>nd, <2>ro, <3>1 DEF ProposeExitByDeadline
    <3>3. CascadeDeadline(p, r) \in Int
      BY <1>b, <1>r0, CascadeDeadlineType
    <3> QED
      BY <1>cl, <1>r0, <2>d, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>a, <1>b

THEOREM NilPrevoteInWindowInv ==
  ASSUME Spec PROVE []NilPrevoteInWindow
<1>1. NilPrevoteInWindow
  BY DEFS Init, NilPrevoteInWindow, OFF, sent, Spec
<1>2. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory
           /\ SentTimeLeNow /\ ProposeExitByDeadline /\ [Next]_vars  )
  BY InvProof, ProposeExitByDeadlineInv, PTL, RoundEntryHistoryInv,
     SentInvInv, SentTimeLeNowInv
  DEFS Inv, Spec
<1>3. [](NilPrevoteInWindow => NilPrevoteInWindow')
  BY <1>2, NilPrevoteInWindowStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 13a. The helpers of the joint induction.                           *)
(***************************************************************************)

\*  The anchor one gossip delay BELOW the ceiling. Every argument that has to
\*  pass the entry spread is anchored here. A polka that is dated at the
\*  ceiling is one Delta from every correct validator. The prevote margin of
\*  Lemma5Timeouts is exactly the slack that this leaves.
CascadeAnchor(p, r) == enteredAt[p][r] + TimeoutPrecommit(r - 1)

\* Arithmetic in a MINIMAL context. The three dates of the cascade, in order,
\* with every fact a call site needs.
LEMMA CascadeDateOrder ==
  ASSUME NEW e \in Nat, NEW d \in Nat, NEW k \in Nat, d > 1
  PROVE  /\ e + k \in Nat
         /\ e + d + k \in Nat
         /\ e + 2 * d + k \in Nat
         /\ e <= e + k
         /\ (e + k) + d = e + d + k
         /\ (e + d + k) + d = e + 2 * d + k
BY SMT

\* The whole correct set is a Byzantine quorum, so anything all of it has sent
\* is a dated certificate. QuorumAvailable is the witness.
LEMMA AllHonestGivesPolka ==
  ASSUME NEW rr \in Rounds, NEW v \in ValuesOrNil, NEW t,
         \A c \in Honest : /\ Prevote(c, rr, v) \in sent
                           /\ sentTime[Prevote(c, rr, v)] <= t
  PROVE  PolkaDated(rr, v, t)
BY QuorumAvailable DEF PolkaDated

LEMMA AllHonestGivesPrecommitQuorum ==
  ASSUME NEW rr \in Rounds, NEW v \in Values,
         \A c \in Honest : Precommit(c, rr, v) \in sent
  PROVE  \E Q \in ByzQuorum : \A s \in Q : Precommit(s, rr, v) \in sent
BY QuorumAvailable

-----------------------------------------------------------------------------
\*  Step "precommit" carries a precommit at the validator's own round. The
\*  twin of StepPastProposeHasPrevote. All three writers of step "precommit"
\*  broadcast a precommit at round[c] in the same step. The two writers of the
\*  round leave step "propose" behind them. A change of round can therefore
\*  not land in step "precommit".
StepPrecommitHasPrecommit ==
  \A c \in Honest :
    step[c] = "precommit"
      => \E w \in ValuesOrNil : Precommit(c, round[c], w) \in sent

LEMMA StepPrecommitHasPrecommitStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, StepPrecommitHasPrecommit
  PROVE  StepPrecommitHasPrecommit'
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1> SUFFICES ASSUME NEW c \in Honest, step'[c] = "precommit"
             PROVE  \E w \in ValuesOrNil : Precommit(c, round'[c], w) \in sent'
  BY DEF StepPrecommitHasPrecommit
\* One typing fact, once. Every constructor below reads the round off it.
<1>ty. c \in Validators /\ round[c] \in Rounds /\ now \in Nat
  BY HonestSubValidators DEF TypeOK
<1>r. round'[c] = round[c]
  <2> SUFFICES ASSUME round'[c] # round[c]
               PROVE  FALSE
    OBVIOUS
  <2>1. \E q \in Honest : \E rr \in Rounds :
          /\ round' = [round EXCEPT ![q] = rr]
          /\ ((OnTimeoutPrecommit(q) /\ rr = round[q] + 1) \/ SkipRound(q, rr))
    BY RoundEnteredStep
  <2> QED
    BY <2>1 DEFS OnTimeoutPrecommit, Rounds, SkipRound, TypeOK
<1>1. CASE step[c] = "precommit"
  BY <1>1, <1>r, <1>sub DEF StepPrecommitHasPrecommit
<1>2. CASE step[c] # "precommit"
  <2>w. \/ OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
        \/ OnPrevoteQuorumValueFirstTime(c) \/ OnPrevoteQuorumNil(c)
        \/ OnTimeoutPrevote(c) \/ OnPrecommitQuorumValue(c)
        \/ OnTimeoutPrecommit(c) \/ (\E rr \in Rounds : SkipRound(c, rr))
    BY <1>2, StepWriterStep
\* The three prevote-step exits are the writers of step "precommit", and each
\* broadcasts its precommit at round[c].
  <2>1. CASE OnPrevoteQuorumValueFirstTime(c)
    <3>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
            Broadcast(c, Precommit(c, round[c], prop.value))
      BY <2>1 DEF OnPrevoteQuorumValueFirstTime
    <3>2. prop.value \in Values
      BY <1>ty, <3>1, RProposalValueTyped
    <3>3. Precommit(c, round[c], prop.value) \in Message
      BY <1>ty, <3>2, MsgPrecommit DEF ValuesOrNil
    <3>4. Precommit(c, round[c], prop.value) \in sent'
      BY <1>ty, <3>1, <3>3 DEFS Broadcast, OFF, sent, TypeOK
    <3> QED
      BY <1>r, <3>2, <3>4 DEF ValuesOrNil
  <2>1b. CASE OnPrevoteQuorumNil(c) \/ OnTimeoutPrevote(c)
    <3>1. Broadcast(c, Precommit(c, round[c], nil))
      BY <2>1b DEFS OnPrevoteQuorumNil, OnTimeoutPrevote
    <3>2. Precommit(c, round[c], nil) \in Message
      BY <1>ty, MsgPrecommit DEF ValuesOrNil
    <3>3. Precommit(c, round[c], nil) \in sent'
      BY <1>ty, <3>1, <3>2 DEFS Broadcast, OFF, sent, TypeOK
    <3> QED
      BY <1>r, <3>3 DEF ValuesOrNil
\* Every other writer lands in a different step.
  <2>2. CASE OnTimeoutPropose(c) \/ OnProposalNoPOL(c) \/ OnProposalWithPOL(c)
    BY <2>2 DEFS OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPropose, TypeOK
  <2>3. CASE OnPrecommitQuorumValue(c)
    BY <2>3 DEFS OnPrecommitQuorumValue, TypeOK
  <2>4. CASE OnTimeoutPrecommit(c)
    BY <2>4 DEFS OnTimeoutPrecommit, Rounds, TypeOK
  <2>5. CASE \E rr \in Rounds : SkipRound(c, rr)
    BY <2>5 DEFS Rounds, SkipRound, TypeOK
  <2> QED
    BY <2>1, <2>1b, <2>2, <2>3, <2>4, <2>5, <2>w
<1> QED
  BY <1>1, <1>2

THEOREM StepPrecommitHasPrecommitInv ==
  ASSUME Spec PROVE []StepPrecommitHasPrecommit
<1>1. StepPrecommitHasPrecommit
  BY DEFS Init, StepPrecommitHasPrecommit, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEFS Inv, Spec
<1>3. [](StepPrecommitHasPrecommit => StepPrecommitHasPrecommit')
  BY <1>2, StepPrecommitHasPrecommitStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
\* A correct prevote for a VALUE at r carries the value of the round-r
\* proposal. PrevoteJustified reports the proposal that backs it, and
\* HonestProposalUnique identifies that proposal with the one in the antecedent.
LEMMA UniqueValuePrevote ==
  ASSUME TypeOK, SentTimeLeNow, PrevoteJustified, HonestProposalUnique,
         NEW r \in Rounds, NEW c \in Honest, NEW w \in Values, NEW v \in Values,
         NEW T \in Nat, Proposer[r] \in Honest,
         Prevote(c, r, w) \in sent, Justified(r, v, T)
  PROVE  w = v
<1>m. Prevote(c, r, w) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>t. /\ sentTime[Prevote(c, r, w)] \in Nat
      /\ sentTime[Prevote(c, r, w)] <= sentTime[Prevote(c, r, w)]
  <2>1. sentTime[Prevote(c, r, w)] \in Nat
    BY <1>m DEFS OFF, sent, SentTimeLeNow, TypeOK
  <2> QED
    BY <2>1, NatLeReflexive
<1>1. Justified(r, w, sentTime[Prevote(c, r, w)])
  BY <1>t DEF PrevoteJustified
<1>2. PICK p1 \in Message :
        /\ p1 \in sent
        /\ p1.type = "Proposal" /\ p1.sender = Proposer[r] /\ p1.round = r
        /\ p1.value = w
  BY <1>1 DEF Justified
<1>3. PICK p2 \in Message :
        /\ p2 \in sent
        /\ p2.type = "Proposal" /\ p2.sender = Proposer[r] /\ p2.round = r
        /\ p2.value = v
  BY DEF Justified
<1>4. /\ p1 = Proposal(p1.sender, p1.round, p1.value, p1.validRound)
      /\ p1.validRound \in Rounds \cup {-1}
      /\ p2 = Proposal(p2.sender, p2.round, p2.value, p2.validRound)
      /\ p2.validRound \in Rounds \cup {-1}
  BY <1>2, <1>3, ProposalRecordRebuild DEF sent
<1> QED
  BY <1>2, <1>3, <1>4 DEF HonestProposalUnique

\* A correct nil prevote at r, with the round-r proposal in the pool, gives the
\* blocking lock. NilPrevoteInWindow dates the prevote inside the window, and
\* item 11b does the rest. This is the one exit every nil case of the induction
\* takes.
LEMMA NilPrevoteGivesBlocking ==
  ASSUME TypeOK, NilPrevoteInWindow, ~ SomeCorrectDecided,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         RoundOrigin(p, r), Proposer[r] \in Honest,
         NilPrevoteBlocks(p, r),
         Prevote(c, r, nil) \in sent,
         NEW v \in Values, NEW vr \in Rounds \cup {-1},
         Proposal(Proposer[r], r, v, vr) \in sent
  PROVE  BlockingLockDuring(p, r)
<1>1. sentTime[Prevote(c, r, nil)] <= CascadeDeadline(p, r)
  BY DEF NilPrevoteInWindow
<1> QED
  BY <1>1 DEF NilPrevoteBlocks

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 13. CascadeCore, three clauses and one joint induction.            *)
(*                                                                         *)
(*    Clause P is anchored at the justified proposal, clause Q at the      *)
(*    polka. The section "the failure modes, enumerated" of the plan holds *)
(*    the reason. A proposal anchor loses the case where a correct         *)
(*    validator leaves r early. The anchor cannot be raised without a      *)
(*    raise of the deadline of the clause. A polka anchor also gives two   *)
(*    more benefits. PrevoteJustified reads the justification off any      *)
(*    correct member of the polka, so clause Q needs no hypothesis about   *)
(*    the justification. LockWindowCore can also be instantiated there, so *)
(*    its clause 1 excludes a validator below r with no hypothesis about   *)
(*    the ceiling.                                                         *)
(*                                                                         *)
(*  The induction is cyclic. P reads Q above r. Q reads N in step          *)
(*  "precommit". N reads P at the anchor of the prevote timer, and Q reads *)
(*  itself at an earlier anchor. Every cycle passes through a DIFFERENT    *)
(*  anchor and every use is an instance of the PRE-state invariant, so     *)
(*  nothing is circular.                                                   *)
(***************************************************************************)

PrecommitQuorumFor(rr, v) ==
  \E Q \in ByzQuorum : \A s \in Q : Precommit(s, rr, v) \in sent

\* Two of the three disjuncts ARE the outcome of the theorem, and the third is
\* one QuorumDecides stage from it, so an escape costs nothing. Every case where
\* a correct validator has left r exits this way.
CascadeEscape(p, r, v) ==
  \/ SomeCorrectDecided
  \/ BlockingLockDuring(p, r)
  \/ PrecommitQuorumFor(r, v)

CascadeCore(p, r) ==
  \A c \in Honest, v \in Values, T \in Nat :
\*  (P) the prevote clause. CascadeCeiling(p, r) <= T + Delta is what excludes
\*  a straggler that is still at r - 1. A consumer with a lower anchor weakens
\*  Justified upwards.
    /\ (  ( /\ T >= GST
            /\ enteredAt[p][r] <= T
            /\ CascadeCeiling(p, r) <= T + Delta
            /\ Valid(v)
            /\ Justified(r, v, T)
            /\ now > T + Delta )
          => \/ (  Prevote(c, r, v) \in sent
                   /\ sentTime[Prevote(c, r, v)] <= T + Delta  )
             \/ CascadeEscape(p, r, v)  )
\* (N) no correct nil precommit at r.
    /\ (  ( /\ T >= GST
            /\ enteredAt[p][r] <= T
            /\ Valid(v)
            /\ Justified(r, v, T) )
          => \/ Precommit(c, r, nil) \notin sent
             \/ CascadeEscape(p, r, v)  )
\* (Q) the precommit clause, anchored at the polka.
    /\ (  ( /\ T >= GST
            /\ Valid(v)
            /\ PolkaDated(r, v, T)
            /\ now > T + Delta )
          => \/ Precommit(c, r, v) \in sent
             \/ CascadeEscape(p, r, v)  )

\*  Each disjunct of the escape is monotone. A decision is permanent. The
\*  blocking lock is a witness in the pool with a frozen timestamp, and a
\*  quorum only grows.
LEMMA CascadeEscapeMove ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
         RoundOrigin(p, r), CascadeEscape(p, r, v)
  PROVE  CascadeEscape(p, r, v)'
<1>1. CASE SomeCorrectDecided
  BY <1>1, DecidedLatchStep DEF CascadeEscape
<1>2. CASE BlockingLockDuring(p, r)
  <2>1. enteredAt'[p][r] = enteredAt[p][r]
    BY EnteredAtFrozenStep DEF RoundOrigin
  <2>2. BlockingLockDuring(p, r)'
    BY <1>2, <2>1, BlockingLockMove
  <2> QED
    BY <2>2 DEF CascadeEscape
<1>3. CASE PrecommitQuorumFor(r, v)
  BY <1>3, SentMonotoneStep DEFS CascadeEscape, PrecommitQuorumFor
<1> QED
  BY <1>1, <1>2, <1>3 DEF CascadeEscape

\* Justified carries a proposal RECORD. Several leaves need it in constructor
\* form, and NilPrevoteGivesBlocking takes it as an argument.
LEMMA JustifiedGivesProposal ==
  ASSUME TypeOK, NEW rr \in Rounds, NEW v \in Values, NEW T,
         Justified(rr, v, T)
  PROVE  \E vr \in Rounds \cup {-1} :
           /\ Proposal(Proposer[rr], rr, v, vr) \in sent
           /\ sentTime[Proposal(Proposer[rr], rr, v, vr)] <= T
<1>1. PICK prop \in Message :
        /\ prop \in sent
        /\ sentTime[prop] <= T
        /\ prop.type = "Proposal"
        /\ prop.sender = Proposer[rr]
        /\ prop.round = rr
        /\ prop.value = v
  BY DEF Justified
<1>2. /\ prop.validRound \in Rounds \cup {-1}
      /\ prop = Proposal(prop.sender, prop.round, prop.value, prop.validRound)
  BY <1>1, ProposalRecordRebuild DEF sent
<1> QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
(***************************************************************************)
(* Item 13c. The joint induction of CascadeCore.                           *)
(*                                                                         *)
(*  Every leaf reads the PRE-state invariant at an anchor that the state   *)
(*  carries. The cycle "P reads Q above r, Q reads N in step precommit, N  *)
(*  reads P at the arming instant" is therefore not circular. Each read is *)
(*  an instance of the hypothesis of the step, at a different anchor.      *)
(*                                                                         *)
(*  Only a Tick can break clause P or clause Q. A fresh message that first *)
(*  makes Justified or PolkaDated true is dated at or below the clock.     *)
(*  Both clauses need the clock a whole Delta above the date. The fresh    *)
(*  case is therefore arithmetic. Clause N carries no clock guard, so it   *)
(*  takes the three emitters of a nil precommit one at a time.             *)
(***************************************************************************)

\* A Byzantine quorum holds a correct member, so a dated certificate reports
\* one correct sender at the date of the certificate.
LEMMA PolkaHasHonest ==
  ASSUME NEW rr, NEW vv, NEW T, PolkaDated(rr, vv, T)
  PROVE  \E y \in Honest : /\ Prevote(y, rr, vv) \in sent
                           /\ sentTime[Prevote(y, rr, vv)] <= T
BY ByzHasHonest DEF PolkaDated

LEMMA AnyPrevoteHasHonest ==
  ASSUME NEW rr, NEW T, AnyPrevoteDated(rr, T)
  PROVE  \E y \in Honest, w \in ValuesOrNil :
           /\ Prevote(y, rr, w) \in sent
           /\ sentTime[Prevote(y, rr, w)] <= T
BY ByzHasHonest DEF AnyPrevoteDated

-----------------------------------------------------------------------------
\* Arithmetic in a minimal context. Every fact below sits in a top-level
\* constant-only lemma, so no leaf gives z3 a quantified invariant to search.

LEMMA SubAddCancel ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW n \in Int, a <= n
  PROVE  n >= (a - b) + b
BY SMT

LEMMA NatFromChain ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c1 \in Int, NEW e \in Nat,
         a >= b, b >= c1, c1 >= e
  PROVE  a \in Nat /\ a >= e
BY SMT

\* The step from one gossip delay to two, for the composed reading below.
LEMMA DeltaStepOrder ==
  ASSUME NEW t \in Nat, NEW d \in Nat, NEW g \in Nat, NEW n \in Nat,
         d > 1, t >= g, n > t + 2 * d
  PROVE  /\ t + d \in Nat
         /\ t + d >= g
         /\ n > t + d
         /\ (t + d) + d = t + 2 * d
BY SMT

\* The anchor of the first-to-leave argument, a whole precommit timeout below
\* the clock. The entry of the leaver is what makes it post-GST.
LEMMA AboveAnchorOrder ==
  ASSUME NEW n \in Nat, NEW k \in Nat, NEW e \in Nat, NEW g \in Nat,
         NEW d \in Nat, NEW s \in Int, NEW eh \in Int,
         d > 1, k > 2 * d, s <= n - k, s >= eh, eh >= e, e > g
  PROVE  /\ n - k \in Nat
         /\ n - k >= g
         /\ n > (n - k) + d
BY SMT

\* The clock, carried above the deadline by the propose margin.
LEMMA GeThroughMargin ==
  ASSUME NEW n \in Int, NEW s \in Int, NEW eh \in Int, NEW e \in Int,
         NEW tp \in Int, NEW d \in Int, NEW k \in Int,
         n >= s, s >= eh + tp, eh >= e, tp > 2 * d + k
  PROVE  n >= e + 2 * d + k
BY SMT

\* The anchor of mode 2, and the one place the prevote margin is spent. The
\* anchor is the later of the arming instant and the entry spread. It therefore
\* clears the ceiling by a gossip delay, and the fired prevote timer is two
\* gossip delays above it. One lemma per case: a conclusion that names a free
\* anchor gives the backend a term to invent, and it does not find it.
LEMMA PrevoteAnchorAtArming ==
  ASSUME NEW e \in Nat, NEW k \in Nat, NEW d \in Nat, NEW g \in Nat,
         NEW q \in Int, NEW tv \in Int, NEW n \in Nat,
         d > 1, e > g, q >= e, tv > 2 * d + k, n >= q + tv, q >= e + k
  PROVE  /\ q >= g
         /\ e <= q
         /\ e + d + k <= q + d
         /\ n > q + 2 * d
<1>1. q >= g
  BY SMT
<1>2. e <= q
  OBVIOUS
<1>3. e + d + k <= q + d
  BY SMT
<1>4. n > q + 2 * d
  BY SMT
<1> QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA PrevotePastTwoDeltas ==
  ASSUME NEW n \in Nat, NEW q \in Nat, NEW tv \in Int,
         NEW d \in Nat, NEW k \in Nat,
         n >= q + tv, tv > 2 * d + k
  PROVE n > q + 2 * d
BY SMT

LEMMA PrevoteAnchorAtSpread ==
  ASSUME NEW e \in Nat, NEW k \in Nat, NEW d \in Nat, NEW g \in Nat,
         NEW q \in Int, NEW tv \in Int, NEW n \in Nat,
         d > 1, e > g, q >= e, tv > 2 * d + k, n >= q + tv, ~ (q >= e + k)
  PROVE  /\ e + k \in Nat
         /\ e + k >= g
         /\ e <= e + k
         /\ q <= e + k
         /\ e + d + k <= (e + k) + d
         /\ n > (e + k) + 2 * d
<1>1. e + k \in Nat
  OBVIOUS
<1>2. e + k >= g
  BY SMT
<1>3. e <= e + k
  OBVIOUS
<1>4. q <= e + k
  BY SMT
<1>5. e + d + k <= (e + k) + d
  BY SMT
<1>6. n > (e + k) + 2 * d
  BY SMT
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

-----------------------------------------------------------------------------
\*  Two readings of the pre-state invariant. The escape does not mention the
\*  validator, so the case split on it stands outside the quantifier. The
\*  correct set is a Byzantine quorum, so the readings for each validator
\*  assemble.

LEMMA CoreGivesPolka ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
         NEW T \in Nat, CascadeCore(p, r),
         T >= GST, enteredAt[p][r] <= T, CascadeCeiling(p, r) <= T + Delta,
         Valid(v), Justified(r, v, T), now > T + Delta
  PROVE  PolkaDated(r, v, T + Delta) \/ CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  PolkaDated(r, v, T + Delta)
  OBVIOUS
<1>1. ASSUME NEW y \in Honest
      PROVE  /\ Prevote(y, r, v) \in sent
             /\ sentTime[Prevote(y, r, v)] <= T + Delta
  BY DEF CascadeCore
<1> QED
  BY <1>1, AllHonestGivesPolka DEF ValuesOrNil

LEMMA CoreGivesQuorum ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
         NEW T \in Nat, CascadeCore(p, r),
         T >= GST, Valid(v), PolkaDated(r, v, T), now > T + Delta
  PROVE  CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  FALSE
  OBVIOUS
<1>1. ASSUME NEW y \in Honest
      PROVE  Precommit(y, r, v) \in sent
  BY DEF CascadeCore
<1> QED
  BY <1>1, AllHonestGivesPrecommitQuorum
  DEFS CascadeEscape, PrecommitQuorumFor

\*  The two readings composed. A justified anchor with two gossip delays of
\*  slack gives the escape outright. Mode 2 and mode 3 both rest on this
\*  lemma.
LEMMA CoreJustifiedGivesEscape ==
  ASSUME TypeOK, NEW p \in Honest, NEW r \in Rounds, NEW v \in Values,
         NEW T \in Nat, CascadeCore(p, r),
         T >= GST, enteredAt[p][r] <= T, CascadeCeiling(p, r) <= T + Delta,
         Valid(v), Justified(r, v, T), now > T + 2 * Delta
  PROVE  CascadeEscape(p, r, v)
<1>n. now \in Nat
  BY DEF TypeOK
<1>ty. /\ T + Delta \in Nat
       /\ T + Delta >= GST
       /\ now > T + Delta
       /\ (T + Delta) + Delta = T + 2 * Delta
  BY <1>n, DeltaType, GSTType, DeltaStepOrder
<1>1. PolkaDated(r, v, T + Delta) \/ CascadeEscape(p, r, v)
  BY <1>ty, CoreGivesPolka
<1>2. CASE PolkaDated(r, v, T + Delta)
  BY <1>2, <1>ty, CoreGivesQuorum
<1> QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
\* Row 9 of the fact map, the first-to-leave argument. A correct validator
\* above r precommitted at r a whole TimeoutPrecommit(r) ago. Clause N makes
\* that precommit a value precommit, PrecommitBacked dates the polka behind it
\* that early, and clause Q at that anchor gives the quorum. No minimum over
\* the leavers is needed: the evidence of one leaver closes the case.
LEMMA AboveGivesEscape ==
  ASSUME TypeOK, SentTimeLeNow, EnteredAtLeNow, EnteredCurrentRound,
         CrossingBacked, PrecommitBacked, PrevoteJustified, PrevoteOncePerRound,
         HonestProposalUnique, RoundVoteAfterEntry,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest, NEW v \in Values,
         NEW T \in Nat, RoundOrigin(p, r), WRDurable(r), CascadeCore(p, r),
         T >= GST, enteredAt[p][r] <= T, Valid(v), Justified(r, v, T),
         round[c] > r
  PROVE  CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  FALSE
  OBVIOUS
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
       /\ TimeoutPrecommit(r) \in Nat /\ TimeoutPrecommit(r) > 2 * Delta
  <2>1. TimeoutPrecommit(r) \in Nat
    BY T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit
  <2>2. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
    BY GSTType DEFS OFF, RoundOrigin, TypeOK
  <2> QED
    BY <2>1, <2>2, DeltaType, GSTType DEFS TypeOK, WRDurable
<1>1. PICK h \in Honest, w \in ValuesOrNil :
        /\ Precommit(h, r, w) \in sent
        /\ sentTime[Precommit(h, r, w)] <= now - TimeoutPrecommit(r)
  BY AboveNeedsCorrectPrecommit
<1>2. w \in Values
  <2>1. Precommit(h, r, nil) \notin sent
    BY DEF CascadeCore
  <2> QED
    BY <1>1, <2>1 DEF ValuesOrNil
\* The entry of h is at or after the entry of p, so the anchor is post-GST.
<1>3. /\ enteredAt[h][r] # OFF
      /\ sentTime[Precommit(h, r, w)] >= enteredAt[h][r]
  BY <1>1 DEF RoundVoteAfterEntry
<1>4. /\ enteredAt[h][r] \in Int
      /\ enteredAt[h][r] >= enteredAt[p][r]
  BY <1>3 DEFS EntriesAtOrAfter, OFF, RoundOrigin, TypeOK
<1>m. Precommit(h, r, w) \in Message
  BY <1>1, HonestSubValidators, MsgPrecommit
<1>s. sentTime[Precommit(h, r, w)] \in Int
  BY <1>1, <1>m DEFS OFF, sent, TypeOK
<1>5. /\ now - TimeoutPrecommit(r) \in Nat
      /\ now - TimeoutPrecommit(r) >= GST
      /\ now > (now - TimeoutPrecommit(r)) + Delta
  BY <1>1, <1>3, <1>4, <1>s, <1>ty, AboveAnchorOrder
<1>6. Backing(r, w, now - TimeoutPrecommit(r))
  BY <1>1, <1>5 DEF PrecommitBacked
<1>7. PolkaDated(r, w, now - TimeoutPrecommit(r))
  BY <1>2, <1>6, NilNotInValues DEF Backing
<1>8. w = v
  <2>1. PICK y \in Honest : Prevote(y, r, w) \in sent
    BY <1>7, PolkaHasHonest
  <2> QED
    BY <1>2, <1>q, <2>1, UniqueValuePrevote
<1> QED
  BY <1>5, <1>7, <1>8, CoreGivesQuorum

-----------------------------------------------------------------------------
\* Fact (*) of the paper, read at one correct sender. A correct nil precommit
\* at rr needs a nil polka, or an any-value prevote quorum a whole
\* TimeoutPrevote(rr) before the precommit.
LEMMA NilPrecommitBacking ==
  ASSUME TypeOK, SentTimeLeNow, PrecommitBacked,
         NEW rr \in Rounds, NEW c \in Honest, Precommit(c, rr, nil) \in sent
  PROVE  \/ \E y \in Honest : Prevote(y, rr, nil) \in sent
         \/ \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
              /\ Prevote(y, rr, w) \in sent
              /\ sentTime[Prevote(y, rr, w)] <= Tq
              /\ now >= Tq + TimeoutPrevote(rr)
<1>m. Precommit(c, rr, nil) \in Message
  BY HonestSubValidators, MsgPrecommit DEF ValuesOrNil
<1>t. /\ sentTime[Precommit(c, rr, nil)] \in Nat
      /\ sentTime[Precommit(c, rr, nil)] <= now
      /\ sentTime[Precommit(c, rr, nil)] <= sentTime[Precommit(c, rr, nil)]
  <2>1. /\ sentTime[Precommit(c, rr, nil)] \in Nat
        /\ sentTime[Precommit(c, rr, nil)] <= now
    BY <1>m DEFS OFF, sent, SentTimeLeNow, TypeOK
  <2> QED
    BY <2>1, NatLeReflexive
<1>1. Backing(rr, nil, sentTime[Precommit(c, rr, nil)])
  BY <1>t DEFS PrecommitBacked, ValuesOrNil
<1>2. CASE PolkaDated(rr, nil, sentTime[Precommit(c, rr, nil)])
  BY <1>2, PolkaHasHonest
<1>3. CASE AnyPrevoteDated(rr, sentTime[Precommit(c, rr, nil)] - TimeoutPrevote(rr))
  <2>ty. /\ TimeoutPrevote(rr) \in Int
         /\ sentTime[Precommit(c, rr, nil)] - TimeoutPrevote(rr) \in Int
    BY <1>t, T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
  <2>1. PICK y \in Honest, w \in ValuesOrNil :
          /\ Prevote(y, rr, w) \in sent
          /\ sentTime[Prevote(y, rr, w)]
               <= sentTime[Precommit(c, rr, nil)] - TimeoutPrevote(rr)
    BY <1>3, AnyPrevoteHasHonest
  <2>2. now >= (sentTime[Precommit(c, rr, nil)] - TimeoutPrevote(rr))
                 + TimeoutPrevote(rr)
    BY <1>t, <2>ty, SubAddCancel
  <2> QED
    BY <2>1, <2>2, <2>ty
<1> QED
  BY <1>1, <1>2, <1>3, NilNotInValues DEF Backing

-----------------------------------------------------------------------------
\*  A correct prevote at r puts the round-r proposal in the pool. Either the
\*  prevote read the proposal, or it came from the propose timeout. In the
\*  second case the propose margin puts the clock above the ceiling, and
\*  ProposalDated reports the proposal of an honest proposer there.
LEMMA ProposalFromCorrectPrevote ==
  ASSUME TypeOK, SentTimeLeNow, PrevoteNeedsProposalOrTimeout, ProposalDated,
         NEW p \in Honest, NEW r \in Rounds, NEW y \in Honest,
         NEW w \in ValuesOrNil,
         RoundOrigin(p, r), WRDurable(r), ~ SomeCorrectDecided,
         Prevote(y, r, w) \in sent
  PROVE  \E v2 \in Values, vr2 \in Rounds \cup {-1} :
           Proposal(Proposer[r], r, v2, vr2) \in sent
<1>m. Prevote(y, r, w) \in Message
  BY HonestSubValidators, MsgPrevote
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
       /\ TimeoutPropose(r) \in Int /\ TimeoutPrecommit(r - 1) \in Nat
       /\ TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
       /\ sentTime[Prevote(y, r, w)] \in Int
       /\ now >= sentTime[Prevote(y, r, w)]
  <2>0. r > 0
    BY DEF RoundOrigin
  <2>1. TimeoutPropose(r) \in Int /\ TimeoutPrecommit(r - 1) \in Nat
    BY <2>0, RoundTypes
  <2>2. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
    BY GSTType DEFS OFF, RoundOrigin, TypeOK
  <2>3. /\ sentTime[Prevote(y, r, w)] \in Int
        /\ now >= sentTime[Prevote(y, r, w)]
    BY <1>m DEFS OFF, sent, SentTimeLeNow, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType, GSTType DEFS TypeOK, WRDurable
<1>1. /\ enteredAt[y][r] # OFF
      /\ \/ \E mm \in sent : /\ mm.type = "Proposal"
                             /\ mm.round = r
                             /\ mm.sender = Proposer[r]
                             /\ sentTime[mm] <= sentTime[Prevote(y, r, w)]
         \/ sentTime[Prevote(y, r, w)] >= enteredAt[y][r] + TimeoutPropose(r)
  BY DEF PrevoteNeedsProposalOrTimeout
<1>2. CASE \E mm \in sent : /\ mm.type = "Proposal"
                            /\ mm.round = r
                            /\ mm.sender = Proposer[r]
                            /\ sentTime[mm] <= sentTime[Prevote(y, r, w)]
  <2>1. PICK mm \in sent : /\ mm.type = "Proposal"
                           /\ mm.round = r
                           /\ mm.sender = Proposer[r]
    BY <1>2
  <2>2. /\ mm.value \in Values
        /\ mm.validRound \in Rounds \cup {-1}
        /\ mm = Proposal(mm.sender, mm.round, mm.value, mm.validRound)
    BY <2>1, ProposalRecordRebuild DEF sent
  <2> QED
    BY <2>1, <2>2
<1>3. CASE sentTime[Prevote(y, r, w)] >= enteredAt[y][r] + TimeoutPropose(r)
  <2>e. enteredAt[y][r] \in Int /\ enteredAt[y][r] >= enteredAt[p][r]
    BY <1>1 DEFS EntriesAtOrAfter, OFF, RoundOrigin, TypeOK
  <2>1. now >= enteredAt[p][r] + 2 * Delta + TimeoutPrecommit(r - 1)
    BY <1>3, <1>ty, <2>e, GeThroughMargin
  <2>2. now > CascadeCeiling(p, r)
    BY <1>ty, <2>1, DeadlineAboveCeiling DEF CascadeCeiling
  <2> QED
    BY <2>2 DEFS ProposalDated, WRDurable
<1> QED
  BY <1>1, <1>2, <1>3

\*  The round-r proposal for v, read in the PRE-state. In a case with a fresh
\*  message, the justification is one step ahead of the pool.
\*  HonestProposalUnique at the PRIMED state is therefore what identifies the
\*  value of the proposal in the pool with v.
LEMMA PreStateProposalForValue ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, [Next]_vars,
         PrevoteNeedsProposalOrTimeout, ProposalDated, HonestProposalUnique',
         NEW p \in Honest, NEW r \in Rounds, NEW y \in Honest,
         NEW w \in ValuesOrNil, NEW v \in Values, NEW T,
         RoundOrigin(p, r), WRDurable(r), ~ SomeCorrectDecided,
         Prevote(y, r, w) \in sent, Justified(r, v, T)'
  PROVE  \E vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr2) \in sent
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>1. PICK v2 \in Values, vr2 \in Rounds \cup {-1} :
        Proposal(Proposer[r], r, v2, vr2) \in sent
  BY ProposalFromCorrectPrevote
<1>2. PICK prop \in Message :
        /\ prop \in sent'
        /\ prop.type = "Proposal"
        /\ prop.sender = Proposer[r]
        /\ prop.round = r
        /\ prop.value = v
  BY DEF Justified
<1>3. /\ prop.validRound \in Rounds \cup {-1}
      /\ prop = Proposal(Proposer[r], r, v, prop.validRound)
  BY <1>2, ProposalRecordRebuild
<1>4. Proposal(Proposer[r], r, v2, vr2) \in sent'
  BY <1>1, SentMonotoneStep
<1>5. v2 = v
  BY <1>1, <1>2, <1>3, <1>4, <1>q DEF HonestProposalUnique
<1> QED
  BY <1>1, <1>5

\* A correct prevote for a VALUE at r carries the value of the round-r
\* proposal. The twin of UniqueValuePrevote, taking the proposal itself rather
\* than a justification, because the caller's justification may be one step
\* fresher than the pool.
LEMMA PrevoteValueIsProposed ==
  ASSUME TypeOK, SentTimeLeNow, PrevoteJustified, HonestProposalUnique,
         NEW r \in Rounds, NEW y \in Honest, NEW w \in Values,
         NEW v \in Values, NEW vr \in Rounds \cup {-1}, Proposer[r] \in Honest,
         Proposal(Proposer[r], r, v, vr) \in sent, Prevote(y, r, w) \in sent
  PROVE  w = v
<1>m. Prevote(y, r, w) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1>t. /\ sentTime[Prevote(y, r, w)] \in Nat
      /\ sentTime[Prevote(y, r, w)] <= sentTime[Prevote(y, r, w)]
  <2>1. sentTime[Prevote(y, r, w)] \in Nat
    BY <1>m DEFS OFF, sent, SentTimeLeNow, TypeOK
  <2> QED
    BY <2>1, NatLeReflexive
<1>1. Justified(r, w, sentTime[Prevote(y, r, w)])
  BY <1>t DEF PrevoteJustified
<1>2. PICK vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, w, vr2) \in sent
  BY <1>1, JustifiedGivesProposal
<1> QED
  BY <1>2 DEF HonestProposalUnique

-----------------------------------------------------------------------------
\*  Mode 2's core. A dated any-value prevote quorum at r, whose date is a
\*  whole TimeoutPrevote(r) below the clock, gives the escape. A correct
\*  member of the quorum either prevoted nil, which gives the lock, or its
\*  prevote justifies the proposal at the anchor. In the second case clause P
\*  builds the polka there.
LEMMA ArmingQuorumGivesEscape ==
  ASSUME TypeOK, SentTimeLeNow, PrevoteJustified, PrevoteOncePerRound,
         HonestProposalUnique, NilPrevoteInWindow, RoundVoteAfterEntry,
         NEW p \in Honest, NEW r \in Rounds, NEW v \in Values, NEW vr \in Rounds \cup {-1},
         NEW Tq \in Int, NEW y \in Honest, NEW w \in ValuesOrNil,
         RoundOrigin(p, r), WRDurable(r), NilPrevoteBlocks(p, r),
         CascadeCore(p, r), Valid(v),
         Proposal(Proposer[r], r, v, vr) \in sent,
         Prevote(y, r, w) \in sent, sentTime[Prevote(y, r, w)] <= Tq,
         now >= Tq + TimeoutPrevote(r)
  PROVE  CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  FALSE
  OBVIOUS
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
  BY DEF CascadeEscape
<1>1. w \in Values
  <2>1. Prevote(y, r, nil) \notin sent
    BY <1>nd, <1>q, NilPrevoteGivesBlocking
  <2> QED
    BY <2>1 DEF ValuesOrNil
<1>2. w = v
  BY <1>1, <1>q, PrevoteValueIsProposed
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
       /\ TimeoutPrevote(r) \in Int /\ TimeoutPrecommit(r - 1) \in Nat
       /\ TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
       /\ sentTime[Prevote(y, r, w)] \in Int
  <2>0. r > 0
    BY DEF RoundOrigin
  <2>1. TimeoutPrevote(r) \in Int /\ TimeoutPrecommit(r - 1) \in Nat
    BY <2>0, RoundTypes, T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
  <2>2. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
    BY GSTType DEFS OFF, RoundOrigin, TypeOK
  <2>m. Prevote(y, r, w) \in Message
    BY HonestSubValidators, MsgPrevote
  <2>3. sentTime[Prevote(y, r, w)] \in Int
    BY <2>m DEFS OFF, sent, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, DeltaType, GSTType DEFS TypeOK, WRDurable
<1>3. /\ enteredAt[y][r] # OFF
      /\ sentTime[Prevote(y, r, w)] >= enteredAt[y][r]
  BY DEF RoundVoteAfterEntry
<1>4. /\ enteredAt[y][r] \in Int
      /\ enteredAt[y][r] >= enteredAt[p][r]
  BY <1>3 DEFS EntriesAtOrAfter, OFF, RoundOrigin, TypeOK
<1>5. /\ Tq \in Nat
      /\ Tq >= enteredAt[p][r]
  BY <1>3, <1>4, <1>ty, NatFromChain
<1>6. Justified(r, v, Tq)
  BY <1>2, <1>5, <1>ty DEF PrevoteJustified
\* The anchor is the later of the arming instant and the entry spread.
<1>7. CASE Tq >= CascadeAnchor(p, r)
  <2>1. Tq >= enteredAt[p][r] + TimeoutPrecommit(r - 1)
    BY <1>7 DEF CascadeAnchor
  <2>2. /\ Tq >= GST
        /\ enteredAt[p][r] <= Tq
        /\ CascadeCeiling(p, r) <= Tq + Delta
        /\ now > Tq + 2 * Delta
    <3>1. Tq >= GST
      BY <1>5, <1>ty, <2>1, PrevoteAnchorAtArming
    <3>2. enteredAt[p][r] <= Tq
      BY <1>5, <1>ty, <2>1, PrevoteAnchorAtArming
    <3>3. CascadeCeiling(p, r) <= Tq + Delta
      BY <1>5, <1>ty, <2>1, PrevoteAnchorAtArming DEF CascadeCeiling
    <3>4. now > Tq + 2 * Delta
      BY <1>5, <1>ty, PrevotePastTwoDeltas
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2> QED
    BY <1>5, <1>6, <2>2, CoreJustifiedGivesEscape
<1>8. CASE ~ (Tq >= CascadeAnchor(p, r))
  <2>1. ~ (Tq >= enteredAt[p][r] + TimeoutPrecommit(r - 1))
    BY <1>8 DEF CascadeAnchor
  <2>2. /\ CascadeAnchor(p, r) \in Nat
        /\ CascadeAnchor(p, r) >= GST
        /\ enteredAt[p][r] <= CascadeAnchor(p, r)
        /\ Tq <= CascadeAnchor(p, r)
        /\ CascadeCeiling(p, r) <= CascadeAnchor(p, r) + Delta
        /\ now > CascadeAnchor(p, r) + 2 * Delta
    BY <1>5, <1>ty, <2>1, PrevoteAnchorAtSpread
    DEFS CascadeAnchor, CascadeCeiling
  <2>3. Justified(r, v, CascadeAnchor(p, r))
    BY <1>5, <1>6, <2>2, JustifiedWeaken
  <2> QED
    BY <2>2, <2>3, CoreJustifiedGivesEscape
<1> QED
  BY <1>7, <1>8

\* Clause N's content, as a state lemma. A correct nil precommit at r, with the
\* round-r proposal for v in the pool, gives the escape. It covers a precommit
\* of any age, so the induction reads it for an old precommit and for a fresh
\* one from OnPrevoteQuorumNil alike.
LEMMA NilPrecommitGivesEscape ==
  ASSUME TypeOK, SentTimeLeNow, PrecommitBacked, PrevoteJustified,
         PrevoteOncePerRound, HonestProposalUnique, NilPrevoteInWindow,
         RoundVoteAfterEntry,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest,
         NEW v \in Values, NEW vr \in Rounds \cup {-1},
         RoundOrigin(p, r), WRDurable(r), NilPrevoteBlocks(p, r),
         CascadeCore(p, r), Valid(v),
         Proposal(Proposer[r], r, v, vr) \in sent,
         Precommit(c, r, nil) \in sent
  PROVE  CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  FALSE
  OBVIOUS
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
  BY DEF CascadeEscape
<1>1. \/ \E y \in Honest : Prevote(y, r, nil) \in sent
      \/ \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
           /\ Prevote(y, r, w) \in sent
           /\ sentTime[Prevote(y, r, w)] <= Tq
           /\ now >= Tq + TimeoutPrevote(r)
  BY NilPrecommitBacking
<1>2. CASE \E y \in Honest : Prevote(y, r, nil) \in sent
  BY <1>2, <1>nd, <1>q, NilPrevoteGivesBlocking
<1>3. CASE \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
             /\ Prevote(y, r, w) \in sent
             /\ sentTime[Prevote(y, r, w)] <= Tq
             /\ now >= Tq + TimeoutPrevote(r)
  BY <1>3, ArmingQuorumGivesEscape
<1> QED
  BY <1>1, <1>2, <1>3

-----------------------------------------------------------------------------
\* The two Tick cases. A Tick freezes the pool, and its maximal-progress guard
\* says that no correct validator can compute, so both lemmas run entirely in
\* the pre-state. Their conclusions name sent and sentTime only, so the step
\* lemma carries them across the Tick by monotonicity alone.

\* Clause P at the one instant the clock can break it. Five positions of a
\* correct validator, and each one gives the prevote, gives the escape, or
\* contradicts the quiet clock.
LEMMA PrevoteAtQuietClock ==
  ASSUME TypeOK, SentTimeLeNow, RcvdSubsetSent, GossipDeadline, EntryWindowCore,
         CrossingBacked, EnteredAtLeNow, EnteredCurrentRound, PrecommitBacked,
         PrevoteJustified, PrevoteOncePerRound, HonestProposalUnique,
         NilPrevoteInWindow, RoundVoteAfterEntry, StepPastProposeHasPrevote,
         DecidedStepOp,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest, NEW v \in Values,
         NEW T \in Nat, RoundOrigin(p, r), WRDurable(r), NilPrevoteBlocks(p, r),
         CascadeCore(p, r), ~ \E x \in Honest : CanCompute(x), now = T + Delta,
         T >= GST, enteredAt[p][r] <= T, CascadeCeiling(p, r) <= T + Delta,
         Valid(v), Justified(r, v, T)
  PROVE  \/ /\ Prevote(c, r, v) \in sent
            /\ sentTime[Prevote(c, r, v)] <= T + Delta
         \/ CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  /\ Prevote(c, r, v) \in sent
                    /\ sentTime[Prevote(c, r, v)] <= T + Delta
  OBVIOUS
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
  BY DEF CascadeEscape
<1>nc. ~ CanCompute(c)
  OBVIOUS
<1>prop. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  BY JustifiedGivesProposal
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ round[c] \in Nat /\ r \in Nat /\ T \in Nat
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
       /\ TimeoutPrecommit(r - 1) \in Nat /\ r > 0
  <2>1. enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST /\ r > 0
    BY GSTType DEFS OFF, RoundOrigin, TypeOK
  <2>2. TimeoutPrecommit(r - 1) \in Nat
    BY <2>1, RoundTypes
  <2> QED
    BY <2>1, <2>2, DeltaType, GSTType DEFS Rounds, TypeOK
<1>sd. step[c] # "decided"
  BY <1>nd, DecidedStepOp DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
\*  Below r. The entry certificate of p reaches every correct validator by the
\*  ceiling, and SkipRound is available there. The clock can therefore not be
\*  AT the ceiling with a validator still below r.
<1>1. ~ (round[c] < r)
  <2> SUFFICES ASSUME round[c] < r
               PROVE  FALSE
    OBVIOUS
  <2>1. AnyPrecommitDated(r - 1, enteredAt[p][r])
    BY EntryCertificateDated DEFS OFF, RoundOrigin
  <2>2. now >= enteredAt[p][r] + Delta + TimeoutPrecommit(r - 1)
    BY <1>ty DEF CascadeCeiling
  <2>3. r - 1 \in Rounds
    BY <1>ty DEF Rounds
  <2>4. round[c] > r - 1
    BY <1>nc, <1>sd, <1>ty, <2>1, <2>2, <2>3, EntryReachedAtCeiling
  <2> QED
    BY <1>ty, <2>4, RoundBelowAndAbovePred
<1>2. ~ (round[c] > r)
  BY <1>nd, AboveGivesEscape DEF CascadeEscape
<1>3. round[c] = r
  BY <1>1, <1>2, <1>ty
\* At r in step "propose": the delivered justification is a computation step.
<1>4. step[c] # "propose"
  BY <1>3, <1>nc, <1>ty, ProposeExitEnabled
<1>5. step[c] \in {"prevote", "precommit"}
  BY <1>4, <1>sd, HonestSubValidators DEFS Step, TypeOK
<1>6. PICK w \in ValuesOrNil : Prevote(c, r, w) \in sent
  BY <1>3, <1>5 DEF StepPastProposeHasPrevote
<1>7. w \in Values
  <2>1. Prevote(c, r, nil) \notin sent
    BY <1>nd, <1>prop, <1>q, NilPrevoteGivesBlocking
  <2> QED
    BY <1>6, <2>1 DEF ValuesOrNil
<1>8. w = v
  BY <1>6, <1>7, <1>prop, <1>q, PrevoteValueIsProposed
<1>m. Prevote(c, r, v) \in Message
  BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
<1> QED
  BY <1>6, <1>8, <1>m, <1>ty DEFS OFF, sent, SentTimeLeNow, TypeOK

\* Clause Q at the one instant the clock can break it. The polka supplies its
\* own justification and its own any-value quorum, so the validator below r is
\* excluded by SkipRound instead of by the ceiling.
LEMMA PrecommitAtQuietClock ==
  ASSUME TypeOK, SentTimeLeNow, RcvdSubsetSent, GossipDeadline, EnteredAtLeNow,
         EnteredCurrentRound, CrossingBacked, PrecommitBacked, PrevoteJustified,
         PrevoteOncePerRound, HonestProposalUnique, NilPrevoteInWindow,
         RoundVoteAfterEntry, StepPrecommitHasPrecommit, DecidedStepOp,
         NEW p \in Honest, NEW r \in Rounds, NEW c \in Honest, NEW v \in Values,
         NEW T \in Nat, RoundOrigin(p, r), WRDurable(r), NilPrevoteBlocks(p, r),
         CascadeCore(p, r), ~ \E x \in Honest : CanCompute(x), now = T + Delta,
         T >= GST, Valid(v), PolkaDated(r, v, T)
  PROVE  Precommit(c, r, v) \in sent \/ CascadeEscape(p, r, v)
<1> SUFFICES ASSUME ~ CascadeEscape(p, r, v)
             PROVE  Precommit(c, r, v) \in sent
  OBVIOUS
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
  BY DEF CascadeEscape
<1>nc. ~ CanCompute(c)
  OBVIOUS
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ round[c] \in Nat /\ r \in Nat /\ T \in Nat
       /\ enteredAt[p][r] \in Nat /\ enteredAt[p][r] > GST
  BY DeltaType, GSTType DEFS OFF, Rounds, RoundOrigin, TypeOK
<1>sd. step[c] # "decided"
  BY <1>nd, DecidedStepOp DEFS DecidedStepOp, HasDecided, SomeCorrectDecided
\*  The polka carries its own any-value quorum and its own justification. It
\*  also carries the entry of one correct member, which is at or after the
\*  entry of p.
<1>any. AnyPrevoteDated(r, T)
  BY PolkaIsAnyPrevote DEF ValuesOrNil
<1>y. PICK y \in Honest : /\ Prevote(y, r, v) \in sent
                         /\ sentTime[Prevote(y, r, v)] <= T
  BY PolkaHasHonest
<1>ju. Justified(r, v, T)
  BY <1>y DEF PrevoteJustified
<1>e. /\ enteredAt[y][r] # OFF
      /\ sentTime[Prevote(y, r, v)] >= enteredAt[y][r]
  BY <1>y DEFS RoundVoteAfterEntry, ValuesOrNil
<1>ent. enteredAt[p][r] <= T
  <2>m. Prevote(y, r, v) \in Message
    BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
  <2>1. /\ sentTime[Prevote(y, r, v)] \in Int
        /\ enteredAt[y][r] \in Int
        /\ enteredAt[y][r] >= enteredAt[p][r]
    BY <1>e, <2>m DEFS EntriesAtOrAfter, OFF, RoundOrigin, sent, TypeOK
  <2> QED
    BY <1>e, <1>y, <1>ty, <2>1, NatFromChain
\* Below r: an any-value quorum a gossip delay old makes SkipRound available.
<1>1. ~ (round[c] < r)
  BY <1>any, <1>nc, <1>sd, <1>ty, SkipEnabledFromQuorum
<1>2. ~ (round[c] > r)
  BY <1>ent, <1>ju, <1>nd, AboveGivesEscape DEF CascadeEscape
<1>3. round[c] = r
  BY <1>1, <1>2, <1>ty
<1>4. step[c] # "propose"
  BY <1>3, <1>ju, <1>nc, <1>ty, ProposeExitEnabled
<1>5. step[c] # "prevote"
  BY <1>3, <1>ju, <1>nc, <1>ty, ValuePrecommitEnabled
<1>6. step[c] = "precommit"
  BY <1>4, <1>5, <1>sd, HonestSubValidators DEFS Step, TypeOK
<1>7. PICK w \in ValuesOrNil : Precommit(c, r, w) \in sent
  BY <1>3, <1>6 DEF StepPrecommitHasPrecommit
<1>8. w \in Values
  <2>1. Precommit(c, r, nil) \notin sent
    BY <1>ent, <1>ju DEF CascadeCore
  <2> QED
    BY <1>7, <2>1 DEF ValuesOrNil
\* The value is v: the precommit is backed by a polka at r, and two polkas at
\* one round agree.
<1>9. w = v
  <2>m. Precommit(c, r, w) \in Message
    BY <1>7, HonestSubValidators, MsgPrecommit
  <2>t. /\ sentTime[Precommit(c, r, w)] \in Nat
        /\ sentTime[Precommit(c, r, w)] <= sentTime[Precommit(c, r, w)]
    <3>1. sentTime[Precommit(c, r, w)] \in Nat
      BY <1>7, <2>m DEFS OFF, sent, TypeOK
    <3> QED
      BY <3>1, NatLeReflexive
  <2>1. Backing(r, w, sentTime[Precommit(c, r, w)])
    BY <1>7, <2>t DEF PrecommitBacked
  <2>2. PolkaDated(r, w, sentTime[Precommit(c, r, w)])
    BY <1>8, <2>1, NilNotInValues DEF Backing
  <2> QED
    BY <1>8, <2>2, TwoPolkasAgree DEF ValuesOrNil
<1> QED
  BY <1>7, <1>9

-----------------------------------------------------------------------------
\*   The entry leg. At the hypothesis state the clock is AT the entry of p.
\*   Clause P and clause Q are therefore vacuous, by arithmetic. Every date
\*   that they admit is at or above the clock. Clause N holds because a nil
\*   precommit at r needs prevote evidence at r, dated a whole prevote timeout
\*   earlier. No round-r vote of a correct validator is before the entry.
LEMMA Lemma5HypGivesCascadeCore ==
  ASSUME TypeOK, SentTimeLeNow, PrecommitBacked, PrevoteOncePerRound,
         PrevoteJustified, HonestProposalUnique, NilPrevoteInWindow,
         RoundVoteAfterEntry,
         NEW p \in Honest, NEW r \in Rounds, Lemma5Hyp(p, r), CaseA(p, r),
         NilPrevoteBlocks(p, r)
  PROVE  CascadeCore(p, r)
<1>dur. RoundOrigin(p, r) /\ WRDurable(r)
  BY Lemma5HypDurable DEF CascadeDurable
<1>q. Proposer[r] \in Honest
  BY DEF Lemma5Hyp
<1>now. now = enteredAt[p][r]
  BY DEFS FirstToEnter, Lemma5Hyp
<1>ty. /\ now \in Nat /\ GST \in Nat /\ Delta \in Nat /\ Delta > 1
       /\ enteredAt[p][r] \in Nat
       /\ TimeoutPrevote(r) \in Nat /\ TimeoutPrevote(r) > 0
  <2>1. TimeoutPrevote(r) \in Nat /\ TimeoutPrevote(r) > 0
    BY T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
  <2> QED
    BY <1>now, <2>1, DeltaType, GSTType DEF TypeOK
<1> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW T \in Nat
             PROVE  /\ (  ( /\ T >= GST
                            /\ enteredAt[p][r] <= T
                            /\ CascadeCeiling(p, r) <= T + Delta
                            /\ Valid(v)
                            /\ Justified(r, v, T)
                            /\ now > T + Delta )
                          => \/ /\ Prevote(c, r, v) \in sent
                                /\ sentTime[Prevote(c, r, v)] <= T + Delta
                             \/ CascadeEscape(p, r, v)  )
                    /\ (  ( /\ T >= GST
                            /\ enteredAt[p][r] <= T
                            /\ Valid(v)
                            /\ Justified(r, v, T) )
                          => \/ Precommit(c, r, nil) \notin sent
                             \/ CascadeEscape(p, r, v)  )
                    /\ (  ( /\ T >= GST
                            /\ Valid(v)
                            /\ PolkaDated(r, v, T)
                            /\ now > T + Delta )
                          => \/ Precommit(c, r, v) \in sent
                             \/ CascadeEscape(p, r, v)  )
  BY DEF CascadeCore
\* Clause P. The entry of p is at or below T and the clock is at the entry.
<1>P. ASSUME enteredAt[p][r] <= T, now > T + Delta
      PROVE  FALSE
  BY <1>P, <1>now, <1>ty
\*  Clause N. A nil precommit at r needs prevote evidence at r, a whole
\*  prevote timeout before the clock. Every round-r vote is at or after the
\*  entry.
<1>N. ASSUME Valid(v), Justified(r, v, T), Precommit(c, r, nil) \in sent,
             ~ CascadeEscape(p, r, v)
      PROVE  FALSE
  <2>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
    BY <1>N DEF CascadeEscape
  <2>prop. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
    BY <1>N, JustifiedGivesProposal
  <2>1. \/ \E y \in Honest : Prevote(y, r, nil) \in sent
        \/ \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
             /\ Prevote(y, r, w) \in sent
             /\ sentTime[Prevote(y, r, w)] <= Tq
             /\ now >= Tq + TimeoutPrevote(r)
    BY <1>N, NilPrecommitBacking
  <2>2. CASE \E y \in Honest : Prevote(y, r, nil) \in sent
    BY <1>dur, <1>q, <2>2, <2>nd, <2>prop, NilPrevoteGivesBlocking
  <2>3. CASE \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
               /\ Prevote(y, r, w) \in sent
               /\ sentTime[Prevote(y, r, w)] <= Tq
               /\ now >= Tq + TimeoutPrevote(r)
    <3>1. PICK Tq \in Int, y \in Honest, w \in ValuesOrNil :
            /\ Prevote(y, r, w) \in sent
            /\ sentTime[Prevote(y, r, w)] <= Tq
            /\ now >= Tq + TimeoutPrevote(r)
      BY <2>3
    <3>2. /\ enteredAt[y][r] # OFF
          /\ sentTime[Prevote(y, r, w)] >= enteredAt[y][r]
      BY <3>1 DEF RoundVoteAfterEntry
    <3>m. Prevote(y, r, w) \in Message
      BY <3>1, HonestSubValidators, MsgPrevote
    <3>3. /\ sentTime[Prevote(y, r, w)] \in Int
          /\ enteredAt[y][r] \in Int
          /\ enteredAt[y][r] >= now
      BY <3>1, <3>2, <3>m DEFS FirstToEnter, Lemma5Hyp, OFF, sent, TypeOK
    <3>4. Tq >= now
      BY <3>1, <3>2, <3>3, <1>ty, NatFromChain
    <3> QED
      BY <1>ty, <3>1, <3>4
  <2> QED
    BY <2>1, <2>2, <2>3
\*  Clause Q. One correct member of the polka entered r at or after p, and its
\*  prevote is dated at or after that entry. The polka can therefore not be
\*  before the clock.
<1>Q. ASSUME PolkaDated(r, v, T), now > T + Delta
      PROVE  FALSE
  <2>1. PICK y \in Honest : /\ Prevote(y, r, v) \in sent
                            /\ sentTime[Prevote(y, r, v)] <= T
    BY <1>Q, PolkaHasHonest
  <2>2. /\ enteredAt[y][r] # OFF
        /\ sentTime[Prevote(y, r, v)] >= enteredAt[y][r]
    BY <2>1 DEFS RoundVoteAfterEntry, ValuesOrNil
  <2>m. Prevote(y, r, v) \in Message
    BY <2>1, HonestSubValidators, MsgPrevote DEF ValuesOrNil
  <2>3. /\ sentTime[Prevote(y, r, v)] \in Int
        /\ enteredAt[y][r] \in Int
        /\ enteredAt[y][r] >= now
    BY <2>1, <2>2, <2>m DEFS FirstToEnter, Lemma5Hyp, OFF, sent, TypeOK
  <2>4. T >= now
    BY <1>ty, <2>1, <2>2, <2>3, NatFromChain
  <2> QED
    BY <1>Q, <1>ty, <2>4
<1> QED
  BY <1>P, <1>N, <1>Q

-----------------------------------------------------------------------------
\*  The step. Clause P and clause Q break only at a Tick, and the two lemmas
\*  above hold the Tick. Clause N carries no guard on the clock. Its case for
\*  an old precommit therefore reads the pre-state instance where the
\*  justification is old. It reads NilPrecommitGivesEscape where the
\*  justification is one step fresher.
LEMMA CascadeCoreStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, SentTimeLeNow, GossipDeadline,
         EntryWindowCore, CrossingBacked, EnteredAtLeNow, EnteredCurrentRound,
         PrecommitBacked, PrevoteJustified, PrevoteOncePerRound,
         HonestProposalUnique, HonestProposalUnique', NilPrevoteInWindow,
         RoundVoteAfterEntry, StepPastProposeHasPrevote,
         StepPrecommitHasPrecommit, DecidedStepOp, ProposalDated,
         PrevoteNeedsProposalOrTimeout, PrevoteArmedQuorumTimed,
         RoundEntryHistory, [Next]_vars,
         NEW p \in Honest, NEW r \in Rounds,
         RoundOrigin(p, r), WRDurable(r), NilPrevoteBlocks(p, r),
         CascadeCore(p, r)
  PROVE  CascadeCore(p, r)'
<1> SUFFICES ASSUME NEW c \in Honest, NEW v \in Values, NEW T \in Nat
             PROVE  /\ (  ( /\ T >= GST
                            /\ enteredAt'[p][r] <= T
                            /\ CascadeCeiling(p, r)' <= T + Delta
                            /\ Valid(v)
                            /\ Justified(r, v, T)'
                            /\ now' > T + Delta )
                          => \/ /\ Prevote(c, r, v) \in sent'
                                /\ sentTime'[Prevote(c, r, v)] <= T + Delta
                             \/ CascadeEscape(p, r, v)'  )
                    /\ (  ( /\ T >= GST
                            /\ enteredAt'[p][r] <= T
                            /\ Valid(v)
                            /\ Justified(r, v, T)' )
                          => \/ Precommit(c, r, nil) \notin sent'
                             \/ CascadeEscape(p, r, v)'  )
                    /\ (  ( /\ T >= GST
                            /\ Valid(v)
                            /\ PolkaDated(r, v, T)'
                            /\ now' > T + Delta )
                          => \/ Precommit(c, r, v) \in sent'
                             \/ CascadeEscape(p, r, v)'  )
  BY DEF CascadeCore
<1>q. Proposer[r] \in Honest
  BY DEF WRDurable
<1>ea. enteredAt'[p][r] = enteredAt[p][r]
  BY EnteredAtFrozenStep DEFS OFF, RoundOrigin
<1>ce. CascadeCeiling(p, r)' = CascadeCeiling(p, r)
  BY <1>ea DEF CascadeCeiling
<1>sub. sent \subseteq sent'
  BY SentMonotoneStep
<1>fz. \A mm \in Message : sentTime[mm] # OFF => sentTime'[mm] = sentTime[mm]
  <2>1. SentTimeFrozenPred \/ vars' = vars
    BY SentTimeFrozenStepL
  <2> QED
    BY <2>1 DEFS SentTimeFrozenPred, vars
<1>esc. CascadeEscape(p, r, v) => CascadeEscape(p, r, v)'
  BY CascadeEscapeMove
<1>n. now' = now \/ now' = now + 1
  BY NowShape
<1>ty. /\ now \in Nat /\ now' \in Nat /\ GST \in Nat
       /\ Delta \in Nat /\ Delta > 1 /\ T \in Nat
  BY <1>n, DeltaType, GSTType DEFS TypeOK
\* The conclusion of clause P, carried across one step.
<1>trP. ASSUME Prevote(c, r, v) \in sent,
               sentTime[Prevote(c, r, v)] <= T + Delta
        PROVE  /\ Prevote(c, r, v) \in sent'
               /\ sentTime'[Prevote(c, r, v)] <= T + Delta
  <2>m. Prevote(c, r, v) \in Message
    BY HonestSubValidators, MsgPrevote DEF ValuesOrNil
  <2>1. sentTime'[Prevote(c, r, v)] = sentTime[Prevote(c, r, v)]
    BY <1>fz, <1>trP, <2>m DEF sent
  <2> QED
    BY <1>sub, <1>trP, <2>1
\* ---- CLAUSE P ----------------------------------------------------------
<1>P. ASSUME T >= GST, enteredAt'[p][r] <= T,
             CascadeCeiling(p, r)' <= T + Delta, Valid(v),
             Justified(r, v, T)', now' > T + Delta,
             ~ CascadeEscape(p, r, v)'
      PROVE  /\ Prevote(c, r, v) \in sent'
             /\ sentTime'[Prevote(c, r, v)] <= T + Delta
  <2>ne. ~ CascadeEscape(p, r, v)
    BY <1>esc, <1>P
  <2>h. /\ enteredAt[p][r] <= T
        /\ CascadeCeiling(p, r) <= T + Delta
    BY <1>ea, <1>ce, <1>P
  <2>gt. now >= T + Delta
    BY <1>n, <1>P, <1>ty
  <2>ju. Justified(r, v, T)
    BY <1>P, <1>ty, <2>gt, JustifiedBack
  <2>1. SUFFICES /\ Prevote(c, r, v) \in sent
                 /\ sentTime[Prevote(c, r, v)] <= T + Delta
    BY <1>trP
  <2>2. CASE now > T + Delta
    BY <2>2, <2>h, <2>ju, <2>ne, <1>P DEF CascadeCore
  <2>3. CASE now = T + Delta
    <3>1. now' = now + 1
      BY <1>n, <1>P, <1>ty, <2>3
    <3>2. Tick
      BY <3>1, TickFromClockStep
    <3>3. ~ \E x \in Honest : CanCompute(x)
      BY <3>2 DEF Tick
    <3> QED
      BY <1>P, <2>3, <2>h, <2>ju, <2>ne, <3>3, PrevoteAtQuietClock
  <2> QED
    BY <1>ty, <2>gt, <2>2, <2>3
\* ---- CLAUSE N ----------------------------------------------------------
<1>N. ASSUME T >= GST, enteredAt'[p][r] <= T, Valid(v), Justified(r, v, T)',
             Precommit(c, r, nil) \in sent', ~ CascadeEscape(p, r, v)'
      PROVE  FALSE
  <2>ne. ~ CascadeEscape(p, r, v)
    BY <1>esc, <1>N
  <2>nd. ~ SomeCorrectDecided /\ ~ BlockingLockDuring(p, r)
    BY <2>ne DEF CascadeEscape
  <2>h. enteredAt[p][r] <= T
    BY <1>ea, <1>N
  \*  Case one, the nil precommit is old. Its own backing puts a correct
  \*  prevote at r in the pool, and that prevote puts the proposal there as
  \*  well. The value of the proposal is therefore identified, even when the
  \*  justification is fresh.
  <2>1. CASE Precommit(c, r, nil) \in sent
    <3>1. \/ \E y \in Honest : Prevote(y, r, nil) \in sent
          \/ \E Tq \in Int, y \in Honest, w \in ValuesOrNil :
               /\ Prevote(y, r, w) \in sent
               /\ sentTime[Prevote(y, r, w)] <= Tq
               /\ now >= Tq + TimeoutPrevote(r)
      BY <2>1, NilPrecommitBacking
    <3>2. PICK y \in Honest, w \in ValuesOrNil : Prevote(y, r, w) \in sent
      BY <3>1 DEF ValuesOrNil
    <3>3. PICK vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr2) \in sent
      BY <1>N, <2>nd, <3>2, PreStateProposalForValue
    <3> QED
      BY <1>N, <2>1, <2>ne, <3>3, NilPrecommitGivesEscape
  \* Case two, the nil precommit is fresh. FreshPrecommitAction names the three
  \* emitters.
  <2>2. CASE Precommit(c, r, nil) \notin sent
    <3>m. Precommit(c, r, nil) \in Message
      BY HonestSubValidators, MsgPrecommit DEF ValuesOrNil
    <3>1. /\ Precommit(c, r, nil).round = round[Precommit(c, r, nil).sender]
          /\ \/ OnPrevoteQuorumValueFirstTime(Precommit(c, r, nil).sender)
             \/ OnPrevoteQuorumNil(Precommit(c, r, nil).sender)
             \/ OnTimeoutPrevote(Precommit(c, r, nil).sender)
      BY <1>N, <2>2, <3>m, FreshPrecommitAction DEF Precommit
    <3>2. /\ round[c] = r
          /\ \/ OnPrevoteQuorumValueFirstTime(c)
             \/ OnPrevoteQuorumNil(c)
             \/ OnTimeoutPrevote(c)
      BY <3>1 DEF Precommit
    \* A value precommit cannot be the fresh nil one.
    <3>3. CASE OnPrevoteQuorumValueFirstTime(c)
      <4>1. PICK prop \in RProposalsFromProposerAt(c, round[c]) :
              Broadcast(c, Precommit(c, round[c], prop.value))
        BY <3>3 DEF OnPrevoteQuorumValueFirstTime
      <4>2. prop.value \in Values
        BY <4>1, HonestSubValidators, RProposalValueTyped DEFS Rounds, TypeOK
      <4>3. Precommit(c, r, nil) = Precommit(c, round[c], prop.value)
        BY <1>N, <2>2, <3>m, <4>1 DEFS Broadcast, OFF, sent, TypeOK
      <4> QED
        BY <4>2, <4>3, NilNotInValues DEF Precommit
    \* A nil polka in the view of c holds a correct nil prevote.
    <3>4. CASE OnPrevoteQuorumNil(c)
      <4>1. RExistsPrevoteQuorum(c, nil, round[c])
        BY <3>4 DEF OnPrevoteQuorumNil
      <4>2. PolkaDated(r, nil, now)
        BY <3>2, <4>1, ViewPolkaDated DEFS Rounds, TypeOK, ValuesOrNil
      <4>3. PICK y \in Honest : Prevote(y, r, nil) \in sent
        BY <4>2, PolkaHasHonest
      <4>4. PICK vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr2) \in sent
        BY <1>N, <2>nd, <4>3, PreStateProposalForValue DEF ValuesOrNil
      <4> QED
        BY <1>q, <2>nd, <4>3, <4>4, NilPrevoteGivesBlocking
    \* The fired prevote timer was armed by a quorum a whole TimeoutPrevote(r)
    \* earlier. That is mode 2, and ArmingQuorumGivesEscape holds it.
    <3>5. CASE OnTimeoutPrevote(c)
      <4>1. timer[c]["prevote"] # OFF /\ now >= timer[c]["prevote"]
        BY <3>5 DEF OnTimeoutPrevote
      <4>2. PICK Q \in ByzQuorum :
              \A s \in Q : \E vv \in ValuesOrNil :
                /\ Prevote(s, round[c], vv) \in sent
                /\ sentTime[Prevote(s, round[c], vv)]
                     <= timer[c]["prevote"] - TimeoutPrevote(round[c])
        BY <4>1 DEF PrevoteArmedQuorumTimed
      <4>3. AnyPrevoteDated(r, timer[c]["prevote"] - TimeoutPrevote(r))
        BY <3>2, <4>2 DEF AnyPrevoteDated
      <4>4. PICK y \in Honest, w \in ValuesOrNil :
              /\ Prevote(y, r, w) \in sent
              /\ sentTime[Prevote(y, r, w)]
                   <= timer[c]["prevote"] - TimeoutPrevote(r)
        BY <4>3, AnyPrevoteHasHonest
      <4>ty. /\ timer[c]["prevote"] \in Int
             /\ TimeoutPrevote(r) \in Int
             /\ timer[c]["prevote"] - TimeoutPrevote(r) \in Int
        <5>1. TimeoutPrevote(r) \in Int
          BY T0PrevoteType, TDeltaType DEFS Rounds, TimeoutPrevote
        <5> QED
          BY <5>1, HonestSubValidators DEFS TimerType, TypeOK
      <4>5. now >= (timer[c]["prevote"] - TimeoutPrevote(r)) + TimeoutPrevote(r)
        BY <4>1, <4>ty, <1>ty, SubAddCancel
      <4>6. PICK vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr2) \in sent
        BY <1>N, <2>nd, <4>4, PreStateProposalForValue
      <4> QED
        BY <1>N, <2>ne, <4>4, <4>5, <4>6, <4>ty, ArmingQuorumGivesEscape
    <3> QED
      BY <3>2, <3>3, <3>4, <3>5
  <2> QED
    BY <2>1, <2>2
\* ---- CLAUSE Q ----------------------------------------------------------
<1>Q. ASSUME T >= GST, Valid(v), PolkaDated(r, v, T)', now' > T + Delta,
             ~ CascadeEscape(p, r, v)'
      PROVE  Precommit(c, r, v) \in sent'
  <2>ne. ~ CascadeEscape(p, r, v)
    BY <1>esc, <1>Q
  <2>gt. now >= T + Delta
    BY <1>n, <1>Q, <1>ty
  <2>pk. PolkaDated(r, v, T)
    BY <1>Q, <1>ty, <2>gt, PolkaBack DEF ValuesOrNil
  <2>1. SUFFICES Precommit(c, r, v) \in sent
    BY <1>sub
  <2>2. CASE now > T + Delta
    BY <2>2, <2>pk, <2>ne, <1>Q DEF CascadeCore
  <2>3. CASE now = T + Delta
    <3>1. now' = now + 1
      BY <1>n, <1>Q, <1>ty, <2>3
    <3>2. Tick
      BY <3>1, TickFromClockStep
    <3>3. ~ \E x \in Honest : CanCompute(x)
      BY <3>2 DEF Tick
    <3> QED
      BY <1>Q, <2>3, <2>pk, <2>ne, <3>3, PrecommitAtQuietClock
  <2> QED
    BY <1>ty, <2>gt, <2>2, <2>3
<1> QED
  BY <1>P, <1>N, <1>Q

-----------------------------------------------------------------------------
\* The latch. Each region conjunct the step lemma reads gets one durability
\* leg, and NilPrevoteBlocks arrives already latched from item 11b.
LEMMA BoxCascadeCoreEntry ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ SentTimeLeNow /\ PrecommitBacked /\ PrevoteOncePerRound
              /\ PrevoteJustified /\ HonestProposalUnique /\ NilPrevoteInWindow
              /\ RoundVoteAfterEntry
              /\ Lemma5Hyp(p, r) /\ CaseA(p, r) /\ NilPrevoteBlocks(p, r)
              => CascadeCore(p, r)  )
BY Lemma5HypGivesCascadeCore, PTL

LEMMA BoxCascadeCoreStep ==
  ASSUME NEW p \in Honest, NEW r \in Rounds
  PROVE  [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
              /\ GossipDeadline /\ EntryWindowCore /\ CrossingBacked
              /\ EnteredAtLeNow /\ EnteredCurrentRound /\ PrecommitBacked
              /\ PrevoteJustified /\ PrevoteOncePerRound
              /\ HonestProposalUnique /\ HonestProposalUnique'
              /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
              /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
              /\ DecidedStepOp /\ ProposalDated
              /\ PrevoteNeedsProposalOrTimeout /\ PrevoteArmedQuorumTimed
              /\ RoundEntryHistory /\ [Next]_vars
              /\ RoundOrigin(p, r) /\ WRDurable(r) /\ NilPrevoteBlocks(p, r)
              /\ CascadeCore(p, r)
              => CascadeCore(p, r)'  )
BY CascadeCoreStepL, PTL

THEOREM CascadeCoreLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec
  PROVE  [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []CascadeCore(p, r))
<1>ds. []DecidedStepOp
  BY DecidedStepInv DEF DecidedStepOp
<1>inv. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
             /\ GossipDeadline /\ EntryWindowCore /\ CrossingBacked
             /\ EnteredAtLeNow /\ EnteredCurrentRound /\ RoundEntryHistory
             /\ [Next]_vars  )
  BY CrossingBackedInv, EnteredAtLeNowInv, EnteredCurrentRoundInv,
     EntryWindowCoreInv, GossipDeadlineInv, InvProof, PTL, RoundEntryHistoryInv,
     SentInvInv, SentTimeLeNowInv
  DEFS Inv, Spec
<1>inv2. [](  PrecommitBacked /\ PrevoteJustified /\ PrevoteOncePerRound
              /\ HonestProposalUnique /\ HonestProposalUnique'
              /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
              /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
              /\ ProposalDated /\ PrevoteNeedsProposalOrTimeout
              /\ PrevoteArmedQuorumTimed  )
  BY HonestProposalUniqueInv, NilPrevoteInWindowInv, PrecommitBackedInv,
     PrevoteArmedQuorumTimedInv, PrevoteJustifiedInv,
     PrevoteNeedsProposalOrTimeoutInv, PrevoteOncePerRoundInv, ProposalDatedInv,
     PTL, RoundVoteAfterEntryInv, StepPastProposeHasPrevoteInv,
     StepPrecommitHasPrecommitInv
<1>en. [](  TypeOK /\ SentTimeLeNow /\ PrecommitBacked /\ PrevoteOncePerRound
            /\ PrevoteJustified /\ HonestProposalUnique /\ NilPrevoteInWindow
            /\ RoundVoteAfterEntry
            /\ Lemma5Hyp(p, r) /\ CaseA(p, r) /\ NilPrevoteBlocks(p, r)
            => CascadeCore(p, r)  )
  BY BoxCascadeCoreEntry
<1>ro. [](TypeOK /\ Lemma5Hyp(p, r) => RoundOrigin(p, r))
  BY Lemma5HypRoundOriginBox
<1>rs. [](RoundOrigin(p, r) => []RoundOrigin(p, r))
  BY RoundOriginStable
<1>wd. [](TypeOK /\ Lemma5Hyp(p, r) => WRDurable(r))
  BY BoxLemma5HypWRDurable
<1>ws. [](WRDurable(r) => []WRDurable(r))
  BY WRDurableLatch
<1>np. [](Lemma5Hyp(p, r) /\ CaseA(p, r) => []NilPrevoteBlocks(p, r))
  BY NilPrevoteBlocksLatch
<1>sp. [](  TypeOK /\ RcvdSubsetSent /\ SentInv /\ SentTimeLeNow
            /\ GossipDeadline /\ EntryWindowCore /\ CrossingBacked
            /\ EnteredAtLeNow /\ EnteredCurrentRound /\ PrecommitBacked
            /\ PrevoteJustified /\ PrevoteOncePerRound
            /\ HonestProposalUnique /\ HonestProposalUnique'
            /\ NilPrevoteInWindow /\ RoundVoteAfterEntry
            /\ StepPastProposeHasPrevote /\ StepPrecommitHasPrecommit
            /\ DecidedStepOp /\ ProposalDated
            /\ PrevoteNeedsProposalOrTimeout /\ PrevoteArmedQuorumTimed
            /\ RoundEntryHistory /\ [Next]_vars
            /\ RoundOrigin(p, r) /\ WRDurable(r) /\ NilPrevoteBlocks(p, r)
            /\ CascadeCore(p, r)
            => CascadeCore(p, r)'  )
  BY BoxCascadeCoreStep
<1> QED
  BY <1>ds, <1>inv, <1>inv2, <1>en, <1>ro, <1>rs, <1>wd, <1>ws, <1>np, <1>sp,
     PTL
=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)