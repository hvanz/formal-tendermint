--------------- MODULE TendermintPartialSyncTerminationSelection ---------------
(***************************************************************************)
(* Selection of the good round: the composition module's                   *)
(* GoodRoundRecurrence, with stable dominance proved downstream in         *)
(* ...Dominator.                                                           *)
(*                                                                         *)
(* Paper Lemma 7 needs a state satisfying Lemma5Hyp(p, r) to recur. This   *)
(* module establishes the five entry and timing conjuncts. ...Dominator    *)
(* establishes condition (3), every correct lock at or below the selected  *)
(* proposer's valid round.                                                 *)
(*                                                                         *)
(*  THE EVENT IS A STEP, NOT A STATE. FirstToEnter(p, r) is hard to reach  *)
(*  as a state, and it is easy to obtain as the POST-STATE of the step     *)
(*  that first writes enteredAt[_][r]. Before that step no correct process *)
(*  has entered r. That gives all three clauses of FirstToEnter at one     *)
(*  time. It also gives the soundness clause, which says that every        *)
(*  correct lock is still strictly below r. That last clause is necessary. *)
(*  Without it the selected instant can be a bad one. Several correct      *)
(*  processes then entered r inside one clock instant, and one of them has *)
(*  already locked AT r. Condition (3) would then demand valid[d].round >= *)
(*  r, and no propagation argument gives that.                             *)
(*                                                                         *)
(* THE DOMINANCE CARRIER IS A FIXED PROCESS, RELATIVIZED TO ENTRY          *)
(* INSTANTS. Two shorter shapes are FALSE. The first is "every correct     *)
(* process is eventually always fresh". It fails whenever locks recur,     *)
(* because a lock writes locked[c] in ONE step, and every other correct    *)
(* process installs its valid record later. The second is "the proposer of *)
(* every entered round dominates". It fails as soon as one correct process *)
(* is permanently stale. A process that skips over a lock round never      *)
(* installs the valid record of that round, and it is still proposer       *)
(* infinitely often. What survives is a FIXED correct d that dominates at  *)
(* the entry instants only, which is EntryDominator.                       *)
(*                                                                         *)
(* THE ROUND BOUND IS THE CLOCK. The first entry into a fixed round is a   *)
(* one-shot event, so the recurrence is proved relative to a rigid bound b *)
(* and then collapsed over [](\E b \in Rounds : RoundAtMost(b)), whose     *)
(* witness is `now` (RoundBelowNowInv). No maximum over Honest is needed.  *)
(*                                                                         *)
(* WHAT THIS MODULE DOES NOT DO. The bound-by-bound assembly runs in the   *)
(* COMPOSITION module, not here. A \A whose body is temporal can be        *)
(* produced and commuted but never instantiated, so the loop has to sit    *)
(* where the round recurrence is a citable NEW-parameterized THEOREM. This *)
(* module exports SelectedEntryFromBound for that loop to call, and        *)
(* SelectedEntryRecurs to collapse the family the loop produces.           *)
(*                                                                         *)
(* This module EXTENDS ...WithinRound, and therefore ...Base, and nothing  *)
(* else. It is therefore independent of ...NonZeno, ...CrossRound and      *)
(* ...RoundProgress, and it can be checked in parallel with them.          *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationWithinRound

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 1: three state facts. No temporal reasoning.                      *)
(***************************************************************************)

\* ---- Rounds never go down ------------------------------------------------
\* OnTimeoutPrecommit and SkipRound are the only writers of `round`, and both
\* raise it. Cloned from the action enumeration of Base's RoundClockInvStepL.
LEMMA RoundMonotoneStep ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest
  PROVE  round'[c] \in Nat /\ round[c] <= round'[c]
BY DEFS Deliver, FaultyStep, HonestNext, HonestStep, Next, OnPrecommitQuorumValue,
  OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
  OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote,
  OnTimeoutPropose, Propose, Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote,
  SkipRound, Tick, TypeOK, vars

\* ---- Invariant 1: a lock never sits above its own round ------------------
\* OnPrevoteQuorumValueFirstTime is the only writer of `locked`, and it stamps
\* the CURRENT round without moving it. Every other action leaves `locked`
\* alone while `round` only rises.
LockedBelowRound == \A c \in Honest : locked[c].round <= round[c]

LEMMA LockedBelowRoundStepL ==
  ASSUME TypeOK, [Next]_vars, LockedBelowRound
  PROVE  LockedBelowRound'
BY RoundMonotoneStep DEFS Deliver, FaultyStep, HonestNext, HonestStep, LockedBelowRound,
  LockState, Next, OnPrecommitQuorumValue, OnPrevoteQuorumNil,
  OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL,
  OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
  Rounds, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK, vars

THEOREM LockedBelowRoundInv == ASSUME Spec PROVE []LockedBelowRound
<1>1. LockedBelowRound
  BY DEF Spec, Init, LockedBelowRound
<1>2. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](LockedBelowRound => LockedBelowRound')
  BY <1>2, LockedBelowRoundStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\*  ---- Invariant 2: the honest set enters rounds in order ------------------
\*  A SINGLE correct process can skip rounds. The correct set as a whole
\*  cannot. SkipRound(p, r2) carries a sender quorum of f + 1 for r2. That
\*  quorum holds an honest sender h that is already at or above r2. The
\*  invariant AT h covers every round that p jumped over. OnTimeoutPrecommit
\*  adds exactly round[p] + 1, and the action itself fills that slot. An entry
\*  slot never returns to OFF.
RoundsEnteredDownward ==
  \A c \in Honest : \A r \in Rounds :
    r <= round[c] => \E d \in Honest : enteredAt[d][r] # OFF

\* A weak quorum of the senders of round r holds an honest validator that has
\* itself reached round r. This duplicates SkipEvidenceHonestRound of
\* ...RoundProgress. It is renamed, so that the composition module can EXTEND
\* both. The twenty lines are worth it, because they keep the two frontier
\* modules independent.
LEMMA SelSkipHonestAtRound ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, NEW p \in Honest, NEW r \in Rounds,
         \E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, r)
  PROVE  \E h \in Honest : r <= round[h]
BY WeakQuorumHasHonest DEFS HonestSentOK, RcvdSubsetSent, RSendersOfAnyMessageAt, RSendersOfTypeAtRound, SentInv

LEMMA RoundsEnteredDownwardStepL ==
  ASSUME TypeOK, RcvdSubsetSent, SentInv, RoundEntryHistory, [Next]_vars,
         RoundsEnteredDownward
  PROVE  RoundsEnteredDownward'
<1> SUFFICES ASSUME NEW c \in Honest, NEW r \in Rounds, r <= round'[c]
             PROVE  \E d \in Honest : enteredAt'[d][r] # OFF
  BY DEF RoundsEnteredDownward
<1>disc. EntryUpdateDiscipline
  BY EntryUpdateDisciplineStep
<1>keep. \A dd \in Honest : enteredAt[dd][r] # OFF => enteredAt'[dd][r] # OFF
  BY <1>disc DEF EntryUpdateDiscipline
<1>ty. \A q \in Honest : round[q] \in Nat
  BY DEFS Rounds, TypeOK
<1>rn. r \in Nat
  BY DEF Rounds
<1>1. CASE \E p \in Honest : OnTimeoutPrecommit(p)
  BY <1>1, <1>keep, <1>rn, <1>ty, NowNotOff DEFS OnTimeoutPrecommit, RoundsEnteredDownward, TypeOK
<1>2. CASE \E p \in Honest : \E rr \in Rounds : SkipRound(p, rr)
  <2>0. PICK p \in Honest : \E rr \in Rounds : SkipRound(p, rr)
    BY <1>2
  <2>1. PICK rr \in Rounds : SkipRound(p, rr)
    BY <2>0
  <2>2. /\ round' = [round EXCEPT ![p] = rr]
        /\ (\E W \in WeakQuorum : W \subseteq RSendersOfAnyMessageAt(p, rr))
    BY <2>1 DEF SkipRound
  <2>3. CASE p # c
    BY <1>keep, <2>2, <2>3 DEFS RoundsEnteredDownward, TypeOK
  <2>4. CASE p = c
    BY <1>keep, <1>rn, <1>ty, <2>2, <2>4, SelSkipHonestAtRound DEFS Rounds, RoundsEnteredDownward, TypeOK
  <2> QED
    BY <2>3, <2>4
<1>3. CASE /\ ~(\E p \in Honest : OnTimeoutPrecommit(p))
           /\ ~(\E p \in Honest : \E rr \in Rounds : SkipRound(p, rr))
  <2>1. round' = round
    BY <1>3 DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next,
      OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
      OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
      OnTimeoutPrevote, OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit,
      ScheduleTimeoutPrevote, Tick, vars
  <2>2. PICK d \in Honest : enteredAt[d][r] # OFF
    BY <2>1 DEF RoundsEnteredDownward
  <2> QED
    BY <2>2, <1>keep
<1> QED
  BY <1>1, <1>2, <1>3

THEOREM RoundsEnteredDownwardInv == ASSUME Spec PROVE []RoundsEnteredDownward
<1>1. RoundsEnteredDownward
  BY HonestNonEmptyL DEFS Init, OFF, Rounds, RoundsEnteredDownward, Spec
<1>2. [](TypeOK /\ RcvdSubsetSent /\ SentInv /\ RoundEntryHistory /\ [Next]_vars)
  BY InvProof, SentInvInv, RoundEntryHistoryInv, PTL DEF Spec, Inv
<1>3. [](RoundsEnteredDownward => RoundsEnteredDownward')
  BY <1>2, RoundsEnteredDownwardStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 2: the first-entry flip.                                          *)
(*                                                                         *)
(* NotEntered(r) is the pre-state of the selection event; FreshEntry(r) is *)
(* its post-state. Only OnTimeoutPrecommit and SkipRound can flip it, and  *)
(* both leave `now` and `locked` alone while setting round'[p] = r, which  *)
(* is everything FreshEntry asks for.                                      *)
(***************************************************************************)

NotEntered(r) == \A c \in Honest : enteredAt[c][r] = OFF

FreshEntry(r) ==
  /\ \E p \in Honest : FirstToEnter(p, r)
  /\ \A c \in Honest : locked[c].round < r

\* The entering process p raises its round to r in the same step, and it
\* leaves now and locked alone. Every other correct entry slot for r is still
\* OFF. All three clauses of FirstToEnter, and the lock clause, therefore
\* follow at one time. This is a top-level lemma and not an inline
\* ASSUME/PROVE step, because an inline step does not propagate its
\* assumptions to the nested leaves.
LEMMA FreshEntryFromRaise ==
  ASSUME TypeOK, NEW r \in Rounds, NotEntered(r),
         \A c \in Honest : round[c] < r,
         \A c \in Honest : locked[c].round < r,
         NEW p \in Honest,
         round' = [round EXCEPT ![p] = r],
         enteredAt' = [enteredAt EXCEPT ![p][r] = now],
         now' = now, locked' = locked
  PROVE  FreshEntry(r)'
BY DEFS FirstToEnter, FreshEntry, NotEntered, Rounds, TypeOK

LEMMA FreshEntryAtFlip ==
  ASSUME TypeOK, RoundEntryHistory, RoundsEnteredDownward, LockedBelowRound,
         [Next]_vars, NEW r \in Rounds, NotEntered(r), ~NotEntered(r)'
  PROVE  FreshEntry(r)'
<1>bnd. \A c \in Honest : round[c] < r
  BY DEFS NotEntered, Rounds, RoundsEnteredDownward, TypeOK
<1>lo. \A c \in Honest : locked[c].round < r
  BY <1>bnd DEFS LockedBelowRound, LockState, Rounds, TypeOK
<1>hit. PICK q \in Honest : enteredAt'[q][r] # OFF
  BY DEF NotEntered
<1>fn. enteredAt \in [Honest -> [Rounds -> Nat \cup {OFF}]] /\ now \in Nat
  BY DEF TypeOK
\* Only OnTimeoutPrecommit and SkipRound write enteredAt. Every other action
\* leaves it fixed, so no other action can have caused the flip.
<1>1. CASE \E p \in Honest : OnTimeoutPrecommit(p)
  BY <1>1, <1>bnd, <1>fn, <1>hit, <1>lo, FreshEntryFromRaise DEFS NotEntered, OnTimeoutPrecommit, Rounds, TypeOK
<1>2. CASE \E p \in Honest : \E rr \in Rounds : SkipRound(p, rr)
  BY <1>2, <1>bnd, <1>fn, <1>hit, <1>lo, FreshEntryFromRaise DEFS NotEntered, SkipRound
<1>3. CASE /\ ~(\E p \in Honest : OnTimeoutPrecommit(p))
           /\ ~(\E p \in Honest : \E rr \in Rounds : SkipRound(p, rr))
  BY <1>3, <1>hit DEFS Broadcast, Deliver, FaultyStep, HonestNext, HonestStep, Next, NotEntered,
    OnPrecommitQuorumValue, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
    OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrevote,
    OnTimeoutPropose, Propose, ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, Tick, vars
<1> QED
  BY <1>1, <1>2, <1>3

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 3: recurrent selected entries.                                    *)
(***************************************************************************)

SelInv == Inv /\ SentInv /\ RoundEntryHistory /\ RoundsEnteredDownward
            /\ LockedBelowRound /\ RoundBelowNow

SelStep == SelInv /\ Next /\ SelInv'

\* Some correct validator is beyond round bnd, and its negation as a rigid
\* ceiling. Named operators, not bare quantifiers, so PTL can match them.
SelRoundAbove(b) == \E c \in Honest : round[c] > b

\* The recurrence as a NAMED atom. Coalescing is easier on a name than on a
\* bare quantifier, and consumers must match this formula syntactically.
SelRoundRecurrence == \A b \in Rounds : []<>SelRoundAbove(b)
RoundAtMost(b)   == \A c \in Honest : round[c] <= b

\* A FreshEntry instant at a round that meets the rigid Lemma 5 side
\* conditions with d as proposer. Everything except condition (3).
SelectedEntry(d) ==
  \E b \in Rounds :
    /\ Proposer[b] = d
    /\ b > 0
    /\ now > GST
    /\ Lemma5Timeouts(b)
    /\ FreshEntry(b)

THEOREM SelInvThm == ASSUME Spec PROVE []SelInv
BY InvProof, SentInvInv, RoundEntryHistoryInv, RoundsEnteredDownwardInv,
  LockedBelowRoundInv, RoundBelowNowInv, PTL DEF SelInv

\* ---- The four boxed legs, in clean Spec-free contexts so PTL can
\* necessitate them.
LEMMA SelFlipLeg ==
  ASSUME NEW b \in Rounds
  PROVE  [](NotEntered(b) /\ [SelStep]_vars => (NotEntered(b)' \/ FreshEntry(b)'))
<1>1. NotEntered(b) /\ [SelStep]_vars => (NotEntered(b)' \/ FreshEntry(b)')
  BY FreshEntryAtFlip DEFS Inv, NotEntered, SelInv, SelStep, vars
<1> QED
  BY <1>1, PTL

LEMMA SelExitLeg ==
  ASSUME NEW b \in Rounds
  PROVE  [](SelInv /\ SelRoundAbove(b) => ~NotEntered(b))
<1>1. SelInv /\ SelRoundAbove(b) => ~NotEntered(b)
  BY DEFS Inv, NotEntered, Rounds, RoundsEnteredDownward, SelInv, SelRoundAbove, TypeOK
<1> QED
  BY <1>1, PTL

LEMMA SelStartLeg ==
  ASSUME NEW bnd \in Rounds, NEW b \in Rounds, bnd < b
  PROVE  [](SelInv /\ RoundAtMost(bnd) => NotEntered(b))
<1>1. SelInv /\ RoundAtMost(bnd) => NotEntered(b)
  BY DEFS Inv, NotEntered, RoundAtMost, RoundEntryHistory, Rounds, SelInv, TypeOK
<1> QED
  BY <1>1, PTL

\* The clock chain of finding 1: a round number is a lower bound on the clock.
\* Therefore now > GST follows from b > GST at a FreshEntry instant, with no
\* more work.
LEMMA SelMilestoneLeg ==
  ASSUME NEW d \in Honest, NEW b \in Rounds,
         b > 0, b > GST, Proposer[b] = d, Lemma5Timeouts(b)
  PROVE  [](SelInv /\ FreshEntry(b) => SelectedEntry(d))
<1>1. SelInv /\ FreshEntry(b) => SelectedEntry(d)
  BY GSTType DEFS FirstToEnter, FreshEntry, Inv, OFF, RoundBelowNow, RoundEntryHistory, Rounds, SelectedEntry, SelInv, TypeOK
<1> QED
  BY <1>1, PTL

\* ---- The reach rule: induction plus exit ---------------------------------
\* While FreshEntry(b) stays false, NotEntered(b) is inductive, which is
\* SelFlipLeg. An observed exit from NotEntered(b) can therefore only have
\* come from FreshEntry(b). The rule was prototyped with FLEXIBLE predicates
\* before it was wired in.
LEMMA FreshEntryReach ==
  ASSUME Spec, NEW b \in Rounds
  PROVE  [](NotEntered(b) /\ <>~NotEntered(b) => <>FreshEntry(b))
<1>inv. []SelInv
  BY SelInvThm
<1>1. [](NotEntered(b) /\ [SelStep]_vars => (NotEntered(b)' \/ FreshEntry(b)'))
  BY SelFlipLeg
<1>2. [][SelStep]_vars
  BY <1>inv, PTL DEFS SelStep, Spec
<1> QED
  BY <1>1, <1>2, PTL

\* ---- Assembly at a rigid bound -------------------------------------------
LEMMA SelectedEntryFromBound ==
  ASSUME Spec, NEW d \in Honest, NEW bnd \in Rounds, NEW b \in Rounds,
         b > bnd, b > 0, b > GST, Proposer[b] = d, Lemma5Timeouts(b),
         []<>SelRoundAbove(b)
  PROVE  [](RoundAtMost(bnd) => <>SelectedEntry(d))
<1>inv. []SelInv
  BY SelInvThm
<1>1. [](SelInv /\ RoundAtMost(bnd) => NotEntered(b))
  BY SelStartLeg
<1>2. [](SelInv /\ SelRoundAbove(b) => ~NotEntered(b))
  BY SelExitLeg
<1>3. []<>~NotEntered(b)
  BY <1>inv, <1>2, PTL
<1>4. [](NotEntered(b) /\ <>~NotEntered(b) => <>FreshEntry(b))
  BY FreshEntryReach
<1>5. [](SelInv /\ FreshEntry(b) => SelectedEntry(d))
  BY SelMilestoneLeg
<1> QED
  BY <1>inv, <1>1, <1>3, <1>4, <1>5, PTL

\* ---- The collapse over the bound -----------------------------------------
\* The witness for [](\E bnd \in Rounds : RoundAtMost(bnd)) is `now`, so no
\* FS_Induction maximum over Honest is needed.
LEMMA SelBoundExistsBox ==
  [](TypeOK /\ RoundBelowNow => (\E bnd \in Rounds : RoundAtMost(bnd)))
<1>1. TypeOK /\ RoundBelowNow => (\E bnd \in Rounds : RoundAtMost(bnd))
  BY DEFS RoundAtMost, RoundBelowNow, Rounds, TypeOK
<1> QED
  BY <1>1, PTL

LEMMA SelBoxFO ==
  ASSUME NEW d \in Honest
  PROVE  [](  (\A bnd \in Rounds : (RoundAtMost(bnd) => <>SelectedEntry(d)))
              => ((\E bnd \in Rounds : RoundAtMost(bnd)) => <>SelectedEntry(d))  )
<1>1. (\A bnd \in Rounds : (RoundAtMost(bnd) => <>SelectedEntry(d)))
        => ((\E bnd \in Rounds : RoundAtMost(bnd)) => <>SelectedEntry(d))
  OBVIOUS
<1> QED
  BY <1>1, PTL

\* The assembly bound by bound is NOT done here. To instantiate at a point a
\* \A whose body is TEMPORAL does not work. After coalescing,
\* []<>SelRoundAbove(bnd) is an opaque atom, and no backend can substitute
\* into it. OBVIOUS, Isa and PTL all fail, and so does a plain pass-through
\* from \A to \A across a rename of the bound. What DOES work is a citation of
\* a THEOREM that is parameterized with NEW, because TLAPS applies that as a
\* rule itself. The CALLER therefore runs the loop. It cites
\* SelectedEntryFromBound at each PICKed round, and it hands the collapsed
\* family to this theorem. This theorem only ever COMMUTES that family, and it
\* never instantiates it.
THEOREM SelectedEntryRecurs ==
  ASSUME Spec, NEW d \in Honest,
         \A bnd \in Rounds : [](RoundAtMost(bnd) => <>SelectedEntry(d))
  PROVE  []<>SelectedEntry(d)
<1>com. [](\A bnd \in Rounds : (RoundAtMost(bnd) => <>SelectedEntry(d)))
  OBVIOUS
<1>ex. [](\E bnd \in Rounds : RoundAtMost(bnd))
  BY InvProof, RoundBelowNowInv, SelBoundExistsBox, PTL DEF Inv
<1>fo. [](  (\A bnd \in Rounds : (RoundAtMost(bnd) => <>SelectedEntry(d)))
            => ((\E bnd \in Rounds : RoundAtMost(bnd)) => <>SelectedEntry(d))  )
  BY SelBoxFO
<1> QED
  BY <1>com, <1>ex, <1>fo, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* LAYER 4: the frontier, and the state implication the composition needs. *)
(***************************************************************************)

\* Paper Lemma 7's condition (3), as a named atom.
SelDominates(d) == \A c \in Honest : locked[c].round <= valid[d].round

SelDominatingExists == \E d \in Honest : SelDominates(d)

\* Condition (3) restricted to the instants where the selection consumes it.
\* The two-regime proof that this eventually stabilizes lives in
\* ...Dominator, after the cross-round catch-up invariant is in scope.
EntryDominator(d) ==
  \A r \in Rounds : (now > GST /\ FreshEntry(r)) => SelDominates(d)

\* The dominator existential as a NAMED atom. Written out, it is a quantifier
\* over a TEMPORAL body. An obligation that shows one of those in a large
\* context of assumptions goes to ls4, and it fails. Behind a definition the
\* existential is an opaque propositional atom. Only StableDominatorElim looks
\* inside it, with an ABSTRACT conclusion, and that keeps the one obligation
\* first-order.
SomeStableDominator == \E d \in Honest : <>[]EntryDominator(d)

\* Existential elimination for the dominator, at an abstract D.
LEMMA StableDominatorElim ==
  ASSUME NEW TEMPORAL D, SomeStableDominator,
         \A d \in Honest : (<>[]EntryDominator(d) => D)
  PROVE  D
BY DEF SomeStableDominator

\* ---- The state implication the composition module glues with -------------
\* A selected entry whose proposer dominates at that instant IS a Lemma 5
\* hypothesis state. Kept here, in a clean Spec-free context, so PTL can
\* necessitate it.
LEMMA SelectedGoodRoundBox ==
  ASSUME NEW d \in Honest
  PROVE  [](SelectedEntry(d) /\ EntryDominator(d) => GoodRoundExists)
<1>1. SelectedEntry(d) /\ EntryDominator(d) => GoodRoundExists
  BY DEFS EntryDominator, FreshEntry, GoodRoundExists, Lemma5Hyp, SelDominates, SelectedEntry
<1> QED
  BY <1>1, PTL

\* The round latch that turns a one-shot round advance into a recurrence:
\* rounds never go down, so "some correct is above b" sticks.
LEMMA SelRoundAboveLatchBox ==
  ASSUME NEW b \in Rounds
  PROVE  [](TypeOK /\ [Next]_vars /\ SelRoundAbove(b) => SelRoundAbove(b)')
<1>1. TypeOK /\ [Next]_vars /\ SelRoundAbove(b) => SelRoundAbove(b)'
  BY RoundMonotoneStep DEFS Rounds, SelRoundAbove, TypeOK
<1> QED
  BY <1>1, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)