---------------- MODULE TendermintPartialSyncTerminationDominator -------------
(***************************************************************************)
(* Stable entry dominator. High locks propagate before every later fresh   *)
(* entry. If no high lock occurs, failure of the current maximum-lock      *)
(* holder raises the bounded maximum. The resulting staircase contradicts  *)
(* the low regime.                                                         *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationSelection,
        TendermintPartialSyncTerminationCrossRound

-----------------------------------------------------------------------------
\* Finite nonempty Honest has a maximum lock holder.
LEMMA MaxLockedRound ==
  ASSUME TypeOK
  PROVE  \E d \in Honest :
           \A c \in Honest : locked[c].round <= locked[d].round
<1> DEFINE P(S) ==
      S # {} =>
        \E d \in S : \A c \in S : locked[c].round <= locked[d].round
<1>int. \A c \in Honest : locked[c].round \in Int
  BY DEF TypeOK, LockState, Rounds
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T \in SUBSET Honest, IsFiniteSet(T), P(T),
              NEW x \in Honest \ T
      PROVE  P(T \cup {x})
  BY <1>2, <1>int
<1>3. P(Honest)
  <2> HIDE DEF P
  <2> QED
    BY <1>1, <1>2, HonestFinite, FS_Induction, IsaM("blast")
<1> QED
  BY <1>3, HonestNonEmptyL DEF P

LEMMA IntLeTransitive ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int,
         a <= b, b <= c
  PROVE  a <= c
BY SMT

\* Lock rounds only rise. A fresh lock is stamped at the current round,
\* which is at least the previous lock round.
LockMonotone ==
  \A c \in Honest : locked[c].round <= locked'[c].round

LEMMA LockMonotoneStep ==
  ASSUME TypeOK, [Next]_vars, LockedBelowRound
  PROVE  LockMonotone
BY RoundMonotoneStep
DEFS Deliver, FaultyStep, HonestNext, HonestStep, LockedBelowRound,
  LockMonotone, LockState, Next, OnPrecommitQuorumValue,
  OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime,
  OnPrevoteQuorumValueLateUpdate, OnProposalNoPOL, OnProposalWithPOL,
  OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose, Rounds,
  ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, TypeOK,
  vars

LockRoundFloor ==
  \A c \in Honest : locked[c].round >= -1

LEMMA LockRoundFloorStepL ==
  ASSUME TypeOK, TypeOK', [Next]_vars, LockedBelowRound, LockRoundFloor
  PROVE  LockRoundFloor'
<1> SUFFICES ASSUME NEW c \in Honest
             PROVE  locked'[c].round >= -1
  BY DEF LockRoundFloor
<1>old. locked[c].round >= -1
  BY DEF LockRoundFloor
<1>mono. locked[c].round <= locked'[c].round
  BY LockMonotoneStep DEF LockMonotone
<1>ty. /\ -1 \in Int
        /\ locked[c].round \in Int
        /\ locked'[c].round \in Int
  BY DEFS LockState, Rounds, TypeOK
<1> QED
  BY ONLY <1>old, <1>mono, <1>ty, IntLeTransitive

THEOREM LockRoundFloorInv == ASSUME Spec PROVE []LockRoundFloor
<1>1. LockRoundFloor
  BY DEF Init, LockRoundFloor, Spec
<1>2. [](TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars)
  BY InvProof, LockedBelowRoundInv, PTL DEF Inv, Spec
<1>3. [](LockRoundFloor => LockRoundFloor')
  BY <1>2, LockRoundFloorStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

-----------------------------------------------------------------------------
MaxLockGe(j) ==
  \E c \in Honest : locked[c].round >= j

IsArgmaxAt(q) ==
  /\ q \in Honest
  /\ \A c \in Honest : locked[c].round <= locked[q].round

ValidGe(q, j) ==
  valid[q].round >= j

LEMMA IntGeNatIsNat ==
  ASSUME NEW a \in Int, NEW b \in Nat, a >= b
  PROVE  a \in Nat
BY SMT

LEMMA NatGeSuccessor ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= b + 1
  PROVE  a > b
BY SMT

LEMMA DeliveryDeadlinePassed ==
  ASSUME NEW sentAt \in Nat, NEW timeout \in Nat,
         NEW current \in Nat, NEW delay \in Nat,
         sentAt + timeout <= current + delay,
         timeout > 2 * delay
  PROVE  current > sentAt + delay
BY SMT

DomInv ==
  /\ Inv
  /\ LockedBelowRound
  /\ ValidBelowRound
  /\ LockedLeValid
  /\ LockRoundFloor
  /\ LockBackedByPrecommit
  /\ LateValueLockGap
  /\ HighLockCatchUp

THEOREM DomInvThm ==
  ASSUME Spec, TimeoutsSufficientBeyond
  PROVE  []DomInv
BY InvProof, LockedBelowRoundInv, ValidBelowRoundInv, LockedLeValidInv,
  LockRoundFloorInv, LockBackedByPrecommitInv, LateValueLockGapInv,
  HighLockCatchUpInv, PTL DEF DomInv

\* This is where the dominator proof consumes paper Lemma 6. At a fresh entry
\* above a high maximum lock, the lock's delivery deadline has passed.
\* HighLockCatchUp raises every correct valid record to that maximum, so every
\* correct process dominates.
LEMMA HighMaxLockDominatesAll ==
  ASSUME TypeOK, LockedLeValid, LockBackedByPrecommit, LateValueLockGap,
         HighLockCatchUp, TimeoutsSufficientBeyond, ~SomeCorrectDecided,
         NEW r \in Rounds, now > GST, FreshEntry(r),
         MaxLockGe(DomCeiling + 1)
  PROVE  \A e \in Honest : SelDominates(e)
<1>1. PICK q \in Honest :
        \A c \in Honest : locked[c].round <= locked[q].round
  BY MaxLockedRound
<1>L. DEFINE L == locked[q].round
<1>2. L >= DomCeiling + 1
  <2>1. PICK c \in Honest : locked[c].round >= DomCeiling + 1
    BY DEF MaxLockGe
  <2>2. locked[c].round <= locked[q].round
    BY <1>1
  <2>ty. /\ DomCeiling + 1 \in Int
          /\ locked[c].round \in Int
          /\ locked[q].round \in Int
    BY DeltaType, GSTType DEFS DomCeiling, LockState, Rounds, TypeOK
  <2> QED
    BY ONLY <2>1, <2>2, <2>ty, IntLeTransitive DEF L
<1>3. L \in Rounds /\ L > DomCeiling
  <2>ceil. DomCeiling \in Nat /\ DomCeiling + 1 \in Nat
    BY DeltaType, GSTType DEF DomCeiling
  <2>ty. L \in Int
    BY DEFS L, LockState, Rounds, TypeOK
  <2>nat. L \in Nat
    BY ONLY <1>2, <2>ceil, <2>ty, IntGeNatIsNat
  <2>gt. L > DomCeiling
    BY ONLY <1>2, <2>ceil, <2>nat, NatGeSuccessor
  <2> QED
    BY <2>nat, <2>gt DEF Rounds
<1>4. PICK p \in Honest : FirstToEnter(p, r)
  BY DEF FreshEntry
<1>5. L < r
  BY <1>1 DEF FreshEntry, L
<1>nonneg. locked[q].round >= 0
  BY <1>3 DEF L, Rounds
<1>6. locked[q].value \in Values
       /\ Precommit(q, L, locked[q].value) \in sent
  BY <1>nonneg DEF LockBackedByPrecommit, L
<1>entry. enteredAt[p][r] = now
  BY <1>4 DEF FirstToEnter
<1>late. enteredAt[p][r] # OFF /\ enteredAt[p][r] > GST
  BY <1>entry, GSTType, SMT DEFS OFF, TypeOK
<1>7. \/ sentTime[Precommit(q, L, locked[q].value)]
             + TimeoutPrecommit(L) <= now + Delta
       \/ L < GST
  BY <1>3, <1>5, <1>6, <1>entry, <1>late DEF LateValueLockGap
<1>8. TimeoutPrecommit(L) > 2 * Delta /\ ~(L < GST)
  BY <1>3, HighRoundFacts, HighRoundPrecommitTimeout
<1>9. now > sentTime[Precommit(q, L, locked[q].value)] + Delta
  <2>deadline.
    sentTime[Precommit(q, L, locked[q].value)]
      + TimeoutPrecommit(L) <= now + Delta
    BY <1>7, <1>8
  <2>msg. Precommit(q, L, locked[q].value) \in Message
    BY <1>6 DEF sent
  <2>sentAt. sentTime[Precommit(q, L, locked[q].value)] \in Nat
    BY <1>6, <2>msg DEFS OFF, sent, TypeOK
  <2>timeout. TimeoutPrecommit(L) \in Nat
    BY <1>3, T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit
  <2>clock. now \in Nat /\ Delta \in Nat
    BY DeltaType DEF TypeOK
  <2> QED
    BY ONLY <1>8, <2>deadline, <2>sentAt, <2>timeout, <2>clock,
      DeliveryDeadlinePassed
<1>10. \A e \in Honest :
          valid[e].round >= L \/ HasDecided(e)
  BY <1>3, <1>6, <1>9 DEF HighLockCatchUp
<1>11. \A e \in Honest : valid[e].round >= L
  BY <1>10 DEF SomeCorrectDecided
<1>12. \A e \in Honest : SelDominates(e)
  <2> SUFFICES ASSUME NEW e \in Honest, NEW c \in Honest
               PROVE  locked[c].round <= valid[e].round
    BY DEF SelDominates
  <2>1. locked[c].round <= L
    BY <1>1 DEF L
  <2>2. L <= valid[e].round
    BY <1>11
  <2>ty. /\ locked[c].round \in Int
          /\ L \in Int
          /\ valid[e].round \in Int
    BY DEFS L, LockState, Rounds, TypeOK
  <2> QED
    BY ONLY <2>1, <2>2, <2>ty, IntLeTransitive
<1> QED
  BY <1>12

AllEntryDominators ==
  \A d \in Honest : EntryDominator(d)

LEMMA BoxHighEntryDominates ==
  [](  DomInv /\ TimeoutsSufficientBeyond /\ ~SomeCorrectDecided
       /\ MaxLockGe(DomCeiling + 1)
       => AllEntryDominators  )
<1>1. DomInv /\ TimeoutsSufficientBeyond /\ ~SomeCorrectDecided
       /\ MaxLockGe(DomCeiling + 1)
       => AllEntryDominators
  BY HighMaxLockDominatesAll
  DEFS AllEntryDominators, DomInv, EntryDominator, Inv
<1> QED
  BY <1>1, PTL

LEMMA BoxAllEntryDominatorAt ==
  ASSUME NEW d \in Honest
  PROVE  [](AllEntryDominators => EntryDominator(d))
<1>1. AllEntryDominators => EntryDominator(d)
  BY DEF AllEntryDominators
<1> QED
  BY <1>1, PTL

LEMMA BoxMaxLockLatch ==
  ASSUME NEW j \in Int
  PROVE  [](  TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars
              /\ MaxLockGe(j)
              => MaxLockGe(j)'  )
<1>1. TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars /\ MaxLockGe(j)
        => MaxLockGe(j)'
  <2> SUFFICES ASSUME TypeOK, TypeOK', LockedBelowRound, [Next]_vars,
                        MaxLockGe(j)
               PROVE  MaxLockGe(j)'
    OBVIOUS
  <2>1. PICK c \in Honest : locked[c].round >= j
    BY DEF MaxLockGe
  <2>mono. LockMonotone
    BY LockMonotoneStep
  <2>up. locked[c].round <= locked'[c].round
    BY <2>mono DEF LockMonotone
  <2>ty. /\ j \in Int
          /\ locked[c].round \in Int
          /\ locked'[c].round \in Int
    BY DEFS LockState, Rounds, TypeOK
  <2>ge. j <= locked'[c].round
    BY ONLY <2>1, <2>up, <2>ty, IntLeTransitive
  <2> QED
    BY <2>ge DEF MaxLockGe
<1> QED
  BY <1>1, PTL

LEMMA BoxDomMaxLockLatch ==
  [](  TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars
       /\ MaxLockGe(DomCeiling + 1)
       => MaxLockGe(DomCeiling + 1)'  )
<1>1. TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars
       /\ MaxLockGe(DomCeiling + 1)
       => MaxLockGe(DomCeiling + 1)'
  <2> SUFFICES ASSUME TypeOK, TypeOK', LockedBelowRound, [Next]_vars,
                        MaxLockGe(DomCeiling + 1)
               PROVE  MaxLockGe(DomCeiling + 1)'
    OBVIOUS
  <2>1. PICK c \in Honest : locked[c].round >= DomCeiling + 1
    BY DEF MaxLockGe
  <2>mono. LockMonotone
    BY LockMonotoneStep
  <2>up. locked[c].round <= locked'[c].round
    BY <2>mono DEF LockMonotone
  <2>ty. /\ DomCeiling + 1 \in Int
          /\ locked[c].round \in Int
          /\ locked'[c].round \in Int
    BY DeltaType, GSTType DEFS DomCeiling, LockState, Rounds, TypeOK
  <2>ge. DomCeiling + 1 <= locked'[c].round
    BY ONLY <2>1, <2>up, <2>ty, IntLeTransitive
  <2> QED
    BY <2>ge DEF MaxLockGe
<1> QED
  BY <1>1, PTL

LEMMA StableDominatorIntro ==
  ASSUME NEW d \in Honest, <>[]EntryDominator(d)
  PROVE  SomeStableDominator
BY DEF SomeStableDominator

THEOREM HighRegimeStable ==
  ASSUME Spec, TimeoutsSufficientBeyond, []~SomeCorrectDecided,
         <>MaxLockGe(DomCeiling + 1)
  PROVE  SomeStableDominator
<1>inv. []DomInv
  BY DomInvThm
<1>lat. [](  TypeOK /\ TypeOK' /\ LockedBelowRound /\ [Next]_vars
             /\ MaxLockGe(DomCeiling + 1)
             => MaxLockGe(DomCeiling + 1)'  )
  BY BoxDomMaxLockLatch
<1>latch. [](MaxLockGe(DomCeiling + 1) => MaxLockGe(DomCeiling + 1)')
  BY <1>inv, <1>lat, PTL DEF DomInv, Inv, Spec
<1>ev. <>[]MaxLockGe(DomCeiling + 1)
  BY <1>latch, PTL
<1>d. PICK d \in Honest : TRUE
  BY HonestNonEmptyL
<1>all. <>[]AllEntryDominators
  BY <1>inv, <1>ev, BoxHighEntryDominates, PTL
<1>at. [](AllEntryDominators => EntryDominator(d))
  BY ONLY BoxAllEntryDominatorAt
<1>1. <>[]EntryDominator(d)
  BY <1>all, <1>at, PTL
<1> QED
  BY <1>1, StableDominatorIntro

-----------------------------------------------------------------------------
\* Low-regime staircase.
LEMMA BoxArgmaxSeedsValid ==
  ASSUME NEW q \in Honest, NEW j \in Nat
  PROVE  [](  TypeOK /\ LockedLeValid /\ IsArgmaxAt(q)
              /\ MaxLockGe(j - 1) => ValidGe(q, j - 1)  )
<1>1. TypeOK /\ LockedLeValid /\ IsArgmaxAt(q)
       /\ MaxLockGe(j - 1) => ValidGe(q, j - 1)
  BY DEFS IsArgmaxAt, LockedLeValid, LockState, MaxLockGe, Rounds, TypeOK, ValidGe
<1> QED
  BY <1>1, PTL

LEMMA BoxValidGeLatch ==
  ASSUME NEW q \in Honest, NEW j \in Int
  PROVE  [](  TypeOK /\ TypeOK' /\ ValidBelowRound /\ [Next]_vars
              /\ ValidGe(q, j)
              => ValidGe(q, j)'  )
<1>1. TypeOK /\ TypeOK' /\ ValidBelowRound /\ [Next]_vars /\ ValidGe(q, j)
        => ValidGe(q, j)'
  <2> SUFFICES ASSUME TypeOK, TypeOK', ValidBelowRound, [Next]_vars,
                        ValidGe(q, j)
               PROVE  ValidGe(q, j)'
    OBVIOUS
  <2>mono. ValidMonotone
    BY ValidMonotoneStep
  <2>old. j <= valid[q].round
    BY DEF ValidGe
  <2>up. valid[q].round <= valid'[q].round
    BY <2>mono DEF ValidMonotone
  <2>ty. /\ j \in Int
         /\ valid[q].round \in Int
         /\ valid'[q].round \in Int
    BY DEFS LockState, Rounds, TypeOK
  <2> QED
    BY ONLY <2>old, <2>up, <2>ty, IntLeTransitive DEF ValidGe
<1> QED
  BY <1>1, PTL

LEMMA BoxValidGePredLatch ==
  ASSUME NEW q \in Honest, NEW j \in Nat
  PROVE  [](  TypeOK /\ TypeOK' /\ ValidBelowRound /\ [Next]_vars
              /\ ValidGe(q, j - 1) => ValidGe(q, j - 1)'  )
<1>1. TypeOK /\ TypeOK' /\ ValidBelowRound /\ [Next]_vars
       /\ ValidGe(q, j - 1) => ValidGe(q, j - 1)'
  <2> SUFFICES ASSUME TypeOK, TypeOK', ValidBelowRound, [Next]_vars,
                        ValidGe(q, j - 1)
               PROVE  ValidGe(q, j - 1)'
    OBVIOUS
  <2>mono. ValidMonotone
    BY ValidMonotoneStep
  <2>old. j - 1 <= valid[q].round
    BY DEF ValidGe
  <2>up. valid[q].round <= valid'[q].round
    BY <2>mono DEF ValidMonotone
  <2>ty. /\ j - 1 \in Int
         /\ valid[q].round \in Int
         /\ valid'[q].round \in Int
    BY DEFS LockState, Rounds, TypeOK
  <2> QED
    BY ONLY <2>old, <2>up, <2>ty, IntLeTransitive DEF ValidGe
<1> QED
  BY <1>1, PTL

LEMMA BoxFailureRaisesMax ==
  ASSUME NEW q \in Honest, NEW j \in Nat
  PROVE  [](  TypeOK /\ ValidGe(q, j - 1) /\ ~EntryDominator(q) => MaxLockGe(j)  )
<1>1. TypeOK /\ ValidGe(q, j - 1) /\ ~EntryDominator(q) => MaxLockGe(j)
  BY DEFS EntryDominator, LockState, MaxLockGe, Rounds, SelDominates, TypeOK, ValidGe
<1> QED
  BY <1>1, PTL

LEMMA DomBoxStaircaseStepAt ==
  ASSUME Spec, NEW q \in Honest, NEW j \in Nat,
         []<>~EntryDominator(q)
  PROVE  [](  IsArgmaxAt(q) /\ MaxLockGe(j - 1) => <>MaxLockGe(j)  )
<1>inv. [](TypeOK /\ LockedBelowRound /\ ValidBelowRound /\ LockedLeValid)
  BY InvProof, LockedBelowRoundInv, ValidBelowRoundInv, LockedLeValidInv, PTL
  DEF Inv, Spec
<1>seed. [](  TypeOK /\ LockedLeValid /\ IsArgmaxAt(q) /\ MaxLockGe(j - 1) => ValidGe(q, j - 1)  )
  BY BoxArgmaxSeedsValid
<1>lat. [](  TypeOK /\ TypeOK' /\ ValidBelowRound /\ [Next]_vars /\ ValidGe(q, j - 1) => ValidGe(q, j - 1)'  )
  BY ONLY BoxValidGePredLatch
<1>raise. [](TypeOK /\ ValidGe(q, j - 1) /\ ~EntryDominator(q) => MaxLockGe(j))
  BY BoxFailureRaisesMax
<1> QED
  BY <1>inv, <1>seed, <1>lat, <1>raise, PTL DEF Spec

NoStableAt(d) ==
  ~<>[]EntryDominator(d)

LEMMA NoStableAtFamily ==
  ASSUME ~SomeStableDominator
  PROVE  \A d \in Honest : NoStableAt(d)
BY DEFS NoStableAt, SomeStableDominator

DomStairAt(q, j) ==
  [](IsArgmaxAt(q) /\ MaxLockGe(j - 1) => <>MaxLockGe(j))

LEMMA StairFamily ==
  ASSUME Spec, ~SomeStableDominator, NEW j \in Nat
  PROVE  \A q \in Honest : DomStairAt(q, j)
<1>ns. ~SomeStableDominator
  OBVIOUS
<1> TAKE q \in Honest
<1>all. \A d \in Honest : NoStableAt(d)
  BY ONLY <1>ns, NoStableAtFamily
<1>not. NoStableAt(q)
  BY <1>all
<1>rec. []<>~EntryDominator(q)
  BY <1>not, PTL DEF NoStableAt
<1> QED
  BY <1>rec, DomBoxStaircaseStepAt DEF DomStairAt

LEMMA DomStairCommute ==
  ASSUME NEW j \in Nat,
         \A q \in Honest : DomStairAt(q, j)
  PROVE  [](\A q \in Honest :
             ((IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j)))
BY DEF DomStairAt

LEMMA DomStairBoxFO ==
  ASSUME NEW j \in Nat
  PROVE  [](  (\A q \in Honest :
                ((IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j)))
              => ((\E q \in Honest :
                     IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j))  )
<1>1. (\A q \in Honest :
        ((IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j)))
      => ((\E q \in Honest :
             IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j))
  OBVIOUS
<1> QED
  BY <1>1, PTL

LEMMA BoxArgmaxExists ==
  ASSUME NEW j \in Nat
  PROVE  [](  TypeOK /\ MaxLockGe(j - 1)
              => (\E q \in Honest : IsArgmaxAt(q) /\ MaxLockGe(j - 1))  )
<1>1. TypeOK /\ MaxLockGe(j - 1)
        => (\E q \in Honest :
              IsArgmaxAt(q) /\ MaxLockGe(j - 1))
  <2> SUFFICES ASSUME TypeOK, MaxLockGe(j - 1)
               PROVE  \E q \in Honest : IsArgmaxAt(q) /\ MaxLockGe(j - 1)
    OBVIOUS
  <2>1. PICK q \in Honest :
          \A c \in Honest : locked[c].round <= locked[q].round
    BY MaxLockedRound
  <2> QED
    BY <2>1 DEF IsArgmaxAt
<1> QED
  BY <1>1, PTL

LEMMA BoxMaxLockGeMinusOne ==
  [](LockRoundFloor => MaxLockGe(0 - 1))
<1>1. LockRoundFloor => MaxLockGe(0 - 1)
  BY HonestNonEmptyL, SMT DEFS LockRoundFloor, MaxLockGe
<1> QED
  BY <1>1, PTL

LEMMA BoxMaxLockGeSuccPred ==
  ASSUME NEW j \in Nat
  PROVE  [](MaxLockGe((j + 1) - 1) <=> MaxLockGe(j))
<1>1. MaxLockGe((j + 1) - 1) <=> MaxLockGe(j)
  BY NatSuccPred
<1> QED
  BY <1>1, PTL

StairResult(j) ==
  <>MaxLockGe(j - 1)

THEOREM MaxLockStaircase ==
  ASSUME Spec, ~SomeStableDominator
  PROVE  \A j \in Nat : StairResult(j)
<1>inv. [](TypeOK /\ LockRoundFloor)
  BY InvProof, LockRoundFloorInv, PTL DEF Inv, Spec
<1> DEFINE P(j) == <>MaxLockGe(j - 1)
<1>base. <>MaxLockGe(0 - 1)
  BY <1>inv, BoxMaxLockGeMinusOne, PTL
<1>0. P(0)
  BY <1>base DEF P
<1>step. \A j \in Nat : P(j) => P(j + 1)
  <2> TAKE j \in Nat
  <2> SUFFICES ASSUME P(j) PROVE P(j + 1)
    OBVIOUS
  <2>ih. <>MaxLockGe(j - 1)
    BY DEF P
  <2>ex. <>(\E q \in Honest :
              IsArgmaxAt(q) /\ MaxLockGe(j - 1))
    BY <1>inv, <2>ih, BoxArgmaxExists, PTL
  <2>fam. \A q \in Honest : DomStairAt(q, j)
    BY StairFamily
  <2>com. [](\A q \in Honest :
        ((IsArgmaxAt(q) /\ MaxLockGe(j - 1)) => <>MaxLockGe(j)))
    BY <2>fam, DomStairCommute
  <2>fo. [](  (\A q \in Honest :
                ((IsArgmaxAt(q) /\ MaxLockGe(j - 1))
                  => <>MaxLockGe(j)))
              => ((\E q \in Honest :
                     IsArgmaxAt(q) /\ MaxLockGe(j - 1))
                    => <>MaxLockGe(j))  )
    BY DomStairBoxFO
  <2>next. <>MaxLockGe(j)
    BY <2>ex, <2>com, <2>fo, PTL
  <2>same. [](MaxLockGe((j + 1) - 1) <=> MaxLockGe(j))
    BY ONLY BoxMaxLockGeSuccPred
  <2> QED
    BY <2>next, <2>same, PTL DEF P
<1>all. \A j \in Nat : P(j)
  <2> HIDE DEF P
  <2> QED
    BY <1>0, <1>step, NatInduction, IsaM("blast")
<1> QED
  BY <1>all DEFS P, StairResult

LEMMA BoxDomCeilingPred ==
  ASSUME DeltaType, GSTType
  PROVE
    [](  MaxLockGe((DomCeiling + 2) - 1)
         <=> MaxLockGe(DomCeiling + 1)  )
<1>ceil. DomCeiling \in Nat
  BY DeltaType, GSTType DEF DomCeiling
<1>arith. (DomCeiling + 2) - 1 = DomCeiling + 1
  BY <1>ceil, SMT
<1>1. MaxLockGe((DomCeiling + 2) - 1)
        <=> MaxLockGe(DomCeiling + 1)
  BY <1>arith
<1> QED
  BY <1>1, PTL

LEMMA StairResultAtCeiling ==
  ASSUME DeltaType, GSTType, StairResult(DomCeiling + 2)
  PROVE  <>MaxLockGe(DomCeiling + 1)
<1>same.
  [](  MaxLockGe((DomCeiling + 2) - 1)
       <=> MaxLockGe(DomCeiling + 1)  )
  BY ONLY DeltaType, GSTType, BoxDomCeilingPred
<1>hit. <>MaxLockGe((DomCeiling + 2) - 1)
  BY DEF StairResult
<1> QED
  BY <1>same, <1>hit, PTL

-----------------------------------------------------------------------------
THEOREM StableEntryDominator ==
  ASSUME Spec, TimeoutsSufficientBeyond
  PROVE  <>SomeCorrectDecided \/ SomeStableDominator
<1> SUFFICES ASSUME []~SomeCorrectDecided PROVE SomeStableDominator
  BY PTL
<1> SUFFICES ASSUME ~SomeStableDominator PROVE FALSE
  OBVIOUS
<1>low. []~MaxLockGe(DomCeiling + 1)
  <2> SUFFICES ASSUME <>MaxLockGe(DomCeiling + 1) PROVE FALSE
    BY PTL
  <2>1. SomeStableDominator
    BY HighRegimeStable
  <2> QED
    BY <2>1
<1>st. \A j \in Nat : StairResult(j)
  BY MaxLockStaircase
<1>n. DomCeiling + 2 \in Nat
  BY DeltaType, GSTType DEF DomCeiling
<1>at. StairResult(DomCeiling + 2)
  BY ONLY <1>st, <1>n
<1>hit. <>MaxLockGe(DomCeiling + 1)
  BY ONLY DeltaType, GSTType, <1>at, StairResultAtCeiling
<1> QED
  BY <1>low, <1>hit, PTL

=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)