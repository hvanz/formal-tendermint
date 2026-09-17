--------------- MODULE TendermintPartialSyncTerminationLockRetry ---------------
(***************************************************************************)
(* Paper Lemma 7, case 2, and the retry. Three ingredients meet here. The  *)
(* good round recurs (a hypothesis of this module, discharged by           *)
(* GoodRoundRecurrence in the composition module). Each good round         *)
(* resolves into a decision or a blocking stale lock formed DURING that    *)
(* round (Lemma5OrBlockingLock, in ...Cascade). And this module            *)
(* supplies the missing piece: the disruption stops, so one good round     *)
(* runs to a decision.                                                     *)
(*                                                                         *)
(* THE MEASURE IS A PAIR COUNT. The disruption of a good round needs a     *)
(* correct VALUE PRECOMMIT, and only a finite number of those is           *)
(* available.                                                              *)
(* 1. The disrupting lock sits at a LOW round. LateValueLockWindow and     *)
(*    DisruptionRoundCeilingWithGST together bound it by Delta + GST.      *)
(* 2. Each low pair <<validator, round>> carries AT MOST ONE lock. A       *)
(*    correct validator sends at most one precommit per round, which is    *)
(*    PrecommitOncePerRound, and an activated sentTime never changes.      *)
(* 3. The clock goes past any fixed lock. Without a decision the clock is  *)
(*    unbounded, which is ClockUnbounded. Good rounds therefore occur at   *)
(*    entry instants that are unboundedly late. Each disruption must be    *)
(*    dated after its own entry instant, and therefore after every lock of *)
(*    the previous era. Each era therefore uses a pair that no earlier era *)
(*    used, and Honest \X (0 .. Delta + GST) is finite. The count is the   *)
(*    measure, and the module has NO admission.                            *)
(*                                                                         *)
(* A measure on the chain of disruptive lock rounds does NOT work. That    *)
(* chain runs through the valid round of the proposer. The vr of a round-r *)
(* proposal can lag valid[Proposer[r]].round at the entry state, so the    *)
(* chain need not increase at all. The count above avoids `valid`          *)
(* completely, and it reads only `sent`.                                   *)
(*                                                                         *)
(* Consumes ...Cascade, and through it ...RoundProgress for the window     *)
(* lemma, the round growth and the fresh-precommit emitter, and            *)
(* ...WithinRound for the good-round interface. Independent of             *)
(* ...CrossRound and ...Selection.                                         *)
(***************************************************************************)
EXTENDS TendermintPartialSyncTerminationCascade

\* ---- The goal of the module ------------------------------------------------
\* Some good round runs without a blocking stale lock. LockRetryDecides turns
\* that into <>SomeCorrectDecided through QuietRoundDecides and UndisruptedElim,
\* and UndisruptedGoodRoundExists at the end of this module discharges it on the
\* pair count.
\*
\* A NAMED atom, because an \E over a TEMPORAL body must travel as a name.
\* Written out in place, it coalesces to a different formula on the two sides
\* of a modus ponens. An obligation that exposes one of those in a large
\* context of assumptions goes to ls4, and it fails. Only UndisruptedElim and
\* UndisruptedIntro look inside, and that keeps those two obligations
\* first-order.
UndisruptedGoodRound ==
  \E p \in Honest : \E r \in Rounds :
    <>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r))

-----------------------------------------------------------------------------
\* ---- Existential elimination at an abstract conclusion --------------------
\* The dominator pattern of ...Selection (StableDominatorElim): do NOT PICK a
\* witness out of an \E over a temporal body. Prove the tail for an arbitrary
\* element and discharge the existential at an abstract D.
LEMMA UndisruptedElim ==
  ASSUME NEW TEMPORAL D, UndisruptedGoodRound,
         \A p \in Honest : \A r \in Rounds :
           (<>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r)) => D)
  PROVE  D
BY DEF UndisruptedGoodRound

\* ---- Existential INTRODUCTION, the mirror image ---------------------------
\* The other side of the same atom, and what turns the negated goal into the
\* leads-to family the count consumes: ~<>(A /\ []~B) is A ~> B. Binder names
\* are p and r on purpose, matching UndisruptedGoodRound's own binders:
\* instantiating a temporal-body quantifier at a differently named constant
\* fails.
LEMMA UndisruptedIntro ==
  ASSUME ~UndisruptedGoodRound, NEW p \in Honest, NEW r \in Rounds
  PROVE  ~<>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r))
BY DEF UndisruptedGoodRound

\*  ---- The quiet-suffix step, per round
\*  ------------------------------------- At the instant of the good round the
\*  outcome is reached later. The blocking disjunct is excluded from that
\*  instant on, so the decision disjunct fires. Lemma5OrBlockingLock is cited
\*  at IDENTITY, which is the only shape that a ~> conclusion supports. Its
\*  outcome reaches PTL as a disjunction of atoms, through the boxed identity
\*  BlockingOutcomeBox, because no backend unfolds a definition under [].
LEMMA QuietRoundDecides ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, Spec,
         <>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r))
  PROVE  <>SomeCorrectDecided
BY BlockingOutcomeBox, Lemma5OrBlockingLock, PTL

-----------------------------------------------------------------------------
\*  ---- Timing ceiling, arithmetic core
\*  -------------------------------------- The disruption of a good round
\*  needs the disrupting validator to be still at its own round lr, in step
\*  "prevote". Another correct validator has by then already entered a round
\*  above lr. TimeoutPrecommit(lr) bounds how long that can last. This lemma is
\*  the step that turns that bound on the CLOCK into a bound on the ROUND. It
\*  is the whole reason why the retry closes on a measure. TimeoutPrecommit is
\*  affine, with a strictly positive increment, so a bound on it is a bound on
\*  lr.
LEMMA DisruptionRoundCeiling ==
  ASSUME NEW lr \in Rounds, TimeoutPrecommit(lr) <= Delta
  PROVE  lr <= Delta
BY DeltaType, T0PrecommitType, TDeltaType DEFS Rounds, TimeoutPrecommit

\* ---- The ceiling in the form that the window lemma delivers --------------
\* LateValueLockWindow cannot conclude TimeoutPrecommit(lr) <= Delta alone.
\* That form is FALSE, and TLC refutes it in the "window-gst" scenario of
\* ...WithinRoundMC. DeliveryDeadline(m) is max(sentTime[m], GST) + Delta. A
\* message that is sent before GST can therefore be withheld until GST +
\* Delta, however early it was sent. A correct validator that is held short of
\* a quorum through that stretch can value-precommit at a low round
\* arbitrarily late, in terms of TimeoutPrecommit.
\*
\* The escape is itself a round bound. The sender of the withholding era was
\* AT round lr at that instant, and RoundBelowNow bounds a correct round by
\* the clock. The residue is therefore lr < GST. Both disjuncts are CONSTANT
\* ceilings, and a constant is all that the retry consumes. The disruptive
\* lock rounds strictly increase, so any constant ceiling bounds the number of
\* disruptions.
LEMMA DisruptionRoundCeilingWithGST ==
  ASSUME NEW lr \in Rounds, TimeoutPrecommit(lr) <= Delta \/ lr < GST
  PROVE  lr <= Delta + GST
BY DeltaType, DisruptionRoundCeiling, GSTType DEF Rounds

-----------------------------------------------------------------------------
(***************************************************************************)
(* THE PAIR COUNT: the ammunition is finite, and the count is the measure. *)
(*                                                                         *)
(*  Three observations close the retry. 1. The disruption lock sits at a   *)
(*  LOW round. LateValueLockWindow and DisruptionRoundCeilingWithGST       *)
(*  together bound the round of the correct value precommit that disrupts  *)
(*  a good round by LockCeiling = Delta + GST. 2. Each low pair carries AT *)
(*  MOST ONE lock. A correct validator sends at most one precommit per     *)
(*  round, which is PrecommitOncePerRound. The pair <<c, lr>>, in the      *)
(*  finite set Honest \X (0 .. LockCeiling), therefore identifies at most  *)
(*  one message, and that message has one frozen sentTime. 3. The clock    *)
(*  goes past any fixed lock. The disruption lock is dated at or after the *)
(*  instant of entry into the good round. Under []~SomeCorrectDecided the  *)
(*  clock is unbounded, so good rounds occur at entry instants that are    *)
(*  unboundedly late. Each one needs a lock that is dated later than the   *)
(*  previous era. The pairs are therefore exhausted.                       *)
(***************************************************************************)

\* ---- The snapshot vocabulary ----------------------------------------------
\* LockCeiling is item 1 of the count: LateValueLockWindow plus
\* DisruptionRoundCeilingWithGST bound the disruption lock's round by it.
LockCeiling == Delta + GST
LowPairs    == Honest \X (0 .. LockCeiling)
LowBudget   == Cardinality(LowPairs)

\* The pairs whose lock has already been spent. Monotone along the behaviour,
\* because `sent` only grows.
UsedLow == { pr \in LowPairs :
               \E w \in Values : Precommit(pr[1], pr[2], w) \in sent }
Used    == Cardinality(UsedLow)

\* THE SNAPSHOT BOUND IS NAMED b THROUGHOUT, and it must stay named b. The
\* conclusion of a TEMPORAL rule matches only at IDENTITY. TLAPS cannot
\* instantiate one, so a cited rule with a temporal conclusion closes only
\* when the backend sees the hypothesis literally as the goal. The bound of
\* ClockUnbounded must therefore carry the same name as the binder of
\* ProgressBeyond, which is b. Every consumer of ClockUnbounded must use that
\* name too. To rename it here breaks FreshRecurs.
\*
\*  THE DEVICE THAT REMOVES EVERY COMPARISON OF TWO TIME POINTS. The natural
\*  form of item 3 is "the lock is newer than everything in `sent` at the
\*  earlier state". That form compares two states. TLAPS cannot instantiate a
\*  quantifier over a temporal body at a PICKed term or at a compound term.
\*  The clock value of the earlier state must therefore never leave the
\*  formula as a state function. To index the snapshot by a CONSTANT b fixes
\*  that. UsedBy(b) is readable at ANY state, and it is monotone, because
\*  `sent` grows and SentTimeFrozenInv freezes an activated sentTime.
\*  Cardinality(UsedBy(b)) >= j therefore LATCHES, and the count carries
\*  forward with no PICK and with no history variable. At a state with now <=
\*  b it agrees with UsedLow, by SentTimeLeNow.
UsedBy(b) == { pr \in LowPairs :
                 \E w \in Values :
                   /\ Precommit(pr[1], pr[2], w) \in sent
                   /\ sentTime[Precommit(pr[1], pr[2], w)] <= b }

\* A low pair whose lock is dated ABOVE b: the fresh ammunition of one era.
FreshLowLock(b) ==
  \E c \in Honest, lr \in 0 .. LockCeiling, w \in Values :
    /\ Precommit(c, lr, w) \in sent
    /\ sentTime[Precommit(c, lr, w)] > b

\* The latched residue of a good round. Lemma5Hyp gives now > GST and
\* FirstToEnter gives enteredAt[p][r] = now, so the conjunction holds at the
\* entry and never fails again (enteredAt is write once).
EnteredPast(p, r, b) ==
  /\ enteredAt[p][r] # OFF
  /\ enteredAt[p][r] > GST
  /\ enteredAt[p][r] > b

\* ---- Items 4 to 6: a disrupted good round uses a low pair ----------------
\* The state core. LateValueLockWindow needs exactly the four conjuncts that
\* EnteredPast and the blocking witness supply between them.
\* DisruptionRoundCeilingWithGST turns the two-disjunct conclusion of that
\* lemma into the single round bound that indexes the set of pairs.
LEMMA FreshFromDisruptionState ==
  ASSUME TypeOK, LateValueLockWindow, NEW p \in Honest, NEW r \in Rounds,
         NEW b \in Nat, EnteredPast(p, r, b), BlockingLockDuring(p, r)
  PROVE  FreshLowLock(b)
<1>1. PICK w \in Values, c \in Honest, lr \in Rounds :
        /\ lr < r
        /\ Precommit(c, lr, w) \in sent
        /\ sentTime[Precommit(c, lr, w)] >= enteredAt[p][r]
  BY DEFS BlockingLockDuring, VotedPrecommit
<1>m. Precommit(c, lr, w) \in Message
  BY DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
<1>w. TimeoutPrecommit(lr) <= Delta \/ lr < GST
  BY <1>1 DEFS EnteredPast, LateValueLockWindow
<1>c. lr <= Delta + GST
  BY <1>w, DisruptionRoundCeilingWithGST
<1>n. lr \in 0 .. LockCeiling
  BY <1>c DEFS LockCeiling, Rounds
\* The timestamp conjunct is the whole of observation 3: the lock is dated at
\* or after the entry instant, and the entry instant is above b.
<1>t. sentTime[Precommit(c, lr, w)] > b
  BY <1>1, <1>m DEFS EnteredPast, OFF, TypeOK
<1> QED
  BY <1>1, <1>n, <1>t DEF FreshLowLock

LEMMA BoxFreshFromDisruption ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ LateValueLockWindow
              /\ EnteredPast(p, r, b) /\ BlockingLockDuring(p, r)
              => FreshLowLock(b)  )
BY FreshFromDisruptionState, PTL

\* EnteredPast latches: enteredAt is write once, and the two inequalities are
\* against CONSTANTS, so no case split over the actions is needed.
LEMMA BoxEnteredPastLatch ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](  TypeOK /\ RoundEntryHistory /\ [Next]_vars
              /\ EnteredPast(p, r, b) => EnteredPast(p, r, b)'  )
<1>1. TypeOK /\ RoundEntryHistory /\ [Next]_vars /\ EnteredPast(p, r, b)
        => EnteredPast(p, r, b)'
  BY EnteredAtFrozenStep DEF EnteredPast
<1> QED
  BY <1>1, PTL

\* The entry: Lemma5Hyp gives now > GST and FirstToEnter gives
\* enteredAt[p][r] = now, so EnteredPast holds AT the good-round instant.
LEMMA BoxEntryFromHyp ==
  ASSUME NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat
  PROVE  [](TypeOK /\ Lemma5Hyp(p, r) /\ now > b => EnteredPast(p, r, b))
<1>1. TypeOK /\ Lemma5Hyp(p, r) /\ now > b => EnteredPast(p, r, b)
  BY DEFS EnteredPast, FirstToEnter, Lemma5Hyp, OFF, TypeOK
<1> QED
  BY <1>1, PTL

\* The per-pair era statement. The leads-to is cited at IDENTITY, the only shape
\* a ~> conclusion supports. []LateValueLockWindow travels as a HYPOTHESIS, so
\* this module states the window lemma rather than re-deriving it.
LEMMA FreshFromEntry ==
  ASSUME Spec, NEW p \in Honest, NEW r \in Rounds, NEW b \in Nat,
         []LateValueLockWindow,
         Lemma5Hyp(p, r) ~> BlockingLockDuring(p, r)
  PROVE  [](Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b))
BY BoxEnteredPastLatch, BoxEntryFromHyp, BoxFreshFromDisruption, InvProof, PTL, RoundEntryHistoryInv DEFS Inv, Spec

\* ---- Items 7 and 8: the era statement recurs ------------------------------
LEMMA FreshBoxFO ==
  ASSUME NEW b \in Nat
  PROVE  [](  (\A p \in Honest : \A r \in Rounds :
                 (Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b)))
              => (GoodRoundExists /\ now > b => <>FreshLowLock(b))  )
<1>1. (\A p \in Honest : \A r \in Rounds :
         (Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b)))
      => (GoodRoundExists /\ now > b => <>FreshLowLock(b))
  BY DEF GoodRoundExists
<1> QED
  BY <1>1, PTL

\* The recurrence. The \A p, r hypothesis is a quantifier over a temporal body:
\* it is PRODUCED by the caller's TAKE and CONSUMED here at TAKEn constants of
\* the IDENTICAL binder names, the only instantiation that survives coalescing.
\* No step instantiates it at a PICKed constant.
THEOREM FreshRecurs ==
  ASSUME Spec, []~SomeCorrectDecided, []<>GoodRoundExists,
         []LateValueLockWindow,
         \A p \in Honest : \A r \in Rounds :
           (Lemma5Hyp(p, r) ~> BlockingLockDuring(p, r))
  PROVE  \A b \in Nat : []<>FreshLowLock(b)
<1> TAKE b \in Nat
<1>cu. <>[](now > b)
  BY ClockUnbounded
\* The PTL validity <>[]A /\ []<>B => []<>(A /\ B): a recurring good round and
\* an eventually permanent clock bound coincide infinitely often.
<1>gr. []<>(GoodRoundExists /\ now > b)
  BY <1>cu, PTL
<1>pr. \A p \in Honest : \A r \in Rounds :
         [](Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b))
  BY FreshFromEntry
<1>c. [](\A p \in Honest : \A r \in Rounds :
           (Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b)))
  BY <1>pr
<1>fo. [](  (\A p \in Honest : \A r \in Rounds :
               (Lemma5Hyp(p, r) /\ now > b => <>FreshLowLock(b)))
            => (GoodRoundExists /\ now > b => <>FreshLowLock(b))  )
  BY FreshBoxFO
<1> QED
  BY <1>gr, <1>c, <1>fo, PTL

\* ---- Item 9: the finite set of pairs -------------------------------------
\* LowPairs is a CONSTANT set, because Honest, Delta and GST are constants.
\* Every snapshot is therefore a subset of one fixed finite set, and the four
\* facts about cardinality below all reduce to FS_Subset over it. The idiom is
\* StepWorkNat of ...Base.
LEMMA LowPairsFinite == IsFiniteSet(LowPairs) /\ LowBudget \in Nat
<1>c. LockCeiling \in Nat
  BY DeltaType, GSTType DEF LockCeiling
<1>1. IsFiniteSet(LowPairs)
  BY <1>c, FS_Interval, FS_Product, HonestFinite DEF LowPairs
<1> QED
  BY <1>1, FS_CardinalityType DEF LowBudget

LEMMA UsedLowFacts ==
  /\ UsedLow \subseteq LowPairs
  /\ IsFiniteSet(UsedLow)
  /\ Cardinality(UsedLow) \in Nat
  /\ Used \in 0 .. LowBudget
BY FS_CardinalityType, FS_Subset, LowPairsFinite DEFS LowBudget, Used, UsedLow

LEMMA UsedByFacts ==
  ASSUME NEW b \in Nat
  PROVE  /\ UsedBy(b) \subseteq UsedLow
         /\ IsFiniteSet(UsedBy(b))
         /\ Cardinality(UsedBy(b)) \in Nat
BY FS_CardinalityType, FS_Subset, UsedLowFacts DEFS UsedBy, UsedLow

LEMMA BoxUsedLeBudget == [](TypeOK => Used \in 0 .. LowBudget)
BY PTL, UsedLowFacts

\* ---- The snapshot latches -------------------------------------------------
\* UsedBy(b) is monotone: `sent` only grows and an activated sentTime never
\* changes. UNCHANGED vars implies SentTimeFrozenPred outright, so the
\* action-level hypothesis needs no case split beyond one step.
LEMMA UsedByMonotone ==
  ASSUME TypeOK, [Next]_vars, [SentTimeFrozenPred]_vars, NEW b \in Nat
  PROVE  UsedBy(b) \subseteq (UsedBy(b))'
BY DeltaType, GSTType, SentMonotoneStep
DEFS Honest, LockCeiling, LowPairs, Message, Precommit, PrecommitMsg, Rounds, sent, SentTimeFrozenPred, UsedBy, ValuesOrNil, vars

LEMMA UsedByLatchState ==
  ASSUME TypeOK, [Next]_vars, [SentTimeFrozenPred]_vars,
         NEW b \in Nat, NEW j \in Nat, Cardinality(UsedBy(b)) >= j
  PROVE  (Cardinality(UsedBy(b)) >= j)'
BY FS_CardinalityType, FS_Subset, LowPairsFinite, UsedByFacts, UsedByMonotone DEFS LockCeiling, LowPairs, UsedBy

LEMMA BoxUsedByLatch ==
  ASSUME NEW b \in Nat, NEW j \in Nat
  PROVE  [](  TypeOK /\ [Next]_vars /\ [SentTimeFrozenPred]_vars
              /\ Cardinality(UsedBy(b)) >= j
              => (Cardinality(UsedBy(b)) >= j)'  )
BY PTL, UsedByLatchState

\* ---- The counting step ---------------------------------------------------
\* This is item 2 of the count, used. A pair whose lock is dated ABOVE b
\* cannot also sit in the snapshot AT b. The pair identifies at most one
\* message, and that message has one frozen timestamp.
LEMMA FreshAddsOneState ==
  ASSUME TypeOK, PrecommitOncePerRound, NEW b \in Nat, NEW j \in Nat,
         FreshLowLock(b), Cardinality(UsedBy(b)) >= j
  PROVE  Used >= j + 1
<1>1. PICK c \in Honest, lr \in 0 .. LockCeiling, w \in Values :
        /\ Precommit(c, lr, w) \in sent
        /\ sentTime[Precommit(c, lr, w)] > b
  BY DEF FreshLowLock
<1>ck. LockCeiling \in Nat
  BY DeltaType, GSTType DEF LockCeiling
<1>lr. lr \in Rounds
  BY <1>1, <1>ck DEF Rounds
<1> DEFINE pr0 == <<c, lr>>
<1>lp. pr0 \in LowPairs
  BY <1>1 DEF LowPairs
<1>in. pr0 \in UsedLow
  BY <1>1, <1>lp DEF UsedLow
<1>out. pr0 \notin UsedBy(b)
  <2> SUFFICES ASSUME pr0 \in UsedBy(b) PROVE FALSE
    OBVIOUS
  <2>1. PICK w2 \in Values :
          /\ Precommit(c, lr, w2) \in sent
          /\ sentTime[Precommit(c, lr, w2)] <= b
    BY DEF UsedBy
  <2>2. w2 = w
    BY <1>1, <1>lr, <2>1 DEFS PrecommitOncePerRound, ValuesOrNil
\* The clash is arithmetic, so the timestamp must be TYPED. TypeOK in the
\* context is not enough. It must be unfolded, and OFF with it.
  <2>3. Precommit(c, lr, w) \in Message
    BY <1>1, <1>lr DEFS Honest, Message, Precommit, PrecommitMsg, ValuesOrNil
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3 DEFS OFF, TypeOK
<1>sub. UsedBy(b) \cup {pr0} \subseteq UsedLow
  BY <1>in, UsedByFacts
<1>fin. IsFiniteSet(UsedBy(b)) /\ Cardinality(UsedBy(b)) \in Nat
  BY UsedByFacts
<1>ul. IsFiniteSet(UsedLow) /\ Cardinality(UsedLow) \in Nat
  BY UsedLowFacts
<1>add. IsFiniteSet(UsedBy(b) \cup {pr0})
        /\ Cardinality(UsedBy(b) \cup {pr0}) = Cardinality(UsedBy(b)) + 1
  BY <1>fin, <1>out, FS_AddElement
<1>le. Cardinality(UsedBy(b) \cup {pr0}) <= Cardinality(UsedLow)
  BY <1>add, <1>ul, <1>sub, FS_Subset
<1> QED
  BY <1>add, <1>fin, <1>le, <1>ul DEF Used

LEMMA BoxFreshAddsOne ==
  ASSUME NEW b \in Nat, NEW j \in Nat
  PROVE  [](  TypeOK /\ PrecommitOncePerRound
              /\ FreshLowLock(b) /\ Cardinality(UsedBy(b)) >= j
              => Used >= j + 1  )
BY FreshAddsOneState, PTL

\* ---- Where SentTimeLeNow enters -------------------------------------------
\* At a state whose clock has not passed b, the snapshot AT b is the whole
\* spent set: every activated timestamp is at most now.
LEMMA UsedEqUsedByState ==
  ASSUME TypeOK, SentTimeLeNow, NEW b \in Nat, now <= b
  PROVE  UsedLow = UsedBy(b)
BY DeltaType, GSTType, UsedByFacts
DEFS Honest, LockCeiling, LowPairs, Message, OFF, Precommit, PrecommitMsg, Rounds, sent, SentTimeLeNow, TypeOK, UsedBy, UsedLow, ValuesOrNil

LEMMA BoxUsedEqUsedBy ==
  ASSUME NEW b \in Nat
  PROVE  [](TypeOK /\ SentTimeLeNow /\ now <= b => UsedLow = UsedBy(b))
BY PTL, UsedEqUsedByState

\* ---- Item 10: the staircase -----------------------------------------------
\* THE GUARD IS A STATE PREDICATE, and it has to be. The natural guard is
\* "inside the region [](Used >= j), at a state with now <= b", but a guard
\* containing [] is not a state predicate, and then the existential lift below
\* coalesces `\E b : ([]... /\ now <= b)` into an atom unrelated to the state
\* predicate `\E b \in Nat : now <= b`, which breaks the step.
\*
\* The region is not necessary. Used >= j at the ONE state is enough. What
\* latches is the SNAPSHOT Cardinality(UsedBy(b)) >= j, and not Used >= j. The
\* snapshot is taken at that state, and BoxUsedByLatch carries it forward.
LEMMA BoxUsedGeZero == [](TypeOK => Used >= 0)
<1>1. TypeOK => Used >= 0
  BY UsedLowFacts
<1> QED
  BY <1>1, PTL

LEMMA BoxGuardExB ==
  ASSUME NEW j \in Nat
  PROVE  [](TypeOK /\ Used >= j => (\E b \in Nat : (Used >= j /\ now <= b)))
<1>1. TypeOK /\ Used >= j => (\E b \in Nat : (Used >= j /\ now <= b))
  BY DEF TypeOK
<1> QED
  BY <1>1, PTL

\* One leg instead of two: the set equality and the cardinality transfer
\* together, so the PTL assembly below sees a single boxed implication.
LEMMA BoxSnapAtBound ==
  ASSUME NEW b \in Nat, NEW j \in Nat
  PROVE  [](  TypeOK /\ SentTimeLeNow /\ now <= b /\ Used >= j
              => Cardinality(UsedBy(b)) >= j  )
<1>1. TypeOK /\ SentTimeLeNow /\ now <= b /\ Used >= j
        => Cardinality(UsedBy(b)) >= j
  BY UsedEqUsedByState DEF Used
<1> QED
  BY <1>1, PTL

\* The step at ONE bound. Snapshot at the guard state, latch it, wait for the
\* era's fresh lock, add the one.
LEMMA BoxStaircaseStepAt ==
  ASSUME Spec, NEW b \in Nat, NEW j \in Nat, []<>FreshLowLock(b)
  PROVE  [](  (Used >= j /\ now <= b) => <>(Used >= j + 1)  )
BY BoxFreshAddsOne, BoxSnapAtBound, BoxUsedByLatch, InvProof, PrecommitOncePerRoundInv, PTL, SentTimeFrozenInv, SentTimeLeNowInv
DEFS Inv, Spec

\* The existential lift over the bound, the ReachCommute / ReachBoxFO idiom of
\* ...Base. Neither step instantiates the family at a PICKed constant.
LEMMA StairCommute ==
  ASSUME NEW j \in Nat, NEW TEMPORAL D,
         \A b \in Nat : []((Used >= j /\ now <= b) => D)
  PROVE  [](\A b \in Nat : ((Used >= j /\ now <= b) => D))
OBVIOUS

LEMMA StairBoxFO ==
  ASSUME NEW j \in Nat
  PROVE  [](  (\A b \in Nat : ((Used >= j /\ now <= b) => <>(Used >= j + 1)))
              => ((\E b \in Nat : (Used >= j /\ now <= b))
                    => <>(Used >= j + 1))  )
<1>1. (\A b \in Nat : ((Used >= j /\ now <= b) => <>(Used >= j + 1)))
      => ((\E b \in Nat : (Used >= j /\ now <= b)) => <>(Used >= j + 1))
  OBVIOUS
<1> QED
  BY <1>1, PTL

\* NatInduction with HIDE DEF, as RoundGrowth and ClockRegionBreaksAt do. The
\* base is stated as P(0) and not as its unfolded form, or the prover cannot
\* match it after the HIDE.
THEOREM UsedStaircase ==
  ASSUME Spec, []~SomeCorrectDecided, []<>GoodRoundExists,
         []LateValueLockWindow,
         \A p \in Honest : \A r \in Rounds :
           (Lemma5Hyp(p, r) ~> BlockingLockDuring(p, r))
  PROVE  \A j \in Nat : <>(Used >= j)
<1>fr. \A b \in Nat : []<>FreshLowLock(b)
  BY FreshRecurs
<1>inv. []TypeOK
  BY InvProof, PTL DEFS Inv, Spec
<1> DEFINE P(j) == <>(Used >= j)
<1>0. P(0)
  BY <1>inv, BoxUsedGeZero, PTL DEF P
<1>step. \A j \in Nat : P(j) => P(j + 1)
  <2> TAKE j \in Nat
  <2> SUFFICES ASSUME P(j) PROVE P(j + 1)
    OBVIOUS
  <2>ih. <>(Used >= j)
    BY DEF P
  <2>g. [](TypeOK /\ Used >= j => (\E b \in Nat : (Used >= j /\ now <= b)))
    BY BoxGuardExB
  <2>ex. <>(\E b \in Nat : (Used >= j /\ now <= b))
    BY <1>inv, <2>ih, <2>g, PTL
  <2>fam. \A b \in Nat : [](  (Used >= j /\ now <= b) => <>(Used >= j + 1)  )
    BY <1>fr, BoxStaircaseStepAt
  <2>com. [](\A b \in Nat : ((Used >= j /\ now <= b) => <>(Used >= j + 1)))
    BY <2>fam, StairCommute
  <2>fo. [](  (\A b \in Nat : ((Used >= j /\ now <= b) => <>(Used >= j + 1)))
              => ((\E b \in Nat : (Used >= j /\ now <= b))
                    => <>(Used >= j + 1))  )
    BY StairBoxFO
  <2> QED
    BY <2>ex, <2>com, <2>fo, PTL DEF P
<1>all. \A j \in Nat : P(j)
  <2> HIDE DEF P
  <2> QED
    BY <1>0, <1>step, NatInduction, IsaM("blast")
<1> QED
  BY <1>all DEF P

-----------------------------------------------------------------------------
\* ---- Item 11: the assembly -----------------------------------------------
\* The bound in the form that the contradiction needs. j > LowBudget is a
\* CONSTANT hypothesis, so it can sit in the ASSUME of a boxed lemma. The
\* conclusion then names the SAME atom Used >= j that the staircase produces.
\* That is what lets PTL close the contradiction, because ls4 does no
\* arithmetic.
LEMMA BoxUsedBelow ==
  ASSUME NEW j \in Nat, j > LowBudget
  PROVE  [](TypeOK => ~(Used >= j))
<1>1. TypeOK => ~(Used >= j)
  BY LowPairsFinite, UsedLowFacts
<1> QED
  BY <1>1, PTL

\* The disruption cannot recur at every good round: the pairs run out.
THEOREM UndisruptedGoodRoundExists ==
  ASSUME Spec, []~SomeCorrectDecided, []<>GoodRoundExists
  PROVE  UndisruptedGoodRound
<1> SUFFICES ASSUME ~UndisruptedGoodRound PROVE FALSE
  BY PTL
\* ~<>(A /\ []~B) is A ~> B, per pair.
<1>lt. \A p \in Honest : \A r \in Rounds :
         (Lemma5Hyp(p, r) ~> BlockingLockDuring(p, r))
  <2> TAKE p \in Honest
  <2> TAKE r \in Rounds
  <2>1. ~<>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r))
    BY UndisruptedIntro
  <2> QED
    BY <2>1, PTL
\* The window lemma enters HERE and only here, as a cited theorem of
\* ...RoundProgress. Everything above took []LateValueLockWindow as a
\* hypothesis, so the two frontiers stayed separate until this line.
<1>w. []LateValueLockWindow
  BY LateValueLockWindowInv
<1>st. \A j \in Nat : <>(Used >= j)
  BY <1>lt, <1>w, UsedStaircase
<1>inv. []TypeOK
  BY InvProof, PTL DEFS Inv, Spec
<1>bd. LowBudget \in Nat
  BY LowPairsFinite
\* The temporal consumption happens INSIDE the TAKE, so <1>no's body is
\* NON-temporal and the final step may instantiate it at the compound term
\* LowBudget + 1. Instantiating the staircase itself there would NOT work: a \A
\* over a temporal body survives no instantiation at a compound term.
<1>no. \A j \in Nat : ~(j > LowBudget)
  <2> TAKE j \in Nat
  <2> SUFFICES ASSUME j > LowBudget PROVE FALSE
    OBVIOUS
  <2>1. <>(Used >= j)
    BY <1>st
  <2>2. [](TypeOK => ~(Used >= j))
    BY BoxUsedBelow
  <2> QED
    BY <1>inv, <2>1, <2>2, PTL
<1> QED
  BY <1>bd, <1>no

-----------------------------------------------------------------------------
\* ---- The export -----------------------------------------------------------
\* The SUFFICES is the composition module's own idiom: (([]~D) => <>D) => <>D
\* is propositionally valid, and it is what hands the export its no-decision
\* hypothesis.
\*
\* <1>all is a \A over a temporal body. It is PRODUCED by TAKE (works) and
\* CONSUMED in a hypothesis position of a cited rule (works). No step
\* instantiates it at a PICKed constant, which is the operation that does not.
THEOREM LockRetryDecides ==
  ASSUME Spec, []<>GoodRoundExists
  PROVE  <>SomeCorrectDecided
<1> SUFFICES ASSUME []~SomeCorrectDecided PROVE <>SomeCorrectDecided
  BY PTL
<1>ex. UndisruptedGoodRound
  BY UndisruptedGoodRoundExists
<1>all. \A p \in Honest : \A r \in Rounds :
          (<>(Lemma5Hyp(p, r) /\ []~BlockingLockDuring(p, r))
             => <>SomeCorrectDecided)
  BY QuietRoundDecides
<1> QED
  BY <1>ex, <1>all, UndisruptedElim
=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)