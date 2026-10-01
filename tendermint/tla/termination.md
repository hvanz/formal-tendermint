# Termination proof

This document describes the proof of Termination: every correct validator eventually decides in a Tendermint height.
The proof follows Section IV of the paper [The latest gossip on BFT consensus][tendermint-paper], Lemmas 5 to 7.
This document refers to version 3 of the paper on arXiv, of 22 November 2019.

The paper writes "correct process", and the specifications write "honest validator".
This document uses the two terms with the same meaning.
In this document, `...X` is the module or configuration `TendermintPartialSyncTerminationX`.

## Result

The theorem is about `TendermintPartialSync`, the most concrete specification.
It is in the module `TendermintPartialSyncTermination`:

```tla
THEOREM TerminationThm == Spec => Termination
```

The property has a condition:

```tla
Termination == TerminationConditions => (\A p \in Honest : <>(decision[p] # nil))

TerminationConditions == EveryHonestProposesAgain
```

`EveryHonestProposesAgain` says that, for each round bound, each honest validator is the proposer of a round above that bound.
Thus each honest validator is the proposer of an infinite number of rounds.
A Byzantine proposer can stay silent, so one honest proposer round is not sufficient.
The proof selects one correct validator, and it needs that validator to be a proposer again after each new lock.
The weighted round-robin proposer function of the paper satisfies this condition.

`Spec` includes weak fairness on each honest action, on each delivery action, and on `Tick`.
The proof has no assumption on the timeout constants, other than that each constant is positive.
The only assumption on `Delta` is `Delta > 0`.
No proof step is `OMITTED`, and the termination modules add no `ASSUME` and no `AXIOM`.

## Proof outline

`TerminationThm` has three steps:

1. `Lemma7Selection` shows that eventually one correct validator decides. This is paper Lemma 7.
2. `DecisionPropagates` shows that one correct decision leads to the decision of each correct validator.
3. `AllDecidedLeadsToEach` puts the result in the form of `Termination`, with one formula for each validator.

The tree below shows the main theorems under `TerminationThm`.
A theorem with no module name is in the composition module, `TendermintPartialSyncTermination`.

```text
TerminationThm
|-- Lemma7Selection                        paper Lemma 7
|     |-- ProposerRecurrenceL              from EveryHonestProposesAgain
|     |-- TimeoutsSufficientBeyondL        clause (4) of Lemma 5 at each round r >= 2 * Delta
|     |-- PostGSTRoundProgress             ...RoundProgress, with ...NonZeno
|     |-- GoodRoundRecurrence
|     |     |-- DominatorExists            ...Dominator, with paper Lemma 6 in ...CrossRound
|     |     `-- GoodRoundFromDominator
|     |           |-- SelectedEntryRecurs  ...Selection
|     |           `-- LateEntryInvThm      the late entry at each round r > GST
|     |-- RecurringResolution              paper Lemma 5, in ...Cascade
|     `-- LockRetryTerminates              ...LockRetry
|-- DecisionPropagates
`-- AllDecidedLeadsToEach                  ...WithinRound
```

A good round is a round `r` with a state that satisfies the hypotheses of Lemma 5, `Lemma5Hyp(p, r)`, for a correct validator `p`.
`GoodRoundExists` is true at such a state.
`Lemma7Selection` has three parts:

1. `GoodRoundRecurrence`: eventually a correct validator decides, or good rounds occur an infinite number of times.
2. `RecurringResolution`: if good rounds occur an infinite number of times, then eventually a correct validator decides, or a correct validator locks a value after GST.
   This part uses Lemma 5.
3. `LockRetryTerminates`: if good rounds occur an infinite number of times, then eventually a correct validator decides.

Parts 2 and 3 follow the two cases of the paper proof.
`LockRetryTerminates` also has the premise that a correct lock occurs after GST.
Its proof does not use that premise, because `LockRetryDecides` needs only the recurrence of good rounds.

The sections below describe the model first.
Then they describe Lemmas 5, 6 and 7, in the order of the paper.
The last sections describe the supporting results, the differences from the paper, and the assumptions.

## The model

This section describes the parts of `TendermintPartialSync` that the termination proof uses.

### Clock and messages

* `now` is a clock with values in `Nat`. Only `Tick` changes it, and `Tick` adds 1.
* `sentTime[m]` records the time when message `m` became available.
  For an honest sender, this is the time of the send.
  For a faulty sender, this is the time when a correct validator receives `m` for the first time. `FaultyStep` sets it.
* `sent` is the set of messages with a `sentTime`, and `rcvd[p]` is the set of messages that `p` received.
* `DeliveryDeadline(m)` is the later one of `sentTime[m]` and `GST`, plus `Delta`.
* `Deliver(p)` is batched. One step gives `p` all the messages that are available to `p`.
* `enteredAt[p][r]` records the time when `p` entered round `r`.
  It is a history variable.
  Thus "the first correct validator to enter round `r` at time `t`" is a state predicate, `FirstToEnter(p, r)`.

`Tick` has three guards:

1. An event depends on time: a message is not delivered yet, or a live timer has not expired.
2. No honest validator can do a computation step. The specification calls this guard maximal progress.
3. The clock is before the delivery deadline of each pending message.

The proof uses maximal progress in many places.
While an honest validator can do a step, the clock does not change.
Thus several clock bounds are state invariants, and not facts about the future.

The `sentTime` of a faulty message is the time of its first correct receipt.
Thus the delivery deadline also applies to faulty messages.
This gives the second part of the Gossip property of the paper.
A message that one correct validator receives also reaches each other correct validator within the same bound.

### Delta

`Delta` is the paper's Δ.
After GST, a message sent at time `t` reaches each correct validator at or before the later one of `t` and `GST`, plus `Delta`.
The reason is that `Tick` can reach the deadline of a pending message, but it cannot pass it.

The only assumption on `Delta` is `Delta > 0`.
With `Delta = 0`, a message sent after GST at the current time has its deadline at `now`.
That message then blocks `Tick`.
A faulty validator that sends a new message after each delivery then stops the clock.
No timeout expires, and Termination is false.
The proof uses `Delta > 0` in one lemma only, `EmptyFrontierDeadlineOk` in `...RoundProgress`.

### Timeouts

For each step X of propose, prevote and precommit, the timeout of round `r` is `T0X + r * TDelta`.
The paper uses the same form, `timeoutX(r) = initTimeoutX + r * timeoutDelta`.
Each of the four constants is a positive natural number.

### Fairness

`Spec` has weak fairness on each of the 13 honest actions, for each honest validator.
`SkipRound` has weak fairness for each round.
`Deliver(p)` has weak fairness for each honest `p`, and `Tick` has weak fairness.
Faulty validators have no fairness.

The specification does not add weak fairness on the disjunction of the honest actions of a validator.
`...NonZeno` derives the progress fact that the proof needs from the separate conditions.

### Quorums

There are `3 * f + 1` validators, and at most `f` of them are faulty.
Each validator has one vote.
A quorum has at least `2 * f + 1` validators, and a weak quorum has at least `f + 1` validators.
The termination proof uses `QuorumAvailable`: a quorum exists that contains only honest validators.

## Lemma 5: one good round

### The paper statement

Paper Lemma 5 has four hypotheses:

1. A correct process `p` is the first correct process to enter a round `r > 0`, at a time `t > GST`.
   At time `t`, each correct process is at round `r` or lower.
2. The proposer `q` of round `r` is correct.
3. At time `t`, the locked round of each correct process is at or below the valid round of `q`.
4. `timeoutPropose(r) > 2Δ + timeoutPrecommit(r - 1)`, `timeoutPrevote(r) > 2Δ` and `timeoutPrecommit(r) > 2Δ`.

The conclusion is that all correct processes decide in round `r` before `t + 4Δ + timeoutPrecommit(r - 1)`.

### The formal hypotheses

`Lemma5Hyp(p, r)`, in `...Base`, has these conjuncts:

* Clause (1): `now > GST`, `r > 0` and `FirstToEnter(p, r)`.
  `FirstToEnter(p, r)` says three things.
  `p` entered `r` at the current time.
  No correct validator is above round `r`.
  No correct validator entered `r` at an earlier time.
* Clause (1), the late entry: `now >= GST + TimeoutPrecommit(r - 1)`.
  The paper does not have this conjunct.
* Clause (2): `Proposer[r]` is honest.
* Clause (3): the lock round of each correct validator is at or below `valid[Proposer[r]].round`.
* Clause (4), `Lemma5Timeouts(r)`: each of the three timeouts of round `r` is above `2 * Delta`.

The hypotheses do not say that no correct validator has decided.
A decision before the good round already satisfies the conclusion.

### The late entry

Formal clause (4) is shorter than paper clause (4).
The propose timeout must be above `2 * Delta` only.
The late-entry conjunct gives the difference.

Let `e` be the entry time of `p` into `r`.
`CrossingBacked` dates a precommit quorum of round `r - 1` at or before `T = e - TimeoutPrecommit(r - 1)`.
The late entry makes `T` a time at or after GST.
Each correct validator then receives the quorum by `T + Delta`.
It then enters round `r` by `T + Delta + TimeoutPrecommit(r - 1)`, which is `e + Delta`.
Thus the entry spread of round `r` is `Delta`.

Without the late entry, the quorum can be sent before GST and delivered at `GST + Delta`.
The entry spread is then `Delta + TimeoutPrecommit(r - 1)`.
The paper adds this term to the propose timeout inequality instead.

Lemma 7 proves the late entry at each round `r > GST` (`EntryLateAfterGST`, `FirstEntryLateAfterGST`).
Thus the late entry is not an assumption on the environment.
The precommit quorum of round `r - 1` has a correct member `h`.
`h` sent its precommit after it entered round `r - 1`.
A validator enters round `r - 1` at a time at or above `r - 1` (`EntryTimeGeRound`), and `r - 1 >= GST`.

The two forms of clause (4) are different at high rounds.
With the timeouts of the paper, `timeoutPropose(r) - timeoutPrecommit(r - 1)` is `T0Propose - T0Precommit + TDelta` at each round.
Thus the paper inequality is true at all rounds, or at no round.
The formal clause (4) is true at each round `r >= 2 * Delta`, for all positive constants (`TimeoutsSufficientBeyond`).

The model `...EntrySpreadMC`, with the configuration `...EntrySpreadCounterexample`, shows why the late entry is necessary.
The run uses `Delta = 2`, `GST = 6` and `T0Precommit = 6`:

1. The round-0 precommit quorum is sent at `now = 1`, before GST.
2. Two correct validators enter round 1 at `now = 7`.
   Round 1 satisfies the paper hypotheses with the formal clause (4).
3. The propose timers of these two validators expire at `now = 12`, before the proposer enters round 1.
4. All correct validators precommit nil in round 1, so round 1 does not decide.

The late entry is false in this run, because `7 < GST + TimeoutPrecommit(0) = 12`.

### The formal conclusion

`Lemma5OrBlockingLock`, in `...Cascade`, says this.
After a state that satisfies `Lemma5Hyp(p, r)`, eventually a correct validator decides, or `BlockingLockDuring(p, r)` becomes true.

The formal conclusion differs from the paper conclusion in three points:

* It needs one correct decision, not the decision of all correct validators.
  `DecisionPropagates` gives the other decisions.
* It has no time bound.
  The proof uses time bounds, but only in its internal steps.
* It has a second branch, the blocking lock.

`BlockingLockDuring(p, r)` has these parts:

* The round-`r` proposal has the value `v` and the valid round `vr`.
* A correct validator `c` sent a precommit for a value `w` different from `v`, at a round `lr` with `vr < lr < r`.
* `c` sent this precommit at or after the entry time of `p` into `r`.

A lock of this type makes `c` refuse the proposal.
The guard of `OnProposalWithPOL` accepts the proposal only in two cases.
The lock round of `c` is at or below `vr`, or the locked value of `c` is `v`.

**Why the second branch is necessary.**
The published statement is false in this model.
A message from a faulty validator can reach a correct validator for the first time after the hypothesis state.
That message can complete a polka below round `r`, and a correct validator then locks at that round.
Clause (3) is true at the hypothesis state only, and the new lock makes it false.
The configuration `...WithinRoundPhase2LockShiftCounterexample` of `...WithinRoundMC` shows this run:

1. `h1` enters round 1 at `now = 3`, and it proposes `b` with the valid round `-1`.
2. At the same time, the faulty validator sends an equivocating prevote for `a` at round 0 to `h3`.
   This prevote completes a round-0 polka for `a`.
3. `h3` locks `a` at round 0.
   It then refuses `b`, and it prevotes nil in round 1.
4. The prevote stage of round 1 does not occur, and no correct validator decides.

The configuration `...WithinRoundPhase2Repaired` checks the same run with the lock branch in the conclusion.
TLC finds no violation there.
The paper handles locks of this type in case 2 of Lemma 7, with Lemma 6.
But the paper proof considers only locks in rounds before the good round.
The lock of this run occurs after the first correct entry into `r`, while another correct validator is still below `r`.

**Why the lock is dated from the entry.**
`BlockingLockDuring(p, r)` needs a lock dated at or after the entry into `r`.
A weaker form, `PostGSTPriorRoundLock(r)`, needs only a correct lock below `r` that was sent after GST.
After one such lock exists, `PostGSTPriorRoundLock` is true at each later round.
A new good round then gives no new information to the retry of Lemma 7.
With the date from the entry, only a new lock can stop a later good round.
The configuration `...WithinRoundLockRelativize` shows the difference.
At the entry into round 2, the round-0 lock satisfies `PostGSTPriorRoundLock(2)`.
But it does not satisfy `BlockingLockDuring("h1", 2)`.

The comparison is "at or after", and not "after".
Maximal progress can put the lock and the entry at the same time, as at `now = 3` in the run above.
The configuration `...WithinRoundBlockingLock` shows that the branch can occur.
It also shows that the strict form does not occur in the same run.

**Corollaries.**
`Lemma5OrPriorLock` replaces the blocking lock with `PostGSTPriorRoundLock(r)`.
The blocking lock is dated at or after `e`, and `e > GST`.
`Lemma5ResolutionExists` applies the corollary to each good round.
`RecurringResolution`, in the composition module, uses it.

### The proof

The modules call the proof of Lemma 5 "the cascade".
The cascade is in five modules:

| Module                 | Content                                                                              |
|------------------------|--------------------------------------------------------------------------------------|
| `...WithinRound`       | The definitions of the outcomes, for example `BlockingLockDuring`, and decide lemmas |
| `...CascadeInvariants` | The vocabulary, the global invariants, the case split and `QuorumDecides`            |
| `...CascadeRegion`     | The bound on the proposal, `ProposalReached`, three latches and `ClockUnbounded`     |
| `...CascadeCore`       | The dates of correct votes, and the joint induction `CascadeCoreLatch`               |
| `...Cascade`           | `QuorumReached`, `EarlyQuorumReached`, `Lemma5OrBlockingLock` and its corollaries    |

**The case split.**
Let `q` be `Proposer[r]`.
At the hypothesis state, one of two cases is true (`Lemma5HypSplitBox`):

* Case A (`CaseA`): each round-`r` proposal of `q` has a valid round `vr` at or above `valid[q].round`.
  Then clause (3) also bounds each correct lock by `vr`.
* Case B (`EarlyPolka`): a polka for a valid value exists at round `r`, with all its prevotes dated between GST and `e`.

Case B is necessary for this reason.
`q` can enter `r`, propose, and increase its valid round at one clock value, before the hypothesis state.
Then `valid[q].round = r`, and a round-`r` polka already exists at time `e`.

**Case A: the stages.**
The table gives the stages of Case A.
`v` is the value of the round-`r` proposal.

| Time                  | Fact                                                                                                                                | Lemma                                       |
|-----------------------|-------------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------|
| `e + Delta`           | Each correct validator that has not decided is at round `r` or above. The round-`r` proposal is sent.                               | `AllAboveEntryRound`, `ProposalDated`       |
| `e + 2 * Delta`       | No correct validator is at round `r` in step "propose". Each correct nil prevote at round `r` is dated at or before this time.      | `ProposeExitByDeadline`, `NilPrevoteInWindow` |
| `e + 3 * Delta`       | Each correct validator prevoted for `v` at or before this time, or an escape is true.                                               | clause P of `CascadeCore`                   |
| after `e + 4 * Delta` | Each correct validator precommitted `v`, or an escape is true.                                                                      | clause Q of `CascadeCore`                   |
| later                 | A correct validator decides.                                                                                                        | `QuorumDecides`                             |

`e + Delta` is `CascadeCeiling(p, r)`, and `e + 2 * Delta` is `CascadeDeadline(p, r)`.
An escape, `CascadeEscape(p, r, v)`, is one of three facts.
A correct validator decided, a blocking lock occurred, or a precommit quorum for `v` exists at round `r`.
Each escape leads to the conclusion of the lemma.

**The timeout inequalities.**
Each inequality of clause (4) excludes one way to leave the stages:

* `TimeoutPropose(r) > 2 * Delta`.
  The propose timer of a correct validator expires after `e + 2 * Delta`.
  Before that time, the validator receives the proposal and prevotes on it.
* `TimeoutPrevote(r) > 2 * Delta`.
  A nil precommit on the prevote timeout needs a prevote quorum that is dated a full `TimeoutPrevote(r)` earlier.
  At that earlier date, clauses P and Q give an escape.
* `TimeoutPrecommit(r) > 2 * Delta`.
  A correct validator above round `r` sent its round-`r` precommit a full `TimeoutPrecommit(r)` earlier.
  Clause N makes that precommit a precommit for a value, and clause Q then gives a quorum.

**The joint induction.**
`CascadeCore(p, r)` has three clauses for each correct validator `c`, value `v` and time `T`:

* P: assume that the proposal for `v` is justified at a time `T` at or after GST and `e`, and that `now > T + Delta`.
  Then `c` prevoted for `v` at or before `T + Delta`, or an escape is true.
* N: assume that the proposal for `v` is justified at a time `T` at or after GST and `e`.
  Then `c` did not precommit nil at round `r`, or an escape is true.
* Q: assume that a polka for `v` is dated at a time `T` at or after GST, and that `now > T + Delta`.
  Then `c` precommitted `v` at round `r`, or an escape is true.

"Justified at `T`" means that the round-`r` proposal for `v` is sent at or before `T`.
If the proposal has a valid round, the polka of that round is also sent at or before `T`.
Clause P also needs `e + Delta <= T + Delta`.

The proof shows the three clauses together, as one inductive invariant (`CascadeCoreLatch`).
Each clause uses another clause, or itself, at an earlier time, so the induction is not circular.
At the entry state, `now = e`, and no correct validator has voted at round `r`.
The proof shows the three clauses at the entry state from these two facts.
Only `Tick` can make clause P or clause Q false.
The proof of that case uses maximal progress and the deadline guard of `Tick`.

**Latches.**
Some facts of the cascade become true only at the hypothesis state.
A latch is a theorem of the form "after `H` is true, `X` stays true".
A latch does not give `X` before `H`.
Thus the proof carries each such fact as a conjunct of the premise of each stage.
The latched facts are:

* `LocksDominateOrDated`: each correct lock satisfies clause (3), or it is dated at or after `e`.
* `NilPrevoteBlocks`: a correct nil prevote at round `r`, dated at or before `e + 2 * Delta`, gives a blocking lock.
* `CascadeCore`, `RoundOrigin` and `WRDurable`.
  `WRDurable(r)` holds the conditions of Lemma 5 that do not change, for example `now >= GST` and clause (4).

**Stages without the WF1 rule.**
The proof does not use the WF1 rule for the stages.
Each stage bounds a time by a constant `b`, and `ClockUnbounded` moves the clock past `b`.
`ClockUnbounded` says this: if no correct validator decides, then for each `b`, eventually `now > b` stays true.
Thus the cascade proof assumes that no correct validator decides.
`Lemma5OrBlockingLock` then removes this assumption, because a decision is already a conclusion.

**Case B.**
At `e + Delta`, no correct validator is below round `r`, and no correct validator is at round `r` in step "propose" or "prevote".
`EarlyPolkaNoNil` excludes correct nil precommits at round `r`.
`EarlyPolkaAbove` says that each correct validator above round `r` precommitted `v`.
Thus each correct validator that has not decided precommitted `v`.
The correct validators form a quorum, by `QuorumAvailable`, so a precommit quorum for `v` exists (`EarlyPolkaGivesQuorum`).
Case B does not use `CascadeCore`, because `NilPrevoteBlocks` is false in Case B.

**The decision.**
`QuorumDecides` goes from the decision evidence of round `r` to a correct decision.
The evidence is the round-`r` proposal for a valid value `v`, and a precommit quorum for `v`.
The proof has two WF1 steps for one correct validator `c`.
First, `Deliver(c)` gives `c` the evidence.
Then `OnPrecommitQuorumValue(c)` decides.
The decision action has no guard on the round, so a validator that left round `r` also decides.

## Lemma 6: a high lock reaches all correct validators

### The paper statement

Assume that a correct process locks a value `v` in round `r`, at a time `t0 > GST`, and that `timeoutPrecommit(r) > 2Δ`.
Then each correct process sets its valid value to `v` and its valid round to `r` before it starts round `r + 1`.

### The formal statement

The module `...CrossRound` holds paper Lemma 6.
No operator has the name `Lemma6`.
The lemma has two invariants, and the proof of each one uses `Spec` and `TimeoutsSufficientBeyond`:

* `ValidCatchUp` is the inductive form.
  Take a correct precommit for a value, at a round `rr` above `DomCeiling`, which is `2 * Delta + GST`.
  Assume that a correct validator that has not decided has a valid round below `rr`.
  Then no correct validator is above round `rr`.
  Also, `now` is at or before the send time of the precommit plus `Delta`.
* `HighLockCatchUp` is the form that other modules use.
  After the send time of such a precommit plus `Delta`, each correct validator has a valid round at or above `rr`, or it has decided.

A high lock is a correct precommit for a value, at a round above `DomCeiling`.
The round alone gives the two premises of the paper:

* A precommit of round `rr` is sent at a time at or above `rr` (`PrecommitRoundLeSendTime`).
  Thus a high lock is sent after GST.
* `rr >= 2 * Delta`, so `TimeoutsSufficientBeyond` gives `TimeoutPrecommit(rr) > 2 * Delta`.

### Why an invariant

The paper gives Lemma 6 as a statement about time.
The formal proof gives it as a state invariant.
The reason is maximal progress.
At the time `sentTime + Delta`, each correct validator has the evidence of the lock, which is the proposal and the polka.
A correct validator with a lower valid round can then update its valid record.
That update is a computation step, so `Tick` is disabled.
Thus the clock cannot pass `sentTime + Delta` while a correct validator has a lower valid round.

### The proof

`ValidCatchUpStepL` does an induction on the steps, with these cases:

* A new high precommit.
  Assume that a correct validator is already above round `rr` when the precommit is sent.
  `LateValueLockGap` then gives `TimeoutPrecommit(rr) <= Delta`.
  This is false, because `TimeoutPrecommit(rr) > 2 * Delta`.
* An old precommit, and the round bound.
  A correct validator can leave round `rr` with `SkipRound` or with `OnTimeoutPrecommit`.
  `SkipRound` needs messages from `f + 1` validators at a higher round, so a correct validator is already above `rr`.
  The induction hypothesis excludes this.
  `OnTimeoutPrecommit` at `rr` needs an expired precommit timer.
  `HighLockPrecommitTimerGap` shows that this timer expires after `sentTime + Delta`.
* An old precommit, and the clock bound.
  Only `Tick` changes `now`.
  At the deadline, a correct validator with a lower valid round can do a step, so `Tick` is disabled (`OldCatchUpDeadline`).

### The difference from the paper

Formal Lemma 6 is only for high locks.
The configuration `...FrontierCounterexample` of `...InterfaceMC` shows that a lock after GST does not bound the correct rounds.
In that run, `v2` reaches round 1 before GST, and `v1` locks at round 0 after GST.
A proposed hypothesis of Lemma 6 said that each correct validator is at or below the round of the lock.
The run makes this hypothesis false.
`ValidCatchUp` proves the round bound for high locks, and it does not assume it.
The dominator proof handles the low locks.

## Lemma 7: good rounds recur

### The paper statement

Let `r0` be the highest round that a correct process started at GST.
Assume that a correct process `p` has this property.
For each correct `c`, the locked round of `c` is at or below the valid round of `p`.
Assume also that `p` is the proposer of a round `r1 > r0`.
The paper writes `r1 > r`, and this document reads it as `r1 > r0`.
The proof has two cases:

1. No correct process locks a value in a round from `r0` to `r1 - 1`.
   Then round `r1` satisfies the hypotheses of Lemma 5, and all correct processes decide in round `r1`.
2. A correct process locks a value in a round of that range.
   Let `r2` be the highest such round, and let `q` be a process that locks in `r2`.
   By Lemma 6, at the end of round `r2`, the valid round of each correct process is `r2`.
   Its valid value is the locked value of `q`.
   Then round `r1` satisfies the hypotheses of Lemma 5.

The paper proof does not show these facts:

* A process `p` with the property above exists.
  Section III-A of the paper gives only an informal reason.
* Clause (4) of Lemma 5 is true at round `r1`.
* The premise `timeoutPrecommit(r2) > 2Δ` of Lemma 6 is true.
* The correct processes reach round `r1` when no process decides.
* No lock occurs during round `r1`, after the first correct entry.
  The Lemma 5 section shows a run with such a lock.

The formal proof proves each of these facts, or it handles the case in a different way.

### The formal statement

`Lemma7Selection` says this: under `Spec` and `TerminationConditions`, eventually a correct validator decides.
Its proof first derives three facts:

* `ProposerRecurrence`, from `EveryHonestProposesAgain`: each honest validator is the proposer of a round above each bound.
  The configuration `...ProposerCounterexample` of `...InterfaceMC` shows why an older condition was not sufficient.
  In that run, `v1` is always the proposer.
  The old condition, "an honest validator is a proposer an infinite number of times", is true.
  But `v2` and `v3` are never proposers, so `EveryHonestProposesAgain` is false.
* `TimeoutsSufficientBeyond`: each round `r >= 2 * Delta` satisfies clause (4).
  Each timeout of round `r` is at least `1 + r * TDelta`, and `r * TDelta >= r >= 2 * Delta`.
  The configuration `...ShortTimeoutCounterexample` of `...InterfaceMC` shows why clause (4) is necessary.
  Round 0 has a correct proposer, but the propose timers expire before the proposal arrives.
  Round 1 does not satisfy the precommit inequality of clause (4).
  TLC reports that the old Termination formula is false on this bounded run.
* `ProgressBeyond`, from `PostGSTRoundProgress`: for each round bound `b`, eventually a correct validator decides, or `now > GST` and a correct validator is above round `b`.

The proof then uses the three parts of the outline: `GoodRoundRecurrence`, `RecurringResolution` and `LockRetryTerminates`.

### The dominator

Clause (3) of Lemma 5 needs a proposer whose valid round is at or above each correct lock.
The formal proof uses one fixed correct validator `d`, and it needs this property only at fresh entries:

* A fresh entry into round `r`, `FreshEntry(r)`, is a state with two properties.
  A correct validator `p` satisfies `FirstToEnter(p, r)`.
  Each correct lock is below round `r`.
* `EntryDominator(d)` says: at each fresh entry after GST, each correct lock round is at or below `valid[d].round`.
* `StableEntryDominator`, in `...Dominator`, says this.
  Eventually a correct validator decides, or for some correct `d`, `EntryDominator(d)` is eventually always true.

Two shorter forms of this property are false:

* "Each correct validator eventually always has a valid round at or above each correct lock."
  This is false when locks occur again and again.
  A lock changes `locked[c]` in one step, and the other correct validators update their valid records later.
* "The proposer of each entered round dominates."
  This is false when one correct validator is always behind.
  A validator that skips over a lock round never updates its valid record for that round.
  But that validator is still a proposer an infinite number of times.

The proof of `StableEntryDominator` has two cases, for the maximum correct lock round:

* The high case: eventually a correct lock round is above `DomCeiling`.
  The maximum lock round `L` then stays above `DomCeiling`.
  At each fresh entry into a round `r` after GST, `L < r`.
  `LateValueLockGap` and `TimeoutPrecommit(L) > 2 * Delta` show that the delivery deadline of the lock has passed.
  `HighLockCatchUp` then gives a valid round at or above `L` to each correct validator that has not decided.
  Thus each correct validator satisfies `EntryDominator`.
* The low case: no correct lock round is ever above `DomCeiling`.
  Assume that no correct validator is a stable dominator.
  Then each correct validator fails to dominate at an infinite number of fresh entries.
  `MaxLockStaircase` shows by induction on `j` that eventually the maximum lock round is at least `j - 1`.
  For the step, take a validator `q` that holds the maximum lock.
  Its valid round is at or above its lock round (`LockedLeValid`), and this stays true.
  The next failure of `q` is a lock above `valid[q].round`, so the maximum lock round is then at least `j`.
  At `j = DomCeiling + 2`, the maximum lock round is above `DomCeiling`.
  This contradicts the low case.

`DominatorExists`, in the composition module, gives `SomeStableDominator` when no correct validator decides.

### The selection of a good round

`SelectedEntry(d)`, in `...Selection`, is a fresh entry into a round `b` with these properties:
`Proposer[b] = d`, `b > 0`, `b > GST`, `now > GST`, and clause (4) at `b`.
`SelectedGoodRoundBox`, in the composition module, shows that `LateEntryInv`, `SelectedEntry(d)` and `EntryDominator(d)` together give `GoodRoundExists`.

The fresh entry is a step, not a state that the proof must reach.
The first step that sets `enteredAt[c][b]` for a correct `c` gives a fresh entry in its next state.
Only `OnTimeoutPrecommit` and `SkipRound` set `enteredAt`, and neither action changes `now` or `locked`.
Before that step, no correct validator is in round `b`, so each correct lock is below `b`.

The lock clause of `FreshEntry` is necessary.
Several correct validators can enter round `b` at one clock value, and one of them can lock at `b` at that clock value.
Clause (3) would then need `valid[d].round >= b`, and no argument gives that.

`GoodRoundFromDominator` shows that good rounds recur:

1. For each round bound, take a round `b` above the bound plus `2 * Delta + GST`, with `Proposer[b] = d`.
   `ProposerRecurrence` gives such a round.
2. Then `b > GST` and `b >= 2 * Delta`, so clause (4) is true at `b`.
3. `ProgressBeyond` moves a correct round above `b`.
   The first entry into `b` is then a fresh entry (`SelectedEntryFromBound`).
4. `SelectedEntryRecurs` combines the results for all bounds.
   At each state, `now` is a bound on each correct round (`RoundBelowNowInv`).

`SelectedEntryFromBound` is for one constant bound.
TLAPS cannot instantiate a universal quantifier whose body is a temporal formula.
Thus the loop over the bounds is in the composition module, where the bound is a `NEW` parameter of a theorem.

### Case 2: the lock retry

The paper takes the highest lock round `r2` before `r1`, and it uses Lemma 6.
The formal proof does not do this.
It uses a retry.
Good rounds occur again and again, and each good round gives a decision or a blocking lock.
`LockRetryDecides`, in `...LockRetry`, shows that blocking locks can stop only a finite number of good rounds.
The argument has four steps:

1. The blocking lock of a good round is at a low round.
   `LateValueLockWindow` and `DisruptionRoundCeilingWithGST` give a lock round at or below `Delta + GST`, which is `LockCeiling`.
2. Each pair of a correct validator and a round has at most one lock.
   A correct validator sends at most one precommit in each round (`PrecommitOncePerRound`).
   The `sentTime` of a sent message does not change (`SentTimeFrozenInv`).
3. If no correct validator decides, the clock passes each bound (`ClockUnbounded`).
   Thus good rounds occur with entry times after each bound `b`.
   The blocking lock of such a round is dated after `b`.
   It therefore uses a pair that no lock dated at or before `b` uses.
4. The set of low pairs, `Honest \X (0 .. LockCeiling)`, is finite.
   But step 3 makes the count of used pairs increase without limit (`UsedStaircase`).
   This is a contradiction.
   Thus some good round has no blocking lock, and a correct validator decides in it (`QuietRoundDecides`).

The bound of step 1 comes from this argument.
The entry into a round `r > lr` comes a full `TimeoutPrecommit(lr)` after a precommit quorum of round `lr` (`CrossingBacked`).
That quorum has a correct member `x`.
If `x` sent its precommit after GST, the lock occurs within `Delta` of that precommit (`LateLockDelivery`).
The lock is also at or after the entry, so `TimeoutPrecommit(lr) <= Delta`, and thus `lr <= Delta`.
If `x` sent its precommit before GST, then `lr < GST`.
The reason is that a precommit of round `lr` is sent at a time at or above `lr`.

The second case is necessary, because a message sent before GST can wait until `GST + Delta`.
The configuration `...WithinRoundWindowGst` shows that the first form of `LateValueLockWindow` is false.
That form did not have the disjunct `lr < GST`.
The configuration `...WithinRoundLockRetry` shows a retry that ends.
A round-0 lock stops good round 1, and good round 2 decides twelve time units later.

A measure on the chain of blocking lock rounds does not work.
That chain goes through the valid round of the proposer.
The valid round of a round-`r` proposal can be lower than `valid[Proposer[r]].round` at the entry state.
Thus the chain does not always increase.
The count of pairs reads only `sent`, and not `valid`.

## Supporting results

### The base layer

`...Base` extends `TendermintPartialSyncRefinement`.
Thus the safety results of the refinement proof are available by name.
The termination proof uses `InvProof`, which gives type correctness and `rcvd \subseteq sent`.
It also uses `SentExtend`, `ValidityInv` and other lemmas of the refinement proof.

`...Base` adds these results:

* Clock facts.
  `now` does not decrease.
  After `now >= GST` is true, it stays true (`GSTLatch`).
  Each correct round is at or below `now` (`RoundBelowNowInv`).
* Message facts.
  A sent message stays sent, and its `sentTime` does not change (`SentTimeFrozenInv`).
  Each `sentTime` is at or below `now` (`SentTimeLeNowInv`).
* Decision facts.
  A correct decision has a precommit quorum in `rcvd` (`DecidedBackedByQuorumInv`), and a decision does not change.
* `HonestFinite`, and the definitions of Lemma 5, for example `Lemma5Hyp`.
* The measure `ComputeWork`, for the clock progress.

### Clock progress

`...NonZeno` shows this fact.
At a fixed clock value, if an honest validator can do a computation step, then eventually an honest step occurs.
The proof uses only the weak fairness of each separate action:

* `ComputeWork` is a natural number that encodes three values in lexicographic order.
  The first value decreases when a round increases.
  The second value decreases when a step changes.
  The third value counts the work that remains in the current step, for example a timer that is not scheduled yet.
* Each honest step decreases `ComputeWork`.
  `Deliver` and `FaultyStep` do not change it.
  `Tick` can change it, so the proof uses it only while the clock does not change.
* The 13 `Enabled*` lemmas show that each guard enables its own fair action.
  The `G*NetworkStable` lemmas show that `Deliver` and `FaultyStep` keep each guard true.
* While a guard is true, maximal progress disables `Tick`.
  Thus the guard stays true until an honest step occurs, and weak fairness gives such a step.
* `AggregateComputationFairness` combines the 13 actions and all honest validators.
  While an honest validator can do a step, `ComputeWork` eventually decreases.

### Round progress

`PostGSTRoundProgress`, in `...RoundProgress`, comes from `RoundGrowth`.
`RoundGrowth` says this.
For each bound `b`, eventually a correct validator decides, or a correct validator is above round `b` and above round `GST`.
Then `RoundBelowNowInv` gives `now > GST`.

`RoundGrowth` uses a measure with a constant bound:

1. Assume that no correct validator decides, and that each correct round stays at or below `b + GST`.
2. `Work(b)` is then a natural number with a constant bound.
   It is similar to `ComputeWork`, but it uses a constant round limit and not the clock.
3. `Deliver`, `FaultyStep` and `Tick` do not change `Work(b)`.
   Each honest step decreases it.
4. `HonestStepsRecur` shows that honest steps occur an infinite number of times if no correct validator decides.
5. A natural number cannot decrease an infinite number of times, so this is a contradiction.

`HonestStepsRecur` has three cases:

* An honest validator can do a computation step.
  `AggregateComputationFairness` gives the step.
* No honest validator can do a step, and no timer is live.
  Then a correct validator `c` has not received a quorum certificate of its own round that is in `sent` (`QuiescentTailWitness`).
  `Deliver(c)` stays enabled, and one `Deliver(c)` step gives `c` the certificate.
  Then `c` can do a step.
* No honest validator can do a step, and a live timer expires at a time `t > now`.
  An old message is a message with `sentTime < now`.
  The measure `ClockWork(t)` counts the ticks to `t`, and the correct validators that have not received all old messages.
  `Deliver` steps decrease the second count.
  When no old message is pending, `EmptyFrontierDeadlineOk` shows that each pending message has a deadline above `now`.
  `Tick` is then enabled, and weak fairness gives it.
  At time `t`, the timeout action is enabled.

`EmptyFrontierDeadlineOk` is the lemma that uses `Delta > 0`.
A message sent at `now` has its deadline at `now + Delta`, which is above `now`.

`ClockUnbounded`, in `...CascadeRegion`, comes from `PostGSTRoundProgress` and `RoundBelowNowInv`.
A correct round above `b` gives `now > b`, and `now` does not decrease.

### Decision propagation

`DecisionPropagates`, in the composition module, shows that one correct decision leads to the decision of each correct validator:

1. A correct validator that decided has its proposal (`DecidedBackedByProposal`) and a precommit quorum (`DecidedBackedByQuorum`) in `rcvd`.
2. `rcvd` is a subset of `sent`, so this certificate is in `sent` (`CertInSent`).
   The certificate stays in `sent`, because a sent message stays sent.
3. `Deliver(c)` is batched, so one step gives each correct validator `c` the full certificate.
4. `OnPrecommitQuorumValue(c)` is then enabled, and weak fairness gives the decision.
5. An induction over the finite set `Honest` gives `CertPropagatesAll`.

This part needs no clock bound.
`Deliver` and the decision action have no clock guard.
Each sent message has `sentTime <= now`, so `Deliver(c)` stays enabled until it occurs.

## Differences from the paper

The table lists each difference between the formal proof and the paper.
The last column names the TLC configurations that show why the difference is necessary.
"Fails" marks an expected failure.

| Subject                            | Paper                                                            | Formal proof                                                                                   | Configuration                                                                  |
|------------------------------------|------------------------------------------------------------------|------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| `Delta`                            | No lower bound is stated                                         | `Delta > 0`. With `Delta = 0`, a faulty validator can stop the clock.                          | None                                                                           |
| Proposer function                  | Weighted round-robin                                             | `EveryHonestProposesAgain`, which round-robin satisfies                                        | `...ProposerCounterexample` (fails)                                            |
| Lemma 5, clause (1)                | `t > GST`                                                        | Also the late entry, `now >= GST + TimeoutPrecommit(r - 1)`. Lemma 7 proves it.                | `...EntrySpreadCounterexample` (fails)                                         |
| Lemma 5, clause (4)                | `timeoutPropose(r) > 2Δ + timeoutPrecommit(r - 1)`               | `TimeoutPropose(r) > 2 * Delta`                                                                | `...EntrySpreadCounterexample` (fails)                                         |
| Lemma 5, conclusion                | All correct processes decide in round `r`, before a time bound   | One correct validator decides, or a blocking lock occurs during round `r`. No time bound.      | `...WithinRoundPhase2LockShiftCounterexample` (fails), `...WithinRoundPhase2Repaired` |
| Lemma 5, date of the lock          | Not applicable                                                   | At or after the entry into `r`, not after GST                                                  | `...WithinRoundLockRelativize`, `...WithinRoundBlockingLock`                   |
| Lemma 6, form                      | A statement about time                                           | A state invariant, from maximal progress                                                       | None                                                                           |
| Lemma 6, scope                     | Each lock after GST with `timeoutPrecommit(r) > 2Δ`              | Locks above round `2 * Delta + GST`. The round bound is proved.                                | `...FrontierCounterexample` (fails)                                            |
| Lemma 7, dominator                 | Assumed                                                          | A fixed correct validator that dominates at fresh entries, proved in two cases                 | None                                                                           |
| Lemma 7, clause (4) at `r1`        | Not shown                                                        | Proved at each round `r >= 2 * Delta`                                                          | `...ShortTimeoutCounterexample` (fails)                                        |
| Lemma 7, case 2                    | The highest lock round `r2`, and Lemma 6                         | A retry, with a finite count of low pairs                                                      | `...WithinRoundLockRetry`, `...WithinRoundWindowGst` (fails)                   |
| Round and clock progress           | Not proved                                                       | `...NonZeno` and `...RoundProgress`                                                            | None                                                                           |
| Decision of all correct validators | Part of Lemma 5                                                  | A separate step, `DecisionPropagates`                                                          | None                                                                           |

## Assumptions

The termination proof depends on these assumptions of `TendermintPartialSync`:

* A finite set of `3 * f + 1` validators, with at most `f` faulty validators.
  Each validator has one vote.
* Three quorum facts, stated as `ASSUME`: `ByzQuorumIntersection`, `WeakQuorumHasHonest` and `QuorumAvailable`.
  They follow from the cardinalities by counting, but no TLAPS lemma derives them yet.
  TLC checks them at `f = 1`.
* Authenticated messages.
  `FaultyStep` sends only messages whose sender is faulty.
* A proposer function from rounds to validators, and at least one valid value (`ValidNonEmpty`).
* `Delta > 0`, and `GST` is a natural number.
* Positive timeout constants `T0Propose`, `T0Prevote`, `T0Precommit` and `TDelta`.
* The fairness conditions of `Spec`.
* `TerminationConditions`, which is the premise of `Termination`.

The termination modules add no `ASSUME` and no `AXIOM`.
The model covers one consensus height.
Validator set changes, accountability and application execution are outside the termination theorem.

## How to check the proof

From this directory, run:

```bash
make termination
```

This target checks the 13 termination modules, one after the other.
On the machine that `README.md` gives, it takes about 6.5 hours for 12,892 proof obligations.
`README.md` gives the time and the count for each module.

Do not check the modules in parallel with `-j6`.
Six `tlapm` processes then compete for the processors, and an obligation can fail with a timeout.
Use plain `make termination`, or `-j2`.
If a module that you did not change fails, check that module again, alone.

To check one module, use its target:

```bash
make term-cascade-core
```

To run a TLC configuration, give the model and the configuration:

```bash
make tlc MC=TendermintPartialSyncTerminationInterfaceMC
make tlc MC=TendermintPartialSyncTerminationWithinRoundMC \
  CFG=TendermintPartialSyncTerminationWithinRoundLockRetry
make tlc MC=TendermintPartialSyncTerminationEntrySpreadMC \
  CFG=TendermintPartialSyncTerminationEntrySpreadCounterexample
```

The configurations whose names end in `Counterexample`, and `...WithinRoundWindowGst`, are expected failures.
Run them one at a time.

[tendermint-paper]: https://arxiv.org/abs/1807.04938
