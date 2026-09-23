# Agreement proof

This document describes the proof for Agreement: honest validators
cannot decide on different values in a Tendermint height.

## Result

The most concrete specification is `TendermintPartialSync`.
Its Agreement theorem is:

```tla
THEOREM AgreementInv == Spec => []Agreement
```

Agreement is scoped to honest validators at the Byzantine and partial synchrony layers.
The proof covers Byzantine voters and Byzantine proposers, assuming authenticated messages and the stated quorum intersection facts.

## Proof chain

```text
TendermintVoting <- TendermintOperational <- TendermintByzantine <- TendermintPartialSync
```

`A <- B` means every behavior of `B`, under its refinement mapping, is a behavior of `A`.
Agreement is proved once on `TendermintVoting`, then transferred to `TendermintPartialSync` through three refinement proofs.

## Voting proof

`TendermintVoting` contain only proposals, votes, locks, and decisions.
The validators' round and step state is disregarded.
Guards directly encode vote uniqueness,
the requirement that a `PRECOMMIT` requires a `PREVOTE` quorum,
and the _Proof-Of-Lock_ (PoL) rule.

`TendermintVotingProofs` establishes that:

1. A decision has a corresponding `PRECOMMIT` quorum.
2. A `PRECOMMIT` quorum has a corresponding `PREVOTE` quorum, also known as  a _polka_.
3. `PolkaDescent` prevents a higher-round _polka_ from changing value above an earlier `PRECOMMIT` quorum.
4. `PrecommitQuorumAgreement` follows across all rounds.
5. `AgreementInv == Spec => []Agreement` follows from decision certificates and `PRECOMMIT` quorum agreement.

The cross-round step uses course-of-values induction. This is the formal
lock-chain argument corresponding to the Tendermint paper's safety reasoning.

## Protocol refinement

`TendermintOperational` adds per-validator rounds, protocol steps,
proposal handling, valid values, and round advancement.
It assumes honest validators only and uses symbolic quorums.

`TendermintOperationalRefinement` maps `sent`, `locked`, and `decision`
directly to the voting specification, via the `Refinement` theorem.
`TendermintOperational` adds state variables — round, step, and others — that
do not exist in `TendermintVoting`.
When the operational model takes a step that changes only those variables,
without touching votes, locks, or decisions, the voting layer sees no change.
In TLA+, such a transition maps to a _stuttering step_: a transition where the
abstract state is unchanged.

```tla
THEOREM Refinement == Spec => V!Spec
```

The proof is a per-action simulation.
Each operational action either matches an abstract action or stutters.
`AgreementInv` then follows by temporal logic, since `Agreement` mentions only `decision`, mapped by the identity.
## Byzantine refinement

`TendermintByzantine` adds faulty validators, Byzantine quorums, designated
proposers, and a permissive faulty action.

`TendermintByzantineRefinement` projects the behavior onto honest validator
state:

* Proposals are kept after removing their sender.
* Honest votes are kept.
* Faulty votes are dropped.
* Byzantine quorums project to intersecting honest quorums.

Keeping sender-stripped proposals preserves proposals from Byzantine leaders.
Dropping faulty votes removes equivocation from the abstract behavior. The
resulting honest behavior refines the operational layer
(`TendermintOperational`), the single edge this module proves. Honest-scoped
`AgreementInv` then follows by transitivity along the chain, reusing
the operational module's agreement theorem; no direct edge onto
`TendermintVoting` is needed.

## Partial synchrony refinement

`TendermintPartialSync` adds concrete quorum cardinalities, timers,
per-validator received sets, message delivery, GST, Delta, and a numeric
clock.

`TendermintPartialSyncRefinement` projects timer, delivery, and clock
state away. Its invariant proves that each honest received set is a subset of
the derived global message pool. Monotonicity then maps local-message guards
to the matching global guards in `TendermintByzantine`.

This final refinement establishes `Agreement` for the paper-level protocol model.

## Assumptions

The proof depends on:

* A nonempty validator set and at least one honest validator.
* An application validity predicate `valid()` over proposed values.
* Authenticated messages, so faulty validators cannot forge honest votes.
* Symbolic quorum intersection in the honest layers.
* Honest intersection of Byzantine quorums in the Byzantine layer.
* The concrete `3f+1`, `2f+1`, and `f+1` quorum assumptions in the partial synchrony layer.

The model covers one consensus height. Validator set changes, accountability,
and application execution are outside the agreement theorem.

## Verification

From the repository root:

```bash
make agreement
```

This checks the four proof modules in order. Measured durations and obligation
counts are in [proof-results.md](./proof-results.md).
