# Tendermint agreement proof

This document describes the TLAPS proof that honest Tendermint validators
cannot decide different values at one consensus height.

## Result

The most concrete specification is `TendermintPartialSync.tla`. Its agreement
theorem is:

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

`TendermintVoting.tla` retains only proposals, votes, locks, and decisions.
Operational round and step state is removed. Guards directly encode vote
uniqueness, the requirement that a precommit follows a prevote quorum, and the
proof-of-lock rule.

`TendermintVotingProofs.tla` establishes:

1. A decision has a corresponding precommit quorum.
2. A precommit quorum has a corresponding prevote quorum, called a polka.
3. `PolkaDescent` prevents a higher-round polka from changing value above an earlier precommit quorum.
4. `PrecommitQuorumAgreement` follows across all rounds.
5. `AgreementInv == Spec => []Agreement` follows from decision certificates and precommit quorum agreement.

The cross-round step uses course-of-values induction. This is the formal
lock-chain argument corresponding to the Tendermint paper's safety reasoning.

## Protocol refinement

`TendermintOperational.tla` adds per-validator rounds, protocol steps,
proposal handling, valid values, and round advancement. It remains all honest
and uses symbolic quorums.

`TendermintOperationalRefinement.tla` maps `sent`, `locked`, and `decision`
directly to the voting specification. Operational state not visible in the
voting layer maps to stuttering. The module proves:

```tla
THEOREM AgreementInv == Spec => []Agreement
```

## Byzantine refinement

`TendermintByzantine.tla` adds faulty validators, Byzantine quorums, designated
proposers, and a permissive faulty action.

`TendermintByzantineRefinement.tla` projects the behavior onto honest validator
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

`TendermintPartialSync.tla` adds concrete quorum cardinalities, timers,
per-validator received sets, message delivery, GST, Delta, and a numeric
clock.

`TendermintPartialSyncRefinement.tla` projects timer, delivery, and clock
state away. Its invariant proves that each honest received set is a subset of
the derived global message pool. Monotonicity then maps local-message guards
to the matching global guards in `TendermintByzantine.tla`.

This final refinement establishes Agreement for the paper-level protocol model.

## Assumptions

The proof depends on:

* A nonempty validator set and at least one honest validator.
* An application validity predicate over proposed values.
* Authenticated senders, so faulty validators cannot forge honest votes.
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
