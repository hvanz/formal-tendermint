# TLA+ specs and proofs of Tendermint

This repository holds four TLA+ specifications of Tendermint consensus algorithm
and TLAPS-checked proofs of its properties: Agreement, Validity, Integrity ([safety](#safety)) and Termination ([liveness](#liveness)).

The specifications follow Algorithm 1 of main reference for the algorithm: [The latest gossip on BFT consensus][tendermint-paper].
The specification considers a single height of consensus: sice Tendermint executes one height at a time, it does cover all relevant behaviour.

The protocol is split across four abstraction levels.
Each level adds one group of self-contained features.
The split keeps the Agreement proof at the most abstract level, where the state is smallest.
Termination is proved at the most concrete level spec, which models the protocol as in the paper: _Partial Synchrony_ augmented with the _Gossip Communication_ property.

## Status

The following properties are proved:

- **Agreement**: No two correct processes decide on different values. *(Safety)*
- **Integrity**: Once a process decides a value, the decision value never changes. *(Safety)*
- **Termination**: All correct processes eventually decide on a value. *(Liveness)*
- **Validity**: A decided value is valid, i.e., it satisfies the predefined predicate denoted `valid()`. *(Safety)*


### Safety

There are four specifications forming a refinement chain:

```text
TendermintVoting <- TendermintOperational <- TendermintByzantine <- TendermintPartialSync
```

`A <- B` means that `B` _refines_ `A`. Every behavior of `B`, under its
refinement mapping, is a behavior of `A`. Specification `A` is the more
abstract one. Specification `B` is the more concrete one.

The safety properties properties are proved once on the `TendermintVoting` model, in `TendermintVotingProofs`.
The refinement proofs then transfer them down to `TendermintPartialSync`.
At the two lower levels, the properties hold for honest validators.

### Liveness

Termination is a liveness property. Refinement onto a more abstract
specification does not transfer it downwards. Termination is therefore proved
directly on `TendermintPartialSync`, the only level with timers, a
numeric clock, `GST`, and `Δ`, modelling the Partially Synchronous model.
The theorem, that lives in `TendermintPartialSyncTermination`, is:

```tla
THEOREM TerminationThm == Spec => Termination
```

`Spec` includes weak fairness on every honest action and on `Tick`. The
property is conditional:

```tla
Termination == TerminationConditions => (\A p \in Honest : <>(decision[p] # nil))
```

`TerminationConditions` is `EveryHonestProposesAgain`. For every round bound,
each honest validator is the proposer of some later round. A Byzantine proposer
can stay silent, so the proof cannot use one honest proposer round only. The
proof also uses the timeout margin assumptions of `TendermintPartialSync`,
which are `ProposeTimeoutMargin` and `PrevoteTimeoutMargin`.

The termination proof reuses the safety results.
`TendermintPartialSyncTerminationBase` extends
`TendermintPartialSyncRefinement`. The transferred invariants are therefore
available by name in the termination modules.

No proof step in the safety chain or in the termination lattice is `OMITTED`.
The termination modules add no axiom of their own.

## Scope

The specifications cover one consensus height with a fixed set of participants.
They do not model validator set
changes over heights, accountability, application execution, or networking outside the
message delivery assumptions of the paper protocol.

## Repository layout

The top level holds the `Makefile`, the prose documents, every `.tla` module,
and every `.cfg` configuration.

### Specifications

There are four specifications forming a refinement chain, from most abstract to most concrete:
* [`TendermintVoting.tla`](./TendermintVoting.tla): abstract voting and lock
  discipline, the core components that ensure Agreement
* [`TendermintOperational.tla`](./TendermintOperational.tla): per-validator
    round and step state machine with leaderless proposals
* [`TendermintByzantine.tla`](./TendermintByzantine.tla): Byzantine fault model
  with faulty validators, authenticated faults, and designated proposers
  and designated proposers
* [`TendermintPartialSync.tla`](./TendermintPartialSync.tla): paper-level
  spec with timers, concrete quorums, and partial synchrony; bottom of the
  refinement chain

### Safety proofs

Introduced in the `TendermintVoting` model, with refinements proved down to `TendermintPartialSync`:
* [`TendermintVotingProofs.tla`](./TendermintVotingProofs.tla)
* [`TendermintOperationalRefinement.tla`](./TendermintOperationalRefinement.tla)
* [`TendermintByzantineRefinement.tla`](./TendermintByzantineRefinement.tla)
* [`TendermintPartialSyncRefinement.tla`](./TendermintPartialSyncRefinement.tla)

The companion [`agreement.md`](./agreement.md) describes how the proof is constructed using these four modules.

### Liveness proof

The Termination proof is split into 13 modules. Each module trusts the theorem
statements of the modules that it extends, and re-checks its own obligations
only. An edit in one module therefore does not re-check the whole proof.

The `EXTENDS` relation is a lattice, not a tree. A module in parentheses is a
second parent of the module above it.

```text
TendermintPartialSyncTerminationBase
  |-- ...WithinRound
  |     |-- ...Selection
  |     `-- ...CascadeInvariants   (also ...RoundProgress)
  |           `-- ...CascadeRegion
  |                 `-- ...CascadeCore
  |                       `-- ...Cascade
  |                             `-- ...LockRetry
  `-- ...NonZeno
        `-- ...RoundProgress
              `-- ...CrossRound
                    `-- ...Dominator   (also ...Selection)
TendermintPartialSyncTermination       (...Dominator and ...LockRetry)
```

The names below omit the `TendermintPartialSyncTermination` prefix.

| Module              | Content                                                                                 |
|---------------------|-----------------------------------------------------------------------------------------|
| `Base`              | Safety facts, clock and latch facts, and the message, decision, and delivery invariants |
| `NonZeno`           | Progress of the clock, and the burst core                                               |
| `RoundProgress`     | `PostGSTRoundProgress`, derived from `RoundGrowth`                                      |
| `WithinRound`       | Within-round safety support for the case split of paper Lemma 5                         |
| `CascadeInvariants` | Vocabulary and global invariants of the Lemma 5 cascade                                 |
| `CascadeRegion`     | Propose ceiling, and the two region conjuncts with their latches                        |
| `CascadeCore`       | Vote dates, and the joint induction                                                     |
| `Cascade`           | Interface of the cascade, which is `Lemma5OrBlockingLock`                               |
| `LockRetry`         | `LockRetryDecides`, on a finite count of disruptive precommit pairs                     |
| `Selection`         | Selection of the entry into a good round                                                |
| `CrossRound`        | Paper Lemma 6, as `ValidCatchUp` and `HighLockCatchUp`                                  |
| `Dominator`         | `StableEntryDominator`, the stable entry dominance                                      |
| (no suffix)         | Paper Lemma 7, decision propagation, and `TerminationThm`                               |

The four `Cascade*` modules are contiguous parts of one earlier module. They
prove paper Lemma 5. The last part keeps the plain `Cascade` name, so its
consumers need no change.

### Bounded model checks

Six `*MC.tla` modules and 16 `*.cfg` configurations check bounded instances with TLC.
Six configurations carry the name of their module. The other ten need the module as a separate argument:

* `...TerminationInterfaceMC` takes `...TerminationFrontierCounterexample`,
  `...TerminationProposerCounterexample`, and
  `...TerminationShortTimeoutCounterexample`
* `...TerminationWithinRoundMC` takes the seven other
  `...TerminationWithinRound*` configurations

The `make tlc` target takes the pair. See [Verification](#verification).

Configurations whose name ends in `Counterexample.cfg`, and
`...WithinRoundWindowGst.cfg`, are expected failures. Each one keeps a
counterexample that motivated a repair. Run those configurations one at a time.
Do not add them to a passing target.

### Measured results

Measured on 2026-08-09 with `/usr/bin/time -p`.

**Agreement**:

| Module                              | Elapsed time | Proof obligations |
|-------------------------------------|-------------:|------------------:|
| `TendermintVotingProofs`            |      0:06.80 |               252 |
| `TendermintOperationalRefinement`   |      0:12.99 |               242 |
| `TendermintByzantineRefinement`     |      0:34.56 |               224 |
| `TendermintPartialSyncRefinement`   |      2:50.69 |               465 |
| **Total**                           |  **3:45.04** |         **1,183** |

**Termination**:

| Module                         | Elapsed time | Proof obligations |
|--------------------------------|-------------:|------------------:|
| `TerminationBase`              |      0:14:42 |             1,357 |
| `TerminationNonZeno`           |      0:17:22 |             1,244 |
| `TerminationRoundProgress`     |      1:00:37 |             2,114 |
| `TerminationWithinRound`       |      0:09:10 |               770 |
| `TerminationCascadeInvariants` |      0:39:42 |             1,275 |
| `TerminationCascadeRegion`     |      1:08:16 |             1,540 |
| `TerminationCascadeCore`       |      1:07:03 |             1,439 |
| `TerminationCascade`           |      0:43:14 |             1,049 |
| `TerminationLockRetry`         |      0:11:58 |               284 |
| `TerminationSelection`         |      0:02:50 |               192 |
| `TerminationCrossRound`        |      0:15:10 |               604 |
| `TerminationDominator`         |      0:11:42 |               408 |
| `Termination`                  |      0:31:43 |               607 |
| **Total**                      |  **6:33:29** |        **12,883** |

Names above omit the `TendermintPartialSync` prefix.
The final agreement refinement is also a dependency of the termination proof
and is listed only in the agreement table.

## Tools

Two tools are needed:  `tlapm` and TLC.
the proofs. TLC is part of the TLA+ tools, and it runs the bounded model checks.

### tlapm
TLA⁺ Proof Manager: the tool that mechanically checks proofs,
part of TLA⁺ Proof System, or TLAPS.

Prebuilt binaries are published in https://github.com/tlaplus/tlapm/releases.
Download the archive for your platform and unpack it.
Add the unpacked `bin/` directory to the `PATH`.


The archive includes `tlapm`, the TLAPS standard proof modules, and the backend
provers that `make` invokes. The backends are Zenon, Isabelle, and an SMT
solver. Check the installation:

```bash
tlapm --version
tlapm --where    # prints the standard-library location
```

To build from source instead, follow the instructions in the repository. The
build needs OCaml and opam: <https://github.com/tlaplus/tlapm>.

### TLC

Tool that checks TLA⁺ models: bounded state-space exploration.

TLC needs Java 11 or later. Download `tla2tools.jar` from the releases page:
<https://github.com/tlaplus/tlaplus/releases>

TLC also needs the TLAPS standard library on its module search path.
Some specifications extend the `TLAPS` module, and `tla2tools.jar` does not carry that module.
So pass its location to the `TLA-Library` system property:

```bash
java -DTLA-Library=$(tlapm --where) -jar /path/to/tla2tools.jar \
  -config TendermintVotingMC.cfg TendermintVotingMC.tla
```

The `make tlc` target sets the property for you (see [Verification](#verification)),
using the `TLA2TOOLS` variable.
Alternatively, put the property in a shell alias if you want a short command:

```bash
alias tlc='java -DTLA-Library=$(tlapm --where) -jar /path/to/tla2tools.jar'
```

### Versions used

The proofs were checked with:

* `tlapm` commit `fd3988f`, built with OCaml 5.1.0. The backends were
  Isabelle2025, Zenon 0.8.4, and Z3 4.8.9 for SMT.
* TLC 2.19 of 8 August 2024, as `tla2tools.jar`, on Java 17

Later versions are expected to work. These are the versions that produced the
recorded results.

## Verification

Put `tlapm` on `PATH` first. See [Installing the
Then run one of these targets:

```bash
make              # both chains, safety first
make agreement    # the four safety modules, about 4 minutes
make termination  # the 13 termination modules, about 6.5 hours
```

Run the termination modules one after the other. Do not fan out with `-j6`.
Six `tlapm` processes starve each other. An obligation then fails with an
internal timeout instead of a real proof failure. Use plain `make termination`,
or `-j2`. Treat a failure in a module that you did not edit as contention, and
re-check that module alone.

To check one module, use its own target, or call `tlapm` directly:

```bash
make term-cascade-core
tlapm --nofp TendermintVotingProofs.tla
```

To run a TLC model, use the `tlc` target. `MC` gives the module, and `CFG` gives
the configuration (defaults to `MC` when empty).  Neither name carries a file extension.

```bash
make tlc MC=TendermintVotingMC
make tlc MC=TendermintPartialSyncTerminationWithinRoundMC \
  CFG=TendermintPartialSyncTerminationWithinRoundLockRetry
```

The target sets the TLAPS library path from `tlapm --where`.
The `TLA2TOOLS` variable configures the location of the downloaded `tla2tools.jar`;
the default value is `$HOME/bin/tla2tools.jar`.

[tendermint-paper]: https://arxiv.org/abs/1807.04938
