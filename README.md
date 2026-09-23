# Formal Tendermint

Formal specifications and model checking for Tendermint-style consensus algorithms.

> **Research code.** This repo contains code for academic research.
> The code is not deployed, not a production system, and not maintained.

## Protocols

- [Fast Tendermint](fast-tendermint/README.md) — consensus in two communication steps, tolerating `f < n/5` Byzantine processes
- [Tendermint](tendermint/tla/README.md) — TLA+ specifications of the original algorithm, with TLAPS proofs of agreement, validity, and termination

## Research Context

The code in this repo supports

- *[Fast Tendermint: Speeding Up a Foundational Consensus Protocol](https://arxiv.org/pdf/2608.13434)*, published at DISC 2026

