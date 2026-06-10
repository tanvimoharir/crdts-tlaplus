# Formal Verification of CRDTs in TLA+

This repository contains TLA+ specifications for Conflict-free Replicated Data Types (CRDTs) developed as part of a guided research project. The specifications formally model operation-based CRDTs and their underlying network assumptions, and verify correctness properties such as Strong Eventual Consistency (SEC).

## Report

The full research report is available [here](https://github.com/tanvimoharir/crdts-tlaplus/blob/main/Guided_Research___Tanvi-3.pdf).

## Repository Structure

### `new/` — Revised Specifications

Contains the refined TLA+ specifications developed during the research, modelling CRDTs with explicit broadcast abstractions and correctness properties.

#### Network / Broadcast Models

| File | Description |
|------|-------------|
| `UnreliableBroadcast.tla` | Unreliable broadcast where messages can be dropped |
| `ReliableBroadcast.tla` | Reliable broadcast guaranteeing validity, agreement, and integrity |
| `CausalBroadcast.tla` | Causal broadcast using vector clocks to enforce causal delivery |
| `rco.tla` | Reliable Causal Order (RCO) broadcast built on top of reliable broadcast |

#### CRDT Specifications

| File | Description |
|------|-------------|
| `OpCounter.tla` | Operation-based increment-only Counter |
| `OpPNCounter.tla` | Operation-based PN-Counter (increment and decrement) |
| `OpGOSet.tla` | Operation-based Grow-Only Set |
| `add_wins_set.tla` | Add-Wins Set (OR-Set) with causal broadcast |
| `lww_wins_register.tla` | Last-Writer-Wins Register using vector clock timestamps |
| `multi_register.tla` | Multi-Value Register preserving concurrent writes |
| `put_wins.tla` | Put-Wins Map (key-value store with add-wins semantics) |

#### Other Files

| File | Description |
|------|-------------|
| `config.txt` | Example TLC model checker configurations for the specifications |

### `crdts/` — Earlier Specifications

Contains an earlier set of TLA+ specifications exploring various CRDT formalisations and network models. These served as the starting point for the refined versions in `new/`.

## Correctness Properties

The specifications verify the following properties:

- **Convergence** — Replicas that have delivered the same set of messages hold the same state.
- **Eventual Delivery** — Every message delivered by one correct replica is eventually delivered by all correct replicas.
- **Strong Eventual Consistency (SEC)** — The conjunction of convergence and eventual delivery.
- **Causal Delivery** — Messages are delivered respecting their causal order (where applicable).

## Running the Specifications

These specifications are designed to be checked with the [TLC model checker](https://lamport.azurewebsites.net/tla/tools.html) (part of the TLA+ Toolbox or VS Code TLA+ extension).

1. Open a `.tla` file in the TLA+ Toolbox or VS Code with the TLA+ extension.
2. Create a model configuration specifying constants (see `new/config.txt` for examples).
3. Add the desired temporal properties (e.g., `SEC`, `Convergence`) to the model checker.
4. Run TLC.

## Author

Tanvi Moharir
