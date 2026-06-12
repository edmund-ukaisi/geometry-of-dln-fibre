# synthesis.md — controller's integrative read (core-quiver-engine)

The controller's *internal* integrative ground: the current read, flushed every tick (the recovery
substrate after compaction). Not a deliverable — the deliverable is the audited `DLNFibre.Core` slice
(rungs 1–3) with statement cards, plus the Mathlib-coverage map.

## State

_Expedition not yet opened._ Skeleton created at setup. Central question + rungs in `brief.md`; opening
decision queue in `priorities.md`.

## Current read

- The target is the network-free engine spine: ambient objects + the orbit ↔ Kostant ↔ rank-pattern
  correspondence (§§2–3). `DLN`/RLCT is out of scope.
- The bedrock-first path is rungs 1→3 (objects, then Prop 3.1 as a characterisation); rung 4 (Gabriel /
  orbits ↔ Kostant) is gated on the Mathlib-coverage recon — it may be reuse or build-from-scratch.

## Mathlib-coverage map (fill from the recon thread)

- quiver representations: _?_
- type-A / $A_n$ indecomposables, Gabriel: _?_
- `Ext` of representations: _?_
- finite-combinatorics / matrix-rank API for Prop 3.1: _?_

## Drift guard

Tag every result Proved / Assumed / Cited / Deferred. Prefer a **characterisation** (the bijection) over a
one-directional formula for Prop 3.1. Keep `Core` free of any `DLN`/network import. Do not let a `Core` name
assert orbit-theoretic content (Gabriel) that is only Cited.
