# synthesis.md — controller's integrative read (core-quiver-engine)

The controller's *internal* integrative ground, flushed every tick (recovery substrate). Deliverable is
the audited `DLNFibre.Core` slice (rungs 1–3) + the Mathlib-coverage map.

## State (after tick 1)

- **Branch:** `expedition/core-quiver-engine` (off `dev`).
- **Controller mode:** dispatch-and-integrate — the controller spawns role-typed subagents per thread,
  green-gates + integrates their returns, and is the sole committer (no live Agent-Teams mailbox this run;
  the docs are the durable source of truth, per expedition.md § recovery).
- **Tick 1 landed:**
  - Thread 01 (recon) — **closed**; coverage map below.
  - Thread 02 (rung 1, ambient objects) — **sorry-free, controller-verified** (whole-lib green 1792 jobs,
    0 sorries, axiom-clean `[propext, Classical.choice, Quot.sound]`); **reviewer fidelity audit pending**
    (batched with Prop 3.1).
- **In flight:** Thread 03 (rungs 2–3, the abstract Prop 3.1 inversion).

## Current read

- Rungs 1–3 are basic-Mathlib reachable (confirmed; rung 1 landed). The spine is: ambient objects →
  rank patterns `r_{ij}` + Kostant multiplicities `m_{ij}` → the inclusion-exclusion bijection (Prop 3.1a,
  abstract) → [rung 4] orbits ↔ Kostant via Gabriel (build-from-scratch).
- **Encoding decision (endorsed):** `d : Fin (N+1) → ℕ` as a fixed parameter; `Rep_d = Tuple d` the
  product space; loci/fibre honest `Set (Tuple d)`. Faithful to the paper (which fixes `d` and varies it
  as a parameter — e.g. permutation invariance), keeps every intermediate `d k` first-class (needed for
  `r_{ij}` and the Kostant constraint), and the `Fin.castSucc` transport is contained in `multPrefix`
  behind two `rfl` step lemmas. Reversed the brief's "weigh (ii)/List-inductive" steer; Codex-corroborated.
- **`submult` (interval sub-products `A_j⋯A_{i+1}`) is the rung-2/3 primitive** — `multPrefix` is its
  `i=0` slice. Thread 03 introduces `submult` and defines `r_{ij} := (submult A i j).rank`; `mult` bridges
  as `submult 0 (last)`.

## Mathlib-coverage map (from thread 01)

- quiver basics: **reuse** (`Quiver`, `Path`, `Prefunctor`, `Rep k G`); quiver-rep layer / path algebra: build.
- type-A interval modules / equioriented chain / Kostant data: **build-from-scratch**.
- Gabriel / Krull–Schmidt decomposition: **build-from-scratch** (the heavy part of rung 4).
- `Ext`: **reuse** (machinery present; instantiate to a module category for Cor 3.5 — next expedition).
- ambient objects + abstract Prop 3.1: **reuse** basic Mathlib (`Matrix.rank`, `Finset`, `Fin`). Confirmed.

## Drift guard

Tag every result Proved / Assumed / Cited / Deferred. Prop 3.1 here is the **abstract array inversion**
(3.1a) — name it as such; the "rank pattern of an *actual tuple* = Σ Gabriel-multiplicities" direction
(3.1b) needs rung 4 and is a *separate*, deferred claim. Keep `Core` free of any `DLN`/network import.
No `Core` name may assert orbit/Gabriel content that is only Cited.
