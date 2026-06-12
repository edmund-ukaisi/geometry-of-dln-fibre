---
title: "Thread 01 — Mathlib quiver-rep coverage recon"
status: closed
topics: [recon, mathlib-coverage, quiver, gabriel, ext]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 01 — Mathlib coverage recon (read-only)

Read-only reconnaissance of Mathlib v4.29.0 (`lean/.lake/packages/mathlib/`) for the engine, via
`scripts/lean-search` + `rg`. No build run (concurrent formaliser). Verdicts: **reuse** / **partial** /
**build-from-scratch**. (Persisted by the controller from the scout's return — the Explore agent is
read-only.)

## Coverage map

| Area | Exists | Missing | Verdict |
|---|---|---|---|
| **1. Quiver reps** | `Quiver`, `Quiver.Path`, `Prefunctor` (`Combinatorics/Quiver/*`); `Paths V` path category, bundled `Quiv` (`CategoryTheory/Category/Quiv`); monoid reps `Representation k G V`, bundled `Rep k G` (`RepresentationTheory/*`) | path **algebra**; representations of a *general quiver* (functor `Paths V ⥤ ModuleCat`); the dimension-vector rep space `Rep_d` | **partial** |
| **2. Type-A / indecomposables** | `Fin n`, `CategoryTheory` finite (co)limits/biproducts, `Simple` objects, full `Abelian/` API | interval/"thin" modules `M_{ij}`; equioriented chain `0→…→N`; Kostant partitions | **build-from-scratch** |
| **3. Gabriel / Krull–Schmidt** | semisimple reps, `RingTheory.FiniteLength`, subobject lattices | a `KrullSchmidt` decomposition theorem; Gabriel (type-A indecomposables = intervals) | **build-from-scratch** |
| **4. Ext** | `Ext R C n` (`CategoryTheory/Abelian/Ext`), derived-cat `Ext` (`Algebra/Homology/DerivedCategory/Ext/Basic`, v4.29+), projective/injective resolutions, full `Homology/` | a direct `dim Ext¹(M,M)` for quiver reps (needs instantiation to a module category) | **reuse** |
| **5. Elementary (rungs 1–3)** | `Matrix.rank`, `Matrix.rank_mul_le*`, `Finset.sum` + interval/telescoping lemmas (`BigOperators.Intervals`), `Fin` dimension handling | the specific inclusion–exclusion identity (trivially provable) | **reuse** |

## Verdicts that steer the expedition

- **Rungs 1–3 (ambient objects + abstract Prop 3.1 inversion): only basic Mathlib** (`Matrix`, `Fin`,
  `Finset`, `BigOperators`). Confirmed — rung 1 has since landed (thread 02).
- **Rung 4 (orbits ↔ Kostant via Gabriel): build-from-scratch.** The type-A interval-module
  classification, Krull–Schmidt-style decomposition, and Kostant-partition data are all absent. This is
  the **largest new infrastructure** of the programme — and, being absent from Mathlib, the most
  reusable asset to get right. Two routes:
  1. **Full build** — define interval modules `M_{ij}` (as a representation of the equioriented type-A
     quiver / a functor to `ModuleCat k` or `FDRep k`), prove the type-A decomposition + uniqueness.
  2. **Cite-and-corollary** — state the type-A Gabriel decomposition (Thm 2.5) with a cited reference,
     prove the orbit ↔ Kostant corollary (Cor 2.9) on top. Lets the codimension layer proceed while the
     heavy quiver machinery is deferred/cited.
- **Ext codimension (Cor 3.5): reuse** Mathlib's `Ext` once reps are embedded in a module category.

## Recommendation (controller-adopted)

Land rungs 1–3 on basic Mathlib (done for rung 1; thread 03 for Prop 3.1). Treat **rung 4 as its own
sub-build** — open it only when whole-in-reach, and decide full-build vs cite-and-corollary then; do not
nibble it. The Ext codimension (Cor 3.5) is the *next* expedition, stacking on rung 4.

*Caveat:* identifiers verified against the cached source; `Ext` universe-polymorphism / module-Ext
instance resolution flagged **unverified (no build)**.
