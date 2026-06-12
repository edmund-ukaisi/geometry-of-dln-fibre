---
title: "Thread 08 — interval modules + direct sums + rankPattern(⊕ M^m)=cumul m (rung 4b)"
status: sorry-free
topics: [interval-module, direct-sum, block-rank, cumul, rung-4]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 08 — interval modules, direct sums, `rankPattern(⊕ M^m) = cumul m` (rung 4b)

Module: `lean/DLNFibre/Core/IntervalModule.lean` (namespace `DLNFibre.Core`), network-free, ~530 lines;
imports `Submult`, `RankPattern`, `Mathlib.Data.Matrix.Block`, `Mathlib.LinearAlgebra.Matrix.ToLin`.
**All four parts landed** (incl. the headline finite fold). Persisted by controller (subagent write-guard).

## Landed
1. **Interval module** `intervalModule i j : Tuple (intervalDim i j)`, `intervalDim i j l = if i≤l∧l≤j then 1 else 0`,
   the **constant-`1`** form `fun t _ _ ↦ if intervalActive i j t then 1 else 0` (cast-free; `=1×1` identity on
   active edges, `0`-dim off the interval).
2. **Indicator** `rankPattern_intervalModule : rankPattern (M_{ij}) i' j' = if i≤i'∧j'≤j then 1 else 0`
   (`[Nontrivial k]`); and `…_eq_cumul` = `cumul N (singleDelta i j) i' j'` (tie to Prop 3.1a).
3. **Binary direct sum** `dirSum A B : Tuple (d+d') = reindex (fromBlocks A 0 0 B)`; block-rank additivity
   `rank_fromBlocks_zero_zero` (proved from scratch — see below); `rankPattern_dirSum : r(A⊕B)=r(A)+r(B)`.
4. **Headline** `rankPattern_intervalDirectSum_eq_cumul` : `(rankPattern (⊕_{(a,b)∈L} M_{ab}) i j : ℤ) =
   cumul N (multiplicityArray L) i j`. The Kostant array is a `List (Fin (N+1)×Fin (N+1))` of endpoint pairs,
   so `foldDim`/`intervalDirectSum` co-recurse and the dependent dims match by `rfl` — the cast slog feared
   in the design never materialised.

## Block-rank additivity lever (the one real Mathlib gap)
**No `Matrix.rank_fromBlocks`/`rank_blockDiagonal` at the v4.29 pin.** Proved from scratch via the
`mulVecLin`/`prodMap` correspondence: `LinearEquiv.sumArrowLequivProdArrow` + `fromBlocks_mulVec`/`zero_mulVec`
(block map ≅ `prodMap`), `LinearMap.range_prodMap`, `Module.finrank_prod`, local helper
`submoduleProdEquiv : p.prod q ≃ₗ p × q`. **Needs `Field K`** (range subspaces free + f.d.) — an honest
weakest-class split; the rest of the file is `CommRing`. Block-diag mult/identity stay `CommRing`.

## Build / audit
Whole lib green (1796 jobs); `scripts/sorries` 0; `#print axioms` on the headline / block-rank / indicator →
only `[propext, Classical.choice, Quot.sound]`; `intervalModule` itself axiom-free. Witnesses over `ℚ`
(`N=2`): `M_{02}`; `M_{00}⊕M_{11}` additivity; the finite fold on `M_{00}⊕M_{01}⊕M_{12}⊕M_{22}` (the Ex 4.3 /
`(2,2,2)` orbit P6, `r₀₂=0`) — **same orbit as the `RankPattern.lean` witness**. Controller green-gated;
reviewer fidelity audit batched into the rung-4 review.

## Scope / precision
Interval-module / direct-sum side ONLY. The headline is about the **constructed** `⊕ M^m`; it does **not**
claim an arbitrary tuple's rank pattern is `cumul` of its Gabriel multiplicities (Prop 3.1b *completeness* =
rung 4d). Nothing named as if it asserted the Gabriel decomposition.

## For the rung-4 review
- **`Field` vs `CommRing` split** is genuine (block-rank additivity is `Field`-only via `Module.finrank_prod`).
  Acceptable for 4c/4d (representations are over a field). A `CommRing`+`Module.Free`/`Finite` generalisation
  is possible later but not automatic.
