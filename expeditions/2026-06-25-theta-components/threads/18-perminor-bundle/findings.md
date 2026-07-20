# Thread 18 — per-minor open cover + chart family (B3-1, B3-2) (formaliser) — certificate

**Formaliser tide, scoped honestly.** Two new files, both axiom-clean `[propext, Classical.choice,
Quot.sound]` (controller-gated); whole library green (3785 jobs); reviewer PASS. **B3-3 transition
coherence NOT built and disclaimed** — so this is the cover + chart family, NOT yet a `locallyTrivial`
bundle.

## Rungs closed
- **B3-2 (keystone + headline): the rank↔minor bridge + the open cover.** The determinantal-rank
  existence fact MISSING in Mathlib v4.29 is now proved: a rank-`r` matrix has SOME invertible `r×r`
  minor. Hence the det-open family covers `Mat^{=r}`.
- **B3-1: the per-minor chart family.** Each per-minor chart is the top-left `pivotRankChart` of a
  coordinate-permuted matrix, inheriting the `GL_r × Mat × Mat` Schur parametrization.
- **B3-3 (transition coherence): NOT built, disclaimed.** Codex-confirmed: base-change homogeneity gives
  only existential `GL×GL` transport, NOT the localized-`AlgEquiv` cocycle data on overlaps. Comparing
  the two ~250-LoC localization equivalences on the overlap is the next rung (tracked as task #117).

## Files (both sorry-free, axiom-clean)
- `lean/DLNFibre/Core/RankMinorCover.lean` — network-free, Mathlib-adjacent (spin-out candidate, like
  `mvPolynomialAwayMapTensorAlgEquiv`).
- `lean/DLNFibre/Core/FibreBundlePerMinor.lean` (imports `RankMinorCover` + `DeterminantalChart`).

## Theorems delivered
- `exists_invertible_minor_of_rank {r} (A : Matrix (Fin p) (Fin q) k) (hr : A.rank = r) :
  ∃ (s : Fin r → Fin p) (t : Fin r → Fin q), Injective s ∧ Injective t ∧ IsUnit ((A.submatrix s t).det)`
  — the rank↔minor bridge (only `[Field k]`).
- `exists_injective_cols_linearIndependent` / `exists_invertible_square_minor_of_cols_linearIndependent`
  — the two reusable index-extraction helpers.
- `rankEqLocus_subset_iUnion_minorChart (r) : rankEqLocus r ⊆ ⋃ st, minorChart k p q st.1 st.2` and
  `rankEqLocus_eq_iUnion_inter_minorChart` — the cover (`minorChart s t := {M | IsUnit ((M.submatrix s
  t).det)}`, `rankEqLocus r := {M | M.rank = r}`).
- `perMinorEquiv` / `perMinorEquiv_inl` / `submatrix_eq_toBlocks₁₁_reindex` /
  `isUnit_submatrix_det_iff_toBlocks₁₁` — the coordinate-permutation reindex carrying the `(s,t)` minor
  to the top-left block.
- `mem_minorChart_inter_rankEqLocus_iff` — per-minor chart membership ⟺ reindexed matrix in
  `pivotRankChart`.
- `minorChartEquiv` — the explicit per-minor `GL_r × Mat × Mat` Schur bijection (transport of
  `pivotRankChartEquiv`). NOTE: the `pivotRankChart`-reuse theorems pin `k : Type` (universe 0) —
  harmless (`ℂ` is `Type 0`), disclaimed in-module.

## Mathlib lemmas used (v4.29)
`Matrix.rank_eq_finrank_span_cols`, `Submodule.exists_fun_fin_finrank_span_eq`, `LinearIndependent.rank_matrix`
+ `Matrix.linearIndependent_rows_iff_isUnit` + `Matrix.isUnit_iff_isUnit_det`, `Matrix.rank_reindex`,
`Matrix.transpose_submatrix`, `row_submatrix_eq_comp`/`col_submatrix_eq_comp`,
`Equiv.ofInjective`/`Equiv.Set.sumCompl`/`Equiv.subtypeEquiv`.

## Artifacts (committed @ 67dff40b / 1f4efb55 / 7f3af5e9)
`threads/18-perminor-bundle/statement-card.md`. Lean: `Core/RankMinorCover.lean`,
`Core/FibreBundlePerMinor.lean`. The tide stayed out of the parallel `smooth-factC` files
(`FibreGenericSmoothUncond.lean`, `LocalizationAtComponent.lean`).

## Net bundle state (controller synthesis)
The full LR Lemma 4.6 bundle is now: **single-chart triviality (thread 11) + the genuine per-minor open
cover of `Mat^{=r}` + the per-minor chart family (thread 18)**, all unconditional + axiom-clean. The ONE
remaining rung to earn the `locallyTrivial` name is **B3-3 transition coherence** (#117) — the cocycle
`AlgEquiv` on chart overlaps, a comparison of two localization equivalences.
