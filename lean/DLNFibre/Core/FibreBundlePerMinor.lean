/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RingTheory.Determinantal.Strata
import DLNFibre.Core.RingTheory.Determinantal.Schur

/-!
# `DLNFibre.Core.FibreBundlePerMinor` — the per-minor pivot chart family + the cover (B3-1, B3-2)

Thread 11 (`Core.FibreBundleReduced`) landed **single-chart** triviality: the chart
`e_β = chartLocalizedAlgEquiv` trivializes the reduced fibre over the **one** top-left-minor open
`{detΔ ≠ 0}`. The honest disclaimer there: a genuine per-minor open cover is **not** built.

This module builds it, at the level of the **base matrix space** `Mat_{p×q}` (the target of the
multiplication map), to the honest scope the brief sets:

- **B3-2 — the open cover (PROVED, the headline).** `Matrix` (`RingTheory.Determinantal.Strata`)
  supplies the missing
  determinantal-rank existence fact: a rank-`r` matrix has **some** invertible `r × r` minor
  (`exists_invertible_minor_of_rank`). Hence the det-open family `{minorChart s t}` over the pivot
  positions `(s, t)` is a genuine open cover of `Mat^{=r} = {M | M.rank = r}`
  (`rankEqLocus_subset_iUnion_minorChart`). This is re-exported here as the bundle's base cover.

- **B3-1 — the per-minor chart family as reindexings of the top-left chart (PROVED).** For each
  pivot `(s, t)` (injective row/column selectors) the chart at `(s, t)` is the **top-left** pivot
  chart `Matrix.pivotRankChart` of the matrix **reindexed** so the `(s, t)` minor sits in the
  top-left block: a coordinate permutation of `Mat_{p×q}` (`perMinorRowEquiv` / `perMinorColEquiv`,
  built from `Equiv.ofInjective` + `Equiv.Set.sumCompl`) carries the `(s, t)` minor to `toBlocks₁₁`
  (`submatrix_det_eq_toBlocks₁₁_det_reindex`) and preserves rank (`Matrix.rank_reindex`). So each
  per-minor chart inherits the top-left Schur parametrization `pivotRankChartEquiv`
  (`GL_r × Mat × Mat`) by transport along the reindex — the "(S,T) minor chart reduces to the
  top-left case via a coordinate permutation" content.

**Scope (honest).** This is the genuine open cover (B3-2) + the per-minor chart family realized as
coordinate-permutation reindexings of the single built top-left chart (B3-1). It does **not** build
the transition coherence (B3-3): the comparison of the two **localized coordinate-ring `AlgEquiv`s**
`e_{S,T} ∘ e_{S',T'}⁻¹` on overlaps — that requires comparing two ~250-LoC localization equivalences
and is the next rung. Base-change homogeneity (`Core.FibreNormalForm`) gives only existential
`GL × GL` transport, not the cocycle data, so it does **not** discharge B3-3 for free. Accordingly
this is **not** named `locallyTrivial`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {p q : ℕ}

/-! ## The per-minor reindexing equivalence (pivot `(s, t)` ↦ top-left block) -/

variable {r : ℕ}

/-- The row reindexing equivalence for a pivot row-selector `s : Fin r → Fin p` (injective): it
puts the `r` selected rows first, the complement after — `Fin r ⊕ ↥(range s)ᶜ ≃ Fin p`. Built from
`Equiv.ofInjective s` (`Fin r ≃ range s`) and `Equiv.Set.sumCompl` (`range s ⊕ (range s)ᶜ ≃ Fin p`).
-/
noncomputable def perMinorEquiv (s : Fin r → Fin p) (hs : Function.Injective s) :
    Fin r ⊕ ↥(Set.range s)ᶜ ≃ Fin p :=
  open Classical in
  (Equiv.sumCongr (Equiv.ofInjective s hs) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range s))

/-- The reindexing sends `Sum.inl i` to `s i` (the selected row sits in the top block). -/
theorem perMinorEquiv_inl (s : Fin r → Fin p) (hs : Function.Injective s) (i : Fin r) :
    perMinorEquiv s hs (Sum.inl i) = s i := by
  classical
  rw [perMinorEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]

/-- **The `(s, t)` minor is the top-left block of the reindexed matrix.** Reindexing `M` by the
pivot equivalences (so the selected rows/columns come first), the `r × r` minor on rows `s`,
columns `t` equals the top-left block `toBlocks₁₁` of the reindexed matrix. Hence their dets agree:
`(M.submatrix s t).det = (reindex perMinorEquiv.symm perMinorEquiv.symm M).toBlocks₁₁.det`. -/
theorem submatrix_eq_toBlocks₁₁_reindex (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (hs : Function.Injective s) (t : Fin r → Fin q)
    (ht : Function.Injective t) :
    M.submatrix s t
      = (reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm M).toBlocks₁₁ := by
  ext i j
  rw [reindex_apply, Equiv.symm_symm, Equiv.symm_symm, toBlocks₁₁, Matrix.of_apply,
    submatrix_apply, submatrix_apply, perMinorEquiv_inl, perMinorEquiv_inl]

/-- **The `(s, t)` minor is invertible iff the reindexed matrix's top-left block is.** Directly from
`submatrix_eq_toBlocks₁₁_reindex`. -/
theorem isUnit_submatrix_det_iff_toBlocks₁₁ (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (hs : Function.Injective s) (t : Fin r → Fin q)
    (ht : Function.Injective t) :
    IsUnit ((M.submatrix s t).det)
      ↔ IsUnit
          ((reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm M).toBlocks₁₁.det) := by
  rw [submatrix_eq_toBlocks₁₁_reindex M s hs t ht]

/-! ## The per-minor chart reduces to the top-left pivot chart

The `Matrix.pivotRankChart` reuse pins the matrix entry field to `Type` (universe `0`): its block
index types must live in the same universe as `k`, and the per-minor block types are `Fin r` and the
complement subtypes `↥(range s)ᶜ ⊆ Fin p`, all in `Type 0`. The DLN application (`k = ℂ`) is in
`Type 0`, so this monomorphic restriction is harmless. -/

section TopLeftReduction

variable {k : Type} [Field k] {p q r : ℕ}

/-- **B3-1 — the per-minor chart is the top-left pivot chart of the reindexed matrix.** For a pivot
position `(s, t)` (injective row/column selectors), a matrix `M` lies in the rank-`r` locus and its
`(s, t)` minor is invertible **iff** the matrix reindexed so the selected rows/columns come first
lies in the top-left pivot chart `Matrix.pivotRankChart` (over the block index types `Fin r` /
`↥(range s)ᶜ` / `↥(range t)ᶜ`). The coordinate permutation `reindex perMinorEquiv.symm` preserves
rank (`Matrix.rank_reindex`) and carries the `(s, t)` minor to the top-left block
(`submatrix_eq_toBlocks₁₁_reindex`). This realizes every per-minor chart as the single built
top-left chart of a permuted matrix — the "(S, T) minor chart reduces to the top-left case via a
coordinate permutation" content of the cover. (Field in `Type` for the `pivotRankChart` reuse.) -/
theorem mem_minorChart_inter_rankEqLocus_iff (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (hs : Function.Injective s) (t : Fin r → Fin q)
    (ht : Function.Injective t) :
    (M ∈ rankEqLocus (k := k) r ∧ M ∈ minorChart k p q s t)
      ↔ reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm M
          ∈ pivotRankChart k (Fin r) (↥(Set.range s)ᶜ) (↥(Set.range t)ᶜ) := by
  rw [pivotRankChart, Set.mem_setOf_eq, rankEqLocus, minorChart, Set.mem_setOf_eq,
    Set.mem_setOf_eq, rank_reindex, Fintype.card_fin,
    isUnit_submatrix_det_iff_toBlocks₁₁ M s hs t ht]

/-- The reindex bijection restricts to the per-minor chart: the subtype of rank-`r` matrices whose
`(s, t)` minor is invertible is carried by `reindex perMinorEquiv.symm` onto the top-left pivot
chart's subtype (`Equiv.subtypeEquiv` along `mem_minorChart_inter_rankEqLocus_iff`). -/
noncomputable def minorChartReindexEquiv (s : Fin r → Fin p) (hs : Function.Injective s)
    (t : Fin r → Fin q) (ht : Function.Injective t) :
    {M : Matrix (Fin p) (Fin q) k //
        M ∈ rankEqLocus (k := k) r ∧ M ∈ minorChart k p q s t}
      ≃ {M' // M' ∈ pivotRankChart k (Fin r) (↥(Set.range s)ᶜ) (↥(Set.range t)ᶜ)} :=
  Equiv.subtypeEquiv (reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm)
    (fun M ↦ mem_minorChart_inter_rankEqLocus_iff M s hs t ht)

/-- **B3-1 headline — the explicit per-minor Schur parametrization.** Every per-minor pivot chart
`{M | M.rank = r ∧ the (s,t) minor is invertible}` is, via the coordinate-permutation reindex
followed by the top-left Schur parametrization (`Matrix.pivotRankChartEquiv`), in explicit bijection
with `GL_r × Mat × Mat`: the chart is freely parametrized by an invertible `r × r` pivot block and
two off-diagonal blocks, the fourth block being Schur-forced. This is the per-minor analogue of the
single top-left chart — a genuine chart for **each** pivot position `(s, t)`, all of them realized
as the one built chart of a permuted matrix. -/
noncomputable def minorChartEquiv (s : Fin r → Fin p) (hs : Function.Injective s)
    (t : Fin r → Fin q) (ht : Function.Injective t) :
    {M : Matrix (Fin p) (Fin q) k //
        M ∈ rankEqLocus (k := k) r ∧ M ∈ minorChart k p q s t}
      ≃ {Δ : Matrix (Fin r) (Fin r) k // IsUnit Δ.det}
          × Matrix (Fin r) (↥(Set.range t)ᶜ) k × Matrix (↥(Set.range s)ᶜ) (Fin r) k :=
  (minorChartReindexEquiv s hs t ht).trans (pivotRankChartEquiv (k := k))

end TopLeftReduction

end DLNFibre.Core
