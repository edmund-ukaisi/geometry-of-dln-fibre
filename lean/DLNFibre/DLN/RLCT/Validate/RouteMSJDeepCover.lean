/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotChart

set_option linter.style.longLine false

/-!
# `RouteMSJDeepCover` — the exact-rank pivot coverage (deep atlas, Tide B base brick)

**Thread `genm-deepatlas`, aoyagi-full Stage 2.** The leaf/base brick of the deep stratified-resolution
atlas (`genm-deepatlas-design/design.md` §3.2): the **exact-rank** pivot-chart coverage of a single
matrix. It refines the banked rank-*locus* coverage `pivotLocus_eq_iUnion` (`{r ≤ rank} = ⋃ pivot
charts`) to the exact-rank stratum, which is the **non-vacuous** form the atlas needs.

## Why exact-rank (the non-vacuity point)

Bare "charts exhaust `{rank ≤ s}`" is VACUOUS: the size-`0` pivot chart (empty row/col embeddings, the
`0×0` minor with `det = 1`) is `Set.univ`, so any union that includes it covers `{rank ≤ s}` trivially
— zero content. The genuine, non-vacuous stratum coverage is at **exact rank `r`**: intersecting each
size-`r` pivot chart with `{rank ≤ r}` pins the rank to exactly `r`, and at `r = 0` the cell collapses
to `{M = 0}` (not the whole space). This is the CR-tree leaf on which the deep recursion's per-level
rank profile is read.

## What lands here (sorry-free)

* **`rankEqLocus_eq_iUnion_pivot_inter`** — `{M | M.rank = r} = ⋃ ρ κ, (pivotChart ρ κ ∩ {M | rank ≤ r})`:
  the exact-rank stratum is the union, over size-`r` row/col pivot embeddings, of the pivot charts cut
  down to `{rank ≤ r}`. Reuses the banked `pivotLocus_eq_iUnion`.

Network-free matrix rank over any field. Standalone (NOT aggregator-wired). Axiom target
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix

namespace DeepAtlas

variable {K : Type*} [Field K] {m n : ℕ}

/-- **Exact-rank pivot coverage (the non-vacuous CR-tree leaf).** The rank-exactly-`r` stratum is the
union, over size-`r` row/column pivot embeddings `(ρ, κ)`, of the pivot charts `{IsUnit (M.submatrix ρ κ)}`
intersected with the closed condition `{rank ≤ r}`. The pivot forces `rank ≥ r`
(`isUnit_submatrix_le_rank`), the intersection pins `rank = r`; conversely a rank-`r` matrix has a
nonzero `r×r` minor (`exists_nonsingular_submatrix_of_le_rank`). Non-vacuous: at `r = 0` the cell is
`{M = 0}`, not `Set.univ`. Refines the banked `pivotLocus_eq_iUnion`. -/
theorem rankEqLocus_eq_iUnion_pivot_inter (r : ℕ) :
    {M : Matrix (Fin m) (Fin n) K | M.rank = r}
      = ⋃ (ρ : Fin r ↪ Fin m) (κ : Fin r ↪ Fin n),
          (pivotChart ρ κ ∩ {M : Matrix (Fin m) (Fin n) K | M.rank ≤ r}) := by
  have hset : {M : Matrix (Fin m) (Fin n) K | M.rank = r}
      = {M : Matrix (Fin m) (Fin n) K | r ≤ M.rank} ∩ {M | M.rank ≤ r} := by
    ext M; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; omega
  rw [hset, pivotLocus_eq_iUnion r]
  ext M
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨ρ, κ, hρκ⟩, hle⟩; exact ⟨ρ, κ, hρκ, hle⟩
  · rintro ⟨ρ, κ, hρκ, hle⟩; exact ⟨⟨ρ, κ, hρκ⟩, hle⟩

/-- Non-vacuity at `r = 0`: the coverage collapses the rank-`0` stratum to `{M = 0}` (via the empty
pivot chart `= Set.univ` cut to `{rank ≤ 0}`), NOT to `Set.univ` — the exact-rank refinement carries
genuine content the bare `{rank ≤ s}` cover does not. Here the zero `2×2` matrix has rank `0`. -/
example : (0 : Matrix (Fin 2) (Fin 2) K).rank = 0 := by simp

end DeepAtlas

end DLNFibre.DLN.RLCT
