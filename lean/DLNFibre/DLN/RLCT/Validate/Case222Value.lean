import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.MonomialThresholdIdentity
import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Value` — the `(2,2,2)` per-leaf monomial-threshold values

The **fm half** of the `(2,2,2)` cover (#54; pp's split-card: `fm` owns the per-leaf VALUE, `fm-2`
owns the measure `∫⁻ = Σ ∫⁻`). The 24-leaf resolution of `dlnLoss (2,2,2) 0` has exactly two leaf
shapes, and **every** leaf threshold is `3/2 = ½·Mval(deepest rank-1 stratum) = lambdaCore (2,2,2)`:

| leaf | count | `d` | `k` | `h` | `monomialThreshold` |
|------|-------|-----|-----|-----|---------------------|
| unit  | 8  | 2 | `![1,1]`   | `![3,2]`   | `3/2` |
| block | 16 | 3 | `![1,1,1]` | `![3,2,3]` | `3/2` |

Each is proven by the S2-free R1.2 threshold bracket: the **binding axis** `j = 1`
(`(k,h) = (1,2) = (1, 3−1)`) gives `≤ 3/2` (`monomialThreshold_le_regularSeq'`, `c = 3`); the
**multiplicity bound** `m = 3` (`3·kⱼ ≤ hⱼ + 1` on every axis: `3 ≤ 4`, `3 ≤ 3`, `3 ≤ 4`) gives
`≥ 3/2` (`monomialThreshold_ge_of_mult'`). So `= 3/2` by antisymmetry — pure (S2-free) arithmetic,
no raw `⨅` evaluation, independent of the `#66` Params↔Fin8 seam. These feed `fm-2`'s `⨅`-over-24-leaves
assembly (`⨅ = 3/2`, `θ = 1`). -/

namespace DLNFibre.DLN.RLCT

open scoped ENNReal

/-- The `(2,2,2)` **unit leaf** (8 of them, `E`/`F0`-pivot, `d = 2`): `monomialThreshold = 3/2`. -/
theorem case222_unit_leaf_threshold :
    monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![3, 2] : Fin 2 → ℕ) = 3 / 2 := by
  apply le_antisymm
  · -- binding axis `j = 1`: `(k 1, h 1) = (1, 2) = (1, 3 − 1)` ⟹ threshold `≤ 3/2`.
    have := monomialThreshold_le_regularSeq' 2 (![1, 1] : Fin 2 → ℕ) (![3, 2] : Fin 2 → ℕ)
      3 (by norm_num) 1 (by rfl) (by rfl)
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this
  · -- multiplicity `m = 3`: `3·kⱼ ≤ hⱼ + 1` on every axis ⟹ threshold `≥ 3/2`.
    have := monomialThreshold_ge_of_mult' 2 (![1, 1] : Fin 2 → ℕ) (![3, 2] : Fin 2 → ℕ)
      3 (by intro j; fin_cases j <;> norm_num)
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this

/-- The `(2,2,2)` **block leaf** (16 of them, δ→step-3 sub-charts, `d = 3`): threshold `= 3/2`. -/
theorem case222_block_leaf_threshold :
    monomialThreshold 3 (![1, 1, 1] : Fin 3 → ℕ) (![3, 2, 3] : Fin 3 → ℕ) = 3 / 2 := by
  apply le_antisymm
  · have := monomialThreshold_le_regularSeq' 3 (![1, 1, 1] : Fin 3 → ℕ) (![3, 2, 3] : Fin 3 → ℕ)
      3 (by norm_num) 1 (by rfl) (by rfl)
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this
  · have := monomialThreshold_ge_of_mult' 3 (![1, 1, 1] : Fin 3 → ℕ) (![3, 2, 3] : Fin 3 → ℕ)
      3 (by intro j; fin_cases j <;> norm_num)
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this

end DLNFibre.DLN.RLCT
