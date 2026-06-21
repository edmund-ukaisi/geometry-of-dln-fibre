import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case222Value

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222` — the `(2,2,2)` headline wrapper (SPECIFY skeleton)

The **third ladder rung** (after `(1,1,1)` and `(2,1,2)`), the thin validate assembly mirroring
`case212_rlct`: the local RLCT of the `(2,2,2)` core loss at the deepest point equals Aoyagi's
closed form `aoyagiLambda (2,2,2) 0 = 3/2` (`#eval`-verified; `= lambdaCore (2,2,2) =
½·Mval(rank-1 stratum)`, θ = 1).

Unlike `(1,1,1)`/`(2,1,2)`, the `(2,2,2)` core is NOT a single chart / product — it needs the full
24-leaf **cover** (`#54`, fm-2's flat-`Fin 8` charts: 8 unit + 16 block leaves). So this wrapper is
thin and **consumes two upstream results**:
1. **the resolution-charts instance** `resolution_charts_case222` (fm-2's `#54` deliverable): the
   `(2,2,2)` instance of `resolution_charts`, `rlctAtOn (core) 0 = ⨅ leaf, monomialThreshold`;
2. **the per-leaf VALUE** (`#68`, mine, on trunk): every leaf threshold is `3/2`
   (`case222_unit_leaf_threshold`, `case222_block_leaf_threshold`), so the `⨅` over the 24-leaf
   family is `3/2`.

**SPECIFY-phase**: the headline + its decomposition into named sorries (the `#54`-gated resolution
instance + the `⨅ = 3/2` value, which becomes one-line once fm-2 pins the concrete leaf family
`(ι, d, k, h)` so `case222_unit/block_leaf_threshold` apply per leaf). The cast tail
(`3/2 = ofReal (aoyagiLambda (2,2,2) 0)`) is proven. This is the validate-assembly, NOT the charts
(`#54`/`#67` are fm-2's) — no duplication.
-/

namespace DLNFibre.DLN.RLCT

open scoped ENNReal

/-- The deepest point of the `(2,2,2)` `B = 0` fibre: the origin (all entries zero). -/
noncomputable def deepest222 : Params (![2, 2, 2] : Fin 3 → ℕ) := fun _ => 0

/-- **The `(2,2,2)` resolution-charts instance** (`#54`, fm-2's flat-`Fin 8` 24-leaf cover): the
core RLCT at the origin equals the `⨅` of the leaf monomial-thresholds — the `(2,2,2)` instance of
the general `resolution_charts (M)`; fm-2 supplies the explicit chart family + the `∫⁻ = Σ ∫⁻`
cover. Stub (the `#54` gate); when it lands, this is `resolution_charts (![2,2,2])` with the
concrete `(ι, d, k, h)` (8 unit `(2, ![1,1], ![3,2])` + 16 block `(3, ![1,1,1], ![3,2,3])`). -/
theorem resolution_charts_case222 :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params (![2, 2, 2] : Fin 3 → ℕ) =>
          dlnLoss (![2, 2, 2] : Fin 3 → ℕ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A) deepest222
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  sorry

/-- **The `(2,2,2)` headline** (target: axiom-clean-mod-S2 once `#54` lands). The local RLCT of the
`(2,2,2)` core loss at the deepest point equals `aoyagiLambda (2,2,2) 0 = 3/2`. Assembled from the
resolution-charts instance (`resolution_charts_case222`, fm-2's `#54`) whose `⨅` over the 24-leaf
family is `3/2` (every leaf `= 3/2` by `#68`'s `case222_unit/block_leaf_threshold`). The third
ladder rung; mirrors `case212_rlct`. -/
theorem case222_rlct :
    rlctAtOn (fun A : Params (![2, 2, 2] : Fin 3 → ℕ) =>
        dlnLoss (![2, 2, 2] : Fin 3 → ℕ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A) deepest222
      = ENNReal.ofReal (aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0) := by
  obtain ⟨ι, _, d, k, h, hres⟩ := resolution_charts_case222
  rw [hres]
  -- `⨅ leaf, monomialThreshold = 3/2` (every leaf `= 3/2` via #68); needs fm-2's concrete leaves.
  have hinf : (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = (3 / 2 : ℝ≥0∞) := by
    sorry
  rw [hinf]
  -- `aoyagiLambda (2,2,2) 0 = 3/2` (kernel) ⟹ `ofReal (3/2) = 3/2`.
  rw [show aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0 = (3 / 2 : ℚ) by decide +kernel]
  rw [show ((3 / 2 : ℚ) : ℝ) = (3 / 2 : ℝ) by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

end DLNFibre.DLN.RLCT
