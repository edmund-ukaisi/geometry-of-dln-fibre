import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case222Value

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222` — the `(2,2,2)` headline wrapper

The **third ladder rung** (after `(1,1,1)` and `(2,1,2)`), the thin validate assembly mirroring
`case212_rlct`: the local RLCT of the `(2,2,2)` core loss at the deepest point equals Aoyagi's
closed form `aoyagiLambda (2,2,2) 0 = 3/2` (`#eval`-verified; `= lambdaCore (2,2,2) =
½·Mval(rank-1 stratum)`, θ = 1).

Unlike `(1,1,1)`/`(2,1,2)`, the `(2,2,2)` core is NOT a single chart / product — it needs the full
24-leaf **cover** (`#54`, fm-2's flat-`Fin 8` charts: 8 unit + 16 block leaves). So this wrapper is
thin and consumes ONE upstream result, `resolution_charts_case222` (fm-2's `#54`), which already
folds in the per-leaf VALUE (`#68`, mine): the resolution exposes a **nonempty** leaf family on
which **every** monomial threshold is `3/2` (`case222_unit/block_leaf_threshold`). Given that, the
`⨅` collapses to `3/2` and the headline `= ofReal (aoyagiLambda (2,2,2) 0)` — both PROVEN here. The
ONE remaining `sorry` is `resolution_charts_case222` itself (the `#54` cover gate). This is the
validate-assembly, NOT the charts (`#54`/`#67` are fm-2's) — no duplication.
-/

namespace DLNFibre.DLN.RLCT

open scoped ENNReal

/-- The deepest point of the `(2,2,2)` `B = 0` fibre: the origin (all entries zero). -/
noncomputable def deepest222 : Params (![2, 2, 2] : Fin 3 → ℕ) := fun _ => 0

/-- **The `(2,2,2)` resolution-charts instance** (`#54`, fm-2's flat-`Fin 8` 24-leaf cover): the
core RLCT at the origin equals the `⨅` of the leaf monomial-thresholds, over a **nonempty** leaf
family on which **every** threshold is `3/2`. The `∀ i, … = 3/2` conjunct is the per-leaf VALUE
(`#68`) folded in: fm-2's 24 leaves are the 8 unit `(2, ![1,1], ![3,2])` + 16 block
`(3, ![1,1,1], ![3,2,3])`, each `= 3/2` by `case222_unit/block_leaf_threshold`. The remaining
`sorry` is the `#54` cover gate alone; when it lands, this is `resolution_charts (![2,2,2])` + the
concrete family + `#68` per leaf. -/
theorem resolution_charts_case222 :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      (∀ i, monomialThreshold (d i) (k i) (h i) = 3 / 2) ∧
      rlctAtOn (fun A : Params (![2, 2, 2] : Fin 3 → ℕ) =>
          dlnLoss (![2, 2, 2] : Fin 3 → ℕ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A) deepest222
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  sorry

/-- **The `(2,2,2)` headline** (one `sorry`: the `#54` cover, inside `resolution_charts_case222`).
The local RLCT of the `(2,2,2)` core loss at the deepest point equals `aoyagiLambda (2,2,2) 0`
(= `3/2`). The `⨅`-over-leaves collapses to `3/2` (nonempty family, every leaf `= 3/2` via `#68`),
and `ofReal (aoyagiLambda (2,2,2) 0) = 3/2` (`decide +kernel`) — both PROVEN. The third ladder rung;
mirrors `case212_rlct`. -/
theorem case222_rlct :
    rlctAtOn (fun A : Params (![2, 2, 2] : Fin 3 → ℕ) =>
        dlnLoss (![2, 2, 2] : Fin 3 → ℕ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A) deepest222
      = ENNReal.ofReal (aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0) := by
  obtain ⟨ι, _, _, d, k, h, hthr, hres⟩ := resolution_charts_case222
  rw [hres]
  -- `⨅` over the nonempty leaf family, every leaf `= 3/2`, collapses to `3/2`.
  have hinf : (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = (3 / 2 : ℝ≥0∞) := by
    simp only [hthr]; exact iInf_const
  rw [hinf, show aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0 = (3 / 2 : ℚ) by decide +kernel,
    show ((3 / 2 : ℚ) : ℝ) = (3 / 2 : ℝ) by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

end DLNFibre.DLN.RLCT
