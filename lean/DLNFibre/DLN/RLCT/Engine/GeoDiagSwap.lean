import DLNFibre.DLN.RLCT.Engine.FlatSwap
import DLNFibre.DLN.RLCT.Engine.GeoJacobianFold

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoDiagSwap` — the swap's determinant fact + the per-edge `β∘S` wrapper (t11)

The higher half of the diagonal-normalization swap `S = flatSwapCLE p d` (def + low properties in
`FlatSwap`): the determinant fact `|det D S| = 1` (needs `clm_involutive_abs_det_one`, `GeoJacobianFold`)
and the per-edge det wrapper for `β ∘ S`. Codex-confirmed Option A
(`threads/10-coverage/codex/s35-swap-realization-answer.md`); the biggest risk (β∘S source vs S∘β target)
is built against — the source swap reads `z_d`, a target swap would leave `z_p`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`|det D S| = 1`** — `S` is a linear involution, so its determinant has modulus `1`
(`clm_involutive_abs_det_one`). The det-neutrality the `β ∘ S` composition needs. -/
theorem flatSwapCLE_abs_det_fderiv_one (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) (x : Params M) :
    |(fderiv ℝ (flatSwapCLE M p d) x).det| = 1 := by
  rw [(flatSwapCLE M p d).hasFDerivAt.fderiv]
  exact clm_involutive_abs_det_one _ (flatSwapCLE_comp_self M p d)

/-- **The per-edge det through `β ∘ S`** (fork-15 wrapper): post-composing the pure blow-up
`geoChartMap g` with the source swap `S = flatSwapCLE p d` (`p = cNodeOf node ⟨pivot⟩` the fan-out pivot
cell) makes the per-edge Fréchet-derivative determinant read the DIAGONAL target `z_d`:

    |det D(geoChartMap g ∘ S) w| = |z_d(w)| ^ (dCenterOfNode node − 1).

Via `abs_det_fderiv_comp_det_one_gauge` (S det-1 + differentiable) + the banked per-edge atom
`geoChartMap_fderiv_det` (reads `z_p` at the gauged point `S w`) + `flatSwapCLE_apply_flat`
(`z_p(S w) = z_{swap p d p}(w) = z_d(w)`). `d` is a parameter; the wiring picks `d = diagTargetOf`. -/
theorem geoChartMap_swap_fderiv_det (g : GeoChart M) (w : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (d : Fin (flatDim M)) :
    |(fderiv ℝ (geoChartMap (dCenterOfNode M) (qNodeOf M) g ∘
        ⇑(flatSwapCLE M (cNodeOf M g.node hd ⟨g.pivot, hp⟩) d)) w).det|
      = |paramsEquivFlat M w d| ^ (dCenterOfNode M g.node - 1) := by
  rw [abs_det_fderiv_comp_det_one_gauge _ _ (geoChartMap_differentiable g)
      (flatSwapCLE_differentiable M _ d) (flatSwapCLE_abs_det_fderiv_one M _ d) w,
    geoChartMap_fderiv_det g _ hd hp, flatSwapCLE_apply_flat, Equiv.swap_apply_left]

end DLNFibre.DLN.RLCT.Engine
