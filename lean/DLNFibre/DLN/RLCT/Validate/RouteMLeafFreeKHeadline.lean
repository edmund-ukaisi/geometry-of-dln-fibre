import DLNFibre.DLN.RLCT.Validate.RouteMLeafReduce

/-!
# `RouteMLeafFreeKHeadline` — the ∀M-L2 interior-det headline with the HONEST free-K Schur engine

Wires the honest engine `engineFreeK` and the `paramsEquivFlat`-stripping reduction
(`Bchart_abs_det_eq_Dtot`) into the capstone `interiorDet_leaf_headline_Bchart`, reducing its open
`hdet` hypothesis to the single, sharp `Params M`-level determinant fact
`|det (Dtot ha (pbo u))| = |det K|^(r+c)` (the free-K Schur frame determinant). This is strictly
SHARPER than the original `hdet`: the opaque `|det DB|` is replaced by the explicit free-K Schur
value, and the measure-preserving `paramsEquivFlat` reindex is discharged.

* `interiorDet_leaf_headline_freeK` — `|det Dφ| = |u p₀|^(minAdm−1) · ∏_s engineFreeK_s`, modulo
  `hDtot : |det (Dtot ha (pbo u))| = engineFreeK_0`.

The remaining obligation `hDtot` is the staircase-determinant of the boundary-factor Jacobian: the
endomorphism `Dtot = paramsEquivFlat ∘ (fderiv BparamsLeaf)` regrouped into the two boundary blocks
is block-(lower)-triangular with diagonal blocks `schurFrameDeriv` (det `|det K|^(r+c)`) and the
det-`1` chain-unit, the shared `N`-coupling strictly off-diagonal (det-invisible). It discharges via
`RouteMStairTwoSided.stairMap_abs_det_twoConj` once the two layer-collecting equivs `eIn/eOut`
(the `frameB`-generalization) are built — the heavy entry-Jacobian regrouping, NOT yet ∀M.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring; no analysis beyond the
chain rule the reduction already uses).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- **The ∀M-L2 interior-det headline with the honest free-K Schur engine**, modulo the single
boundary-factor determinant `hDtot : |det (Dtot ha (pbo u))| = engineFreeK_0`. The chart Jacobian
abs-det is `|u p₀|^(minAdm−1) · ∏_s engineFreeK_s` with `engineFreeK` the explicit free-K Schur
value (`|det K|^(r+c)` at boundary 0, `1` at the leaf). Wires `Bchart_abs_det_eq_Dtot` (stripping
`paramsEquivFlat`) into `interiorDet_leaf_headline_Bchart`. -/
theorem interiorDet_leaf_headline_freeK (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (hDtot : |LinearMap.det (Dtot ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u))|
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2))) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveAt M ha (by norm_num)
        (leafPivot M ha (by norm_num) h0r h0c)) u).toLinearMap|
      = |u (leafPivot M ha (by norm_num) h0r h0c)| ^ (minAdm M - 1)
        * ∏ s : Fin 2, engineFreeK ha h0r h0c u s := by
  refine interiorDet_leaf_headline_Bchart ha h0r h0c u (engineFreeK ha h0r h0c u) ?_
  -- `hdet`: strip `paramsEquivFlat` (Bchart_abs_det_eq_Dtot), collapse the product, then `hDtot`.
  rw [Bchart_abs_det_eq_Dtot ha _, engineFreeK_prod, hDtot]

end L2

end DLNFibre.DLN.RLCT
