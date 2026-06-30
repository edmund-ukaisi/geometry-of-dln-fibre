import DLNFibre.DLN.RLCT.Validate.RouteMTwoSidedReg
import DLNFibre.DLN.RLCT.Validate.RouteMProjV0Gate
import DLNFibre.DLN.RLCT.Validate.RouteMLeafFreeKHeadline

/-!
# `RouteMHDtotConj` — `hDtot` from the two-sided staircase conjugacy of `Dtot` (the assembly wrapper)

The ∀M-L2 capstone `interiorDet_leaf_headline_freeK` (`RouteMLeafFreeKHeadline`) carries one
hypothesis, `hDtot : |det (Dtot ha (pbo u))| = |det K|^(r+c)`. This module records the ASSEMBLY: given
the two-sided staircase conjugacy of `Dtot` — layer-collecting equivs `eIn eOut : E ≃ₗ StairProd V 2`
with `eOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, the regauge abs-det-`1` (`hreg`, discharged by
`RouteMTwoSidedReg.hreg_of_measurePreserving_comp`), and the two diagonal blocks identified as
`f 0 = schurFrameDeriv X K N` (det `|det K|^(r+c)`, the banked Schur frame) and `f 1` det-`1` (the
banked chain unit) — `hDtot` follows from `RouteMStairTwoSided.stairMap_abs_det_twoConj`.

This is the `interiorDet_phiFlatLiveR1_of_stairConj`-analogue at the `Dtot`/`hDtot` level: it banks
the determinant bookkeeping (the keystone + the two diagonal-block dets), reducing `hDtot` to exactly
the GEOMETRIC block identity `hD` + the concrete `eIn`/`eOut` construction (the remaining slot-partition
tide). The two `f`-block det identifications are NOT axioms here — they are discharged from the banked
`schurFrameDeriv_det` and `chainUnit_det`.

* `hDtot_of_twoStairConj` — `hDtot` from `(eIn, eOut, hD, hreg)` + `f 0 = schurFrameDeriv …` (its det
  the engine value) + `|det (f 1)| = 1`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked keystone + Schur/chain dets;
no analysis).
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- **`hDtot` from the two-sided staircase conjugacy of `Dtot`.** Given the two boundary spaces
`V 0 = SchurInc t r c` and `V 1` (the leaf-chain space), the layer-collecting equivs `eIn eOut`, the
staircase identity `hD : eOut ∘ Dtot ∘ eIn.symm = stairMap V 2 f c`, the regauge abs-det-`1` `hreg`,
the layer-0 block `f 0 = schurFrameDeriv X K (readN)` with `|det X-K-N-frame| = |det K|^(r+c)` matched
to `leafKcore`, and the leaf block `|det (f 1)| = 1`, the boundary-factor determinant is the free-K
Schur value `|det K|^(r+c)` — exactly the `hDtot` the capstone consumes.

The det conclusion is `∏_{s:Fin 2} |det (f s)| = |det K|^(r+c) · 1`; `hf0`/`hf1` plug the two block
dets, the keystone `stairMap_abs_det_twoConj` does the rest. -/
theorem hDtot_of_twoStairConj
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V 2)
    (eIn eOut : (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd V 2)
    (hD : (eOut : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd V 2)
        ∘ₗ Dtot ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
        ∘ₗ (eIn.symm : StairProd V 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
      = stairMap V 2 f c)
    (hreg : |LinearMap.det ((eOut.symm : StairProd V 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
        ∘ₗ (eIn : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd V 2))| = 1)
    (hf0 : |LinearMap.det (f 0)|
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)))
    (hf1 : |LinearMap.det (f 1)| = 1) :
    |LinearMap.det (Dtot ha
        (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u))|
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  -- the keystone: `|det Dtot| = ∏_{s:Fin 2} |det (f s)|`
  rw [stairMap_abs_det_twoConj V 2 f c eIn eOut _ hD hreg, Fin.prod_univ_two]
  -- `Fin.prod_univ_two` yields `|det (f ↑0)| * |det (f ↑1)|` with `↑0 = 0`, `↑1 = 1` (defeq); plug
  -- the two block dets `hf0`/`hf1` (the leaf block det `1`).
  show |LinearMap.det (f 0)| * |LinearMap.det (f 1)| = _
  rw [hf0, hf1, mul_one]

/-- **The capstone wired through the `Dtot` conjugacy** — the ∀M-L2 interior-det headline modulo the
GEOMETRIC two-sided staircase conjugacy of `Dtot` (the lone remaining geometric input). Composes
`hDtot_of_twoStairConj` into `interiorDet_leaf_headline_freeK`: the chart Jacobian abs-det is
`|u p₀|^(minAdm−1) · ∏_s engineFreeK_s`, the determinant determined by the staircase conjugacy of the
boundary-factor Jacobian. -/
theorem interiorDet_leaf_headline_of_DtotConj
    (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (ha : StructAdm M (tach M)) (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V 2)
    (eIn eOut : (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd V 2)
    (hD : (eOut : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd V 2)
        ∘ₗ Dtot ha (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u)
        ∘ₗ (eIn.symm : StairProd V 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
      = stairMap V 2 f c)
    (hreg : |LinearMap.det ((eOut.symm : StairProd V 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
        ∘ₗ (eIn : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd V 2))| = 1)
    (hf0 : |LinearMap.det (f 0)|
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)))
    (hf1 : |LinearMap.det (f 1)| = 1) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveAt M ha (by norm_num)
        (leafPivot M ha (by norm_num) h0r h0c)) u).toLinearMap|
      = |u (leafPivot M ha (by norm_num) h0r h0c)| ^ (minAdm M - 1)
        * ∏ s : Fin 2, engineFreeK ha h0r h0c u s :=
  interiorDet_leaf_headline_freeK ha h0r h0c u
    (hDtot_of_twoStairConj V ha h0r h0c u f c eIn eOut hD hreg hf0 hf1)

end L2

end DLNFibre.DLN.RLCT

end
