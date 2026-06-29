import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Foundations.S1Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction` — the generic ∀M MP box-reduction

The **measure-preserving plumbing** that reduces the flat-coordinate hfin integral
`∫_{routeMBaseNbhd M} |routeMCore M|^{−c'}` to the layer-product box integral
`∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^{−c'}` — for an **arbitrary** width vector `M`, no depth or
output-width restriction. This is the ∀M analog of `routeMCore_M334_le_matBox` (which only worked at
depth `L = 2`, where `prod M A = A0·A1` collapses to a two-matrix product).

## What this file is (and is NOT)

This is the **decision-independent reduction half** of the hfin upper bound, and *only* that:

* `routeMCore_le_matBox` — `∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} ≤ routeMLayerBoxIntegral M c' 1`,
  pure measure-preserving plumbing (open box ⊆ closed cube; transport through `paramsEquivFlat` MP to
  the all-entries-bounded `paramsBoxM`; the loss-at-`0` = `frobSq(prod)` identity). Fully ∀M,
  axiom-clean. NO SchurCore, NO threshold claim.

It does **NOT** claim finiteness of that box integral. The finiteness
`routeMLayerBoxIntegral M c' 1 < ⊤` for `c' < ½·minAdm M` is the genuine ANALYTIC content
(`RouteMBoxThresholdFinite M`, the named hypothesis below) — for general `M` it needs the iterated-fibre
peel or the rank-stratified Schur recursion, and the SchurCore chain discharges it **only** for the
specific `p = 4` binding family (`SchurCore` is hardcoded at the column count `4`; for arbitrary output
width `M (last L)` and the `½·minAdm M` threshold there is no literal ∀M wiring — a category error,
decorrelated-Codex-confirmed). Naming the gap as `RouteMBoxThresholdFinite` keeps the caveat next to the
claim: `routeMCore_threshold_lt_top_of_box` is true ∀M *given* the box finiteness; supplying the box
finiteness is per-family work.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The generic layer-product loss identity and the `Params M` box -/

/-- **The generic zero-target loss identity** `dlnLoss M 0 A = frobSq (prod M A)`: at target `0` the
square-Frobenius loss is the squared Frobenius norm of the layer product. The ∀M form of
`dlnLoss_M334_eq_frobSq` / `dlnLoss_M4422_eq_frobSq`. -/
theorem dlnLoss_zero_eq_frobSq (M : Fin (L + 1) → ℕ) (A : Params M) :
    dlnLoss M 0 A = frobSq (prod M A) := by
  unfold dlnLoss frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- **The `Params M` box** of radius `T`: all layer-matrix entries in `[−T, T]`. The all-entries-bounded
parameter box `cubeBox (flatDim M) T` pulls back to under `paramsEquivFlat`. The ∀M analog of
`paramsBox334`. -/
def paramsBoxM (M : Fin (L + 1) → ℕ) (T : ℝ) : Set (Params M) :=
  {A | ∀ s i j, A s i j ∈ Set.Icc (-T) T}

/-- **The layer-product box integral** `∫_{A ∈ paramsBoxM M T} frobSq(prod M A)^{−c'}` — the
finiteness target of the hfin upper bound, AFTER the MP reduction. The ∀M generalisation of the
two-matrix-box RHS of `routeMCore_M334_le_matBox`. -/
noncomputable def routeMLayerBoxIntegral (M : Fin (L + 1) → ℕ) (c' T : ℝ) : ℝ≥0∞ :=
  ∫⁻ A in paramsBoxM M T, ENNReal.ofReal ((frobSq (prod M A)) ^ (-c'))

/-! ## The flat-decode + box-preimage facts (generic) -/

/-- **The flat decode** `paramsEquivFlat M A (equivFin idx) = A idx.1.1 idx.1.2 idx.2` — a flat
coordinate reads back the layer matrix entry. Generic (`∀ L M`); the `arrowCongr'`/`piCurry`/
`Sigma.uncurry` unfold. (Re-derived locally here to avoid importing the `RouteM334`/`RouteM4422`
Hfin files, which both define a private `paramsEquivFlat_decode` and would collide.) -/
theorem paramsEquivFlat_decodeM (M : Fin (L + 1) → ℕ) (A : Params M) (idx : FlatIdx M) :
    paramsEquivFlat M A (Fintype.equivFin (FlatIdx M) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-- `paramsEquivFlat M ⁻¹' (cubeBox (flatDim M) T) = paramsBoxM M T` — the closed flat cube box pulls
back to the all-entries-bounded `Params` box (the flat decode ranges over all matrix entries). The ∀M
analog of `paramsEquivFlat_preimage_box334`. -/
theorem paramsEquivFlat_preimage_paramsBoxM (M : Fin (L + 1) → ℕ) (T : ℝ) :
    paramsEquivFlat M ⁻¹' (cubeBox (flatDim M) T) = paramsBoxM M T := by
  ext A
  simp only [Set.mem_preimage, cubeBox, paramsBoxM, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq]
  constructor
  · intro h s i j
    have := h (Fintype.equivFin (FlatIdx M) ⟨⟨s, i⟩, j⟩)
    rwa [paramsEquivFlat_decodeM M A ⟨⟨s, i⟩, j⟩] at this
  · intro h k
    obtain ⟨idx, rfl⟩ := (Fintype.equivFin (FlatIdx M)).surjective k
    rw [paramsEquivFlat_decodeM M A idx]
    exact h idx.1.1 idx.1.2 idx.2

/-- `paramsBoxM M T` is measurable (the cube-box preimage of the measurable flattening). -/
theorem measurableSet_paramsBoxM (M : Fin (L + 1) → ℕ) (T : ℝ) :
    MeasurableSet (paramsBoxM M T) := by
  rw [← paramsEquivFlat_preimage_paramsBoxM M T]
  exact ((by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) :
    MeasurableSet (cubeBox (flatDim M) T)).preimage (paramsEquivFlat M).measurable

/-- `routeMCore M` is nonnegative (the loss is a squared Frobenius norm). The ∀M analog of
`routeMCore_M334_nonneg`. -/
theorem routeMCore_nonneg (M : Fin (L + 1) → ℕ) (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ routeMCore M x := by
  rw [routeMCore]; exact dlnLoss_nonneg M 0 _

/-! ## The generic MP box-reduction -/

/-- **The generic ∀M box-reduction (the MP plumbing, S2-FREE).** For `0 < c'`,
`∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} ≤ routeMLayerBoxIntegral M c' 1`. Pure measure-preserving
plumbing, mirroring `routeMCore_M334_le_matBox` steps 1–3 (dominate the open box `(−1,1)^N` by the
closed cube `[−1,1]^N`; transport through `paramsEquivFlat` MP to the `Params M` box `paramsBoxM M 1`;
rewrite the integrand by the loss-at-`0` = `frobSq(prod M A)` identity). NO layer split is performed —
the RHS keeps the full layer product `prod M A`, the ∀M-correct shape (the per-layer split exists only
at fixed depth). Holds for EVERY `c'` (the reduction is pure plumbing, no positivity needed). The
finiteness of the RHS is the SEPARATE analytic content (`RouteMBoxThresholdFinite`). -/
theorem routeMCore_le_matBox (M : Fin (L + 1) → ℕ) (c' : ℝ) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-c'))
      ≤ routeMLayerBoxIntegral M c' 1 := by
  have hopen_sub : flatOpenBox (routeMAmbient M) ⊆ cubeBox (routeMAmbient M) 1 := by
    intro x hx i _
    have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
    rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  -- Step 1: |routeMCore| = routeMCore (nonneg), dominate the open box by the closed cube box.
  have hbound : ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-c'))
      ≤ ∫⁻ x in cubeBox (routeMAmbient M) 1, ENNReal.ofReal (routeMCore M x ^ (-c')) := by
    rw [routeMBaseNbhd]
    refine le_trans (lintegral_mono_set hopen_sub) (le_of_eq ?_)
    refine setLIntegral_congr_fun (by
      rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (fun x _ => ?_)
    rw [abs_of_nonneg (routeMCore_nonneg M x)]
  refine le_trans hbound (le_of_eq ?_)
  -- Step 2: transport the closed cube box via paramsEquivFlat (MP) to paramsBoxM M 1.
  have hcore : ∀ A : Params M,
      routeMCore M (paramsEquivFlat M A) = frobSq (prod M A) := by
    intro A
    rw [congrFun (routeMCore_comp_paramsEquivFlat M) A, dlnLoss_zero_eq_frobSq]
  have hmpF := measurePreserving_paramsEquivFlat M
  rw [routeMLayerBoxIntegral]
  have hpre := hmpF.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (paramsEquivFlat M))
    (fun x => ENNReal.ofReal (routeMCore M x ^ (-c')))
    (cubeBox (routeMAmbient M) 1)
  calc ∫⁻ x in cubeBox (routeMAmbient M) 1, ENNReal.ofReal (routeMCore M x ^ (-c'))
      = ∫⁻ A in (paramsEquivFlat M) ⁻¹' cubeBox (routeMAmbient M) 1,
          ENNReal.ofReal (routeMCore M (paramsEquivFlat M A) ^ (-c')) := hpre.symm
    _ = ∫⁻ A in paramsBoxM M 1, ENNReal.ofReal (frobSq (prod M A) ^ (-c')) := by
        rw [show (paramsEquivFlat M) ⁻¹' cubeBox (routeMAmbient M) 1 = paramsBoxM M 1 from
          paramsEquivFlat_preimage_paramsBoxM M 1]
        refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
        rw [hcore A]

/-! ## The named analytic gap + the re-pointed threshold theorem -/

/-- **The named analytic finiteness hypothesis.** `RouteMBoxThresholdFinite M` asserts that the layer
product box integral is finite below the geometric threshold `½·minAdm M`. This is the genuine open
content of the hfin upper bound — the MP reduction (`routeMCore_le_matBox`) is decision-independent, but
SUPPLYING this finiteness is per-family work (iterated-fibre / Schur recursion; the SchurCore `p = 4`
chain discharges it only for the specific binding family). Named here so the caveat lives beside the
claim it gates. -/
def RouteMBoxThresholdFinite (M : Fin (L + 1) → ℕ) : Prop :=
  ∀ c' : NNReal, (c' : ℝ) < (minAdm M : ℝ) / 2 → routeMLayerBoxIntegral M (c' : ℝ) 1 < ⊤

/-- **The hfin upper bound, GIVEN the box finiteness (∀M, axiom-clean).** For `c' < ½·minAdm M`,
`∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤` — provided the layer-product box integral is finite
(`hbox : RouteMBoxThresholdFinite M`). The `c' = 0` integrand is `(·)^0 = 1`, integral = volume(box)
< ⊤; for `0 < c'` the MP reduction `routeMCore_le_matBox` dominates by `routeMLayerBoxIntegral`, finite
by `hbox`. The general-M analog of `routeMCore_M334_threshold_lt_top`, with the analytic finiteness made
an explicit, named hypothesis rather than hidden. -/
theorem routeMCore_threshold_lt_top_of_box (M : Fin (L + 1) → ℕ)
    (hbox : RouteMBoxThresholdFinite M) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤ := by
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand is (·)^0 = 1, integral = volume(box) < ⊤.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hone : ∀ x, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = 1 := by
      intro x; rw [hzero]; simp [Real.rpow_zero]
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.one_lt_top ?_
    rw [routeMBaseNbhd]
    have hopen_sub : flatOpenBox (routeMAmbient M) ⊆ cubeBox (routeMAmbient M) 1 := by
      intro x hx i _
      have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
      rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    refine lt_of_le_of_lt (measure_mono hopen_sub) ?_
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  · -- 0 < c' < ½·minAdm M: reduce to the box integral, then `hbox`.
    exact lt_of_le_of_lt (routeMCore_le_matBox M (c' : ℝ)) (hbox c' hc')

end DLNFibre.DLN.RLCT
