import DLNFibre.DLN.RLCT.Validate.D1HChartResidualC2
import DLNFibre.DLN.RLCT.Validate.D1ResidualJacobianRank
import DLNFibre.Core.ResidualRank

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ResidualDerivExpose` — the `b1` derivative-exposing first peel

The banked first-peel producer `dln_hchart_residual_c2` (`D1HChartResidualC2`) DISCARDS the
residual's Fréchet derivative: it returns only `(q, t0, ContDiff, q(0,t0)=0, RLCT-transfer)`, from
which the Jacobian cannot be recovered. This module builds the `b1` brick of the L = 2 D1 `≥`-leg
gate `hrank₂`: it re-runs the same construction but ADDITIONALLY exposes

    HasFDerivAt (fun t => q (0, t)) L t0

with `L` the explicit composite `readout(DG(0)) ∘ f'.symm ∘ sliceMap` (the residual-vector
differential ∘ the inverse chart derivative ∘ the flat-complement injection), feeds it through the
banked `b1 → b2` bridge (`jacResid_rank_eq_of_hasFDerivAt`), and closes with the network-free `b2`
rank identity (`DLNFibre.Core.residual_finrank_eq`) to get

    (jacResid (q(0,·)) t0).rank = finrank ℝ (range Tresid) − m,

where `Tresid` is the (un-zeroed) flat residual-polynomial Jacobian at the origin. `m = nRegL2 H r`
at the use-site (the number of selected regular directions). The remaining `finrank(range Tresid)
− m = extraCountRect …` count is the separate `b3` middle-stratum piece.

## The chain (locality: `q =ᶠ g₁` near `w0 = splitHomeo 0`, so the slice residual `= g₁(0,·)`)

  * `sliceMap t := (splitHomeo hec).symm (0, t)` — LINEAR (a `ContinuousLinearMap`), range exactly
    the flat complement subspace `W = {z : z (ec j) = 0}`; base `sliceMap t0 = 0`.
  * `Ψsymm` — the IFT inverse chart, `HasFDerivAt Ψsymm f'.symm 0` (re-exposed here; the banked
    `_fix` corollary drops it).
  * `G z := rawResidVec … Ψsymm`-as-a-flat-point-function — `= (residual poly vector) ∘ Ψsymm`,
    so its outer factor `Gpoly` is `C^∞`, `HasFDerivAt Gpoly (DGpoly 0) 0`.

Chain-ruling `G ∘ Ψsymm ∘ sliceMap` and matching the composite to `b2`'s `zeroSel ∘ T ∘ P⁻¹ ∘ inj`
(with `P = f' = chartFDerivEquiv`, `hP` from `dChartΦcoord_sel`, `hsurj` from the invertible minor)
gives the rank identity. Scope L = 2 (`H : Fin 3 → ℕ`).
-/

open Matrix Module MeasureTheory Set Filter LinearMap
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {m : ℕ} {ec : Fin m → Fin (flatDim H)}
  {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H} {r : ℕ}
  {er : Fin m → Fin (H 0) × Fin (H 2)}

/-! ## The derivative-exposing right-inverse chart corollary

`rlctAtOn_eq_of_contDiff_chart_rinv_fix` (banked) returns `Ψsymm`, its `C²`-ness, `Ψsymm 0 = 0`,
the local right-inverse germ, and the RLCT transfer — but NOT `HasFDerivAt Ψsymm f'.symm 0`. This
variant additionally surfaces that derivative (`hsymm_hfderiv`, internal to the chart). -/

/-- **The right-inverse chart, additionally exposing the inverse derivative.** Same output as
`rlctAtOn_eq_of_contDiff_chart_rinv_fix`, plus `HasFDerivAt Ψsymm (f'.symm) wstar` — the IFT
inverse's derivative, needed to differentiate the residual germ. -/
theorem rlctAtOn_eq_of_contDiff_chart_rinv_fix_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    (f : E → ℝ) (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar) :
    ∃ (Ψsymm : E → E) (V : Set E), IsOpen V ∧ wstar ∈ V ∧
      ContDiffOn ℝ 2 Ψsymm V ∧
      Ψsymm wstar = wstar ∧
      HasFDerivAt Ψsymm (f'.symm : E →L[ℝ] E) wstar ∧
      (∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w) ∧
      rlctAtOn f wstar = rlctAtOn (fun w => f (Ψsymm w)) wstar := by
  obtain ⟨Ψ, Ψsymm, DΨ, DΨsymm, V, hVopen, hwV, hΨfix, hleft, hright, hΨcont, hsymmcont,
    hderiv, hderivsymm, hdetmeas, hdetmeassymm, hbdd, hbddsymm, hΨΦ, hsymmCD, hΨsymm_deriv⟩ :=
    exists_boundedUnit_chart_of_contDiffAt Φ wstar f' hΦ hΦ' hfix
  -- `Ψsymm wstar = wstar` (the left inverse at `wstar`, with `Ψ wstar = wstar`).
  have hsymmfix : Ψsymm wstar = wstar := by
    have := hleft wstar hwV; rwa [hΨfix] at this
  have hsymmCA : ContinuousAt Ψsymm wstar :=
    (hsymmcont.continuousWithinAt hwV).continuousAt (hVopen.mem_nhds hwV)
  have h2 : ∀ᶠ w in 𝓝 wstar, Ψsymm w ∈ V := by
    have hmem : Ψsymm wstar ∈ V := by rw [hsymmfix]; exact hwV
    exact hsymmCA (hVopen.mem_nhds hmem)
  have hrinv : ∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w := by
    filter_upwards [hVopen.mem_nhds hwV, h2] with w hwVmem hsymmVmem
    rw [← hΨΦ _ hsymmVmem]; exact hright w hwVmem
  refine ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hsymmfix, hΨsymm_deriv, hrinv, ?_⟩
  have hinv : ∀ w ∈ V, Ψsymm (Φ w) = w := by
    intro w hw; rw [← hΨΦ w hw]; exact hleft w hw
  have hgerm : f =ᶠ[𝓝 wstar] fun w => (fun w => f (Ψsymm w)) (Φ w) := by
    filter_upwards [hVopen.mem_nhds hwV] with w hwV'
    show f w = f (Ψsymm (Φ w))
    rw [hinv w hwV']
  exact rlctAtOn_eq_of_contDiff_chart f (fun w => f (Ψsymm w)) Φ wstar f' hΦ hΦ' hfix hgerm

/-! ## The flat-complement slice injection `t ↦ splitHomeo.symm (0, t)`

The map `sliceMap t := (splitHomeo hec).symm ((0 : Fin m → ℝ), t)` places the free block `t` on the
complement coordinates and zeroes the selected `ec`-coordinates. It is LINEAR (a `→L`), with range
exactly the flat complement subspace `W = {z : ∀ j, z (ec j) = 0}` — the `inj` `b2` consumes. -/

/-- The flat-complement slice injection as a bare linear map: coordinate `c` reads the complement
block `t` if `c` is unselected, else `0`. Pointwise equal to `t ↦ (splitHomeo hec).symm (0, t)`. -/
noncomputable def sliceMapLin (hec : Function.Injective ec) :
    (Fin (flatDim H - m) → ℝ) →ₗ[ℝ] (Fin (flatDim H) → ℝ) where
  toFun t := fun c => if hc : selPred ec c then 0 else t ((complEquiv hec).symm ⟨c, hc⟩)
  map_add' x y := by
    funext c; by_cases hc : selPred ec c <;> simp [hc]
  map_smul' a x := by
    funext c; by_cases hc : selPred ec c <;> simp [hc]

theorem sliceMapLin_apply (hec : Function.Injective ec) (t : Fin (flatDim H - m) → ℝ)
    (c : Fin (flatDim H)) :
    sliceMapLin hec t c = if hc : selPred ec c then 0 else t ((complEquiv hec).symm ⟨c, hc⟩) := rfl

/-- `sliceMapLin` agrees with `t ↦ (splitHomeo hec).symm (0, t)`. -/
theorem sliceMapLin_eq_splitHomeo_symm (hec : Function.Injective ec)
    (t : Fin (flatDim H - m) → ℝ) :
    sliceMapLin hec t = (splitHomeo hec).symm ((0 : Fin m → ℝ), t) := by
  funext c
  rw [sliceMapLin_apply, splitHomeo_symm_apply]
  by_cases hc : selPred ec c
  · simp only [dif_pos hc]; rfl
  · simp only [dif_neg hc]

/-- The slice injection as a `ContinuousLinearMap` (finite-dim domain). -/
noncomputable def sliceMapCLM (hec : Function.Injective ec) :
    (Fin (flatDim H - m) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ) :=
  (sliceMapLin hec).toContinuousLinearMap

@[simp] theorem sliceMapCLM_apply (hec : Function.Injective ec) (t : Fin (flatDim H - m) → ℝ) :
    sliceMapCLM hec t = sliceMapLin hec t := rfl

theorem sliceMapCLM_coe (hec : Function.Injective ec) :
    ((sliceMapCLM hec : (Fin (flatDim H - m) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ)) :
      (Fin (flatDim H - m) → ℝ) →ₗ[ℝ] (Fin (flatDim H) → ℝ)) = sliceMapLin hec :=
  LinearMap.coe_toContinuousLinearMap _

/-- **`range (sliceMapLin) = W`** — the flat complement subspace `{z : ∀ j, z (ec j) = 0}`. -/
theorem range_sliceMapLin (hec : Function.Injective ec) :
    LinearMap.range (sliceMapLin hec)
      = { z : Fin (flatDim H) → ℝ | ∀ j, z (ec j) = 0 } := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩ j
    rw [sliceMapLin_apply, dif_pos ⟨j, rfl⟩]
  · intro hz
    -- build the preimage: read the complement coordinates of `z`.
    refine ⟨fun i => z ((complEquiv hec) i), ?_⟩
    funext c
    rw [sliceMapLin_apply]
    by_cases hc : selPred ec c
    · rw [dif_pos hc]; obtain ⟨j, rfl⟩ := hc; exact (hz j).symm
    · rw [dif_neg hc, Equiv.apply_symm_apply]

/-! ## The flat residual-polynomial vector and its derivative

`rawResidVec B v er Ψsymm w = residPolyZeroVec (Ψsymm w)`, where `residPolyZeroVec` is a `C^∞`
function of the flat point: the `i`-th coordinate is the `er`-zeroed loss entry
`if selRow er (decode i) then 0 else (prod (gmapAt v z) − B) (decode i)`. Its derivative CLM at the
origin is assembled from the per-entry loss gradients (`hasStrictFDerivAt_lossEntry`). -/

/-- The `er`-zeroed loss-entry residual as a plain-`Pi` vector on the flat space. -/
noncomputable def residPiZero (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (er : Fin m → Fin (H 0) × Fin (H 2)) (z : Fin (flatDim H) → ℝ) : Fin (H 0 * H 2) → ℝ :=
  fun i => if selRow er ((entryIdx H).symm i) then 0
    else (prod H (gmapAt H v z) - B) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2

/-- The `er`-zeroed residual vector as a `EuclideanSpace`-valued map (`toLp` of `residPiZero`). -/
noncomputable def residPolyZeroVec (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (er : Fin m → Fin (H 0) × Fin (H 2)) (z : Fin (flatDim H) → ℝ) :
    EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
  (EuclideanSpace.equiv (Fin (H 0 * H 2)) ℝ).symm (residPiZero B v er z)

/-- `rawResidVec … Ψsymm w = residPolyZeroVec (Ψsymm w)` — the flat residual is `residPolyZeroVec`
precomposed with the chart inverse. -/
theorem rawResidVec_eq_residPolyZeroVec
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ)) (w : Fin (flatDim H) → ℝ) :
    rawResidVec B v er Ψsymm w = residPolyZeroVec B v er (Ψsymm w) := rfl

/-- The `i`-th coordinate of `residPiZero` as a function of `z`. -/
theorem residPiZero_apply (z : Fin (flatDim H) → ℝ) (i : Fin (H 0 * H 2)) :
    residPiZero B v er z i = if selRow er ((entryIdx H).symm i) then 0
      else (prod H (gmapAt H v z) - B) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2 := rfl

/-- The per-coordinate derivative functional of `residPiZero`: `0` on a selected loss entry, the
loss-entry gradient `prodAuxEntryDeriv` otherwise. -/
noncomputable def dResidPiZeroCoord (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (er : Fin m → Fin (H 0) × Fin (H 2)) (i : Fin (H 0 * H 2)) :
    (Fin (flatDim H) → ℝ) →L[ℝ] ℝ :=
  if selRow er ((entryIdx H).symm i) then 0
  else prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
        (Nat.lt_succ_self 2) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2

/-- The assembled plain-`Pi` residual derivative CLM at `0`. -/
noncomputable def dResidPiZero (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (er : Fin m → Fin (H 0) × Fin (H 2)) :
    (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (H 0 * H 2) → ℝ) :=
  ContinuousLinearMap.pi (dResidPiZeroCoord B v er)

/-- **`HasFDerivAt residPiZero (dResidPiZero) 0`** — each coordinate is either the constant `0`
(selected) or the loss entry (with the banked strict gradient), assembled by `hasFDerivAt_pi`. -/
theorem hasFDerivAt_residPiZero :
    HasFDerivAt (residPiZero B v er) (dResidPiZero B v er) (0 : Fin (flatDim H) → ℝ) := by
  classical
  rw [dResidPiZero, hasFDerivAt_pi]
  intro i
  have hcoord : (fun z => residPiZero B v er z i)
      = fun z => if selRow er ((entryIdx H).symm i) then 0
          else (prod H (gmapAt H v z) - B) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2 := by
    funext z; rw [residPiZero_apply]
  rw [hcoord, dResidPiZeroCoord]
  by_cases hsr : selRow er ((entryIdx H).symm i)
  · simp only [if_pos hsr]
    exact hasFDerivAt_const (0 : ℝ) (0 : Fin (flatDim H) → ℝ)
  · simp only [if_neg hsr]
    exact (hasStrictFDerivAt_lossEntry H B v 0
      ((entryIdx H).symm i).1 ((entryIdx H).symm i).2).hasFDerivAt

/-- The `EuclideanSpace`-valued residual derivative CLM at `0`: `dResidPiZero` post-composed with
the `Pi → EuclideanSpace` (`toLp`) continuous linear equiv. -/
noncomputable def dResidPolyZero (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (v : Params H)
    (er : Fin m → Fin (H 0) × Fin (H 2)) :
    (Fin (flatDim H) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
  (((EuclideanSpace.equiv (Fin (H 0 * H 2)) ℝ).symm :
      (Fin (H 0 * H 2) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2))) :
      (Fin (H 0 * H 2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2))).comp
    (dResidPiZero B v er)

/-- **`HasFDerivAt residPolyZeroVec (dResidPolyZero) 0`** — the `toLp` CLM ∘ the plain-`Pi` residual
derivative. -/
theorem hasFDerivAt_residPolyZeroVec :
    HasFDerivAt (residPolyZeroVec B v er) (dResidPolyZero B v er) (0 : Fin (flatDim H) → ℝ) := by
  refine (ContinuousLinearMap.hasFDerivAt
    (((EuclideanSpace.equiv (Fin (H 0 * H 2)) ℝ).symm :
      (Fin (H 0 * H 2) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2))) :
      (Fin (H 0 * H 2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2)))).comp
    0 hasFDerivAt_residPiZero

/-! ## The `b1` producer — the first-peel residual with its slice-residual derivative exposed

Same construction as `dln_hchart_residual_c2` (`D1HChartResidualC2`), routed through the
derivative-exposing chart corollary, so that the output ADDITIONALLY carries the Fréchet derivative
of the slice residual `t ↦ q (0, t)` at its basepoint, spelled as the explicit composite CLM

    residDerivL := dResidPolyZero ∘ f'.symm ∘ sliceMapCLM,

`f' = chartFDerivEquiv`. The germ `q =ᶠ residPolyZeroVec ∘ Ψsymm ∘ splitHomeo.symm` (locality of the
bump) + the chain rule (linear slice ∘ `HasFDerivAt Ψsymm f'.symm 0` ∘ `HasFDerivAt residPolyZeroVec
… 0`) expose it. -/

/-- The explicit slice-residual derivative CLM `dResidPolyZero ∘ f'.symm ∘ sliceMapCLM`. -/
noncomputable def residDerivL (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    (Fin (flatDim H - m) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
  (dResidPolyZero B v er).comp
    (((chartFDerivEquiv H B v er ec hec hminor).symm :
        (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ)).comp (sliceMapCLM hec))

/-- **The `b1` first-peel producer, with the slice-residual derivative exposed.** At an optimal `v`
(`prod v = B`, `rank B = r`) with the invertible flat-Jacobian minor `(er, ec)`, the same first-peel
`C²` residual `q` as `dln_hchart_residual_c2` (slice-vanishing + RLCT transfer), ADDITIONALLY
carrying `HasFDerivAt (fun t => q (0, t)) (residDerivL …) t0`. -/
theorem dln_hchart_residual_c2_deriv (hopt : prod H v = B) (hr : B.rank = r)
    (her : Function.Injective er) (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    ∃ (q : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) → EuclideanSpace ℝ (Fin (H 0 * H 2)))
      (t0 : Fin (flatDim H - m) → ℝ),
      ContDiff ℝ 2 q ∧
      q ((0 : Fin m → ℝ), t0) = 0 ∧
      rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin m → ℝ), t0) ∧
      HasFDerivAt (fun t : Fin (flatDim H - m) → ℝ => q ((0 : Fin m → ℝ), t))
        (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor) t0 := by
  classical
  set Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) := chartΦ H B v er ec with hΦdef
  set f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ) :=
    chartFDerivEquiv H B v er ec hec hminor with hf'def
  have hΦcd : ContDiff ℝ 2 Φ := contDiff_chartΦ
  have hΦ' : HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ)) 0 :=
    hasFDerivAt_chartΦ_equiv hec hminor
  have hfix : Φ 0 = 0 := chartΦ_zero hec
  -- the right-inverse chart, additionally exposing `Ψsymm 0 = 0` AND `HasFDerivAt Ψsymm f'.symm 0`.
  obtain ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hΨ0, hΨsymm_deriv, hrinv, hrlcttransfer⟩ :=
    rlctAtOn_eq_of_contDiff_chart_rinv_fix_deriv (lossFlatShift H B v) Φ 0 f' hΦcd hΦ' hfix
  -- the residual vector, `C²` on `V`.
  have hgCD : ContDiffOn ℝ 2 (rawResidVec B v er Ψsymm) V :=
    contDiffOn_rawResidVec hopt Ψsymm hsymmCD
  set U : Set ((Fin m → ℝ) × (Fin (flatDim H - m) → ℝ)) := splitHomeo hec '' V with hUdef
  have hUopen : IsOpen U := (splitHomeo hec).isOpenMap V hVopen
  set w0 : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) := splitHomeo hec 0 with hw0def
  have hw0U : w0 ∈ U := ⟨0, hwV, rfl⟩
  have hmapsto : Set.MapsTo (splitHomeo hec).symm U V := by
    rintro p ⟨w, hwV', rfl⟩
    rw [Homeomorph.symm_apply_apply]; exact hwV'
  have hsymmContDiff2 : ContDiff ℝ 2 (splitHomeo hec).symm := by
    refine (contDiff_splitHomeo_symm hec).of_le ?_
    rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg1CD : ContDiffOn ℝ 2
      (fun p => rawResidVec B v er Ψsymm ((splitHomeo hec).symm p)) U := by
    have := hgCD.comp (hsymmContDiff2.contDiffOn (s := U)) hmapsto
    exact this
  -- bump-globalise at `(n := 2)`: `q` global `C²`, `=ᶠ g₁` near `w0`.
  obtain ⟨q, hqCD, hqeq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffOn (n := 2) hUopen hw0U hg1CD
  -- `splitHomeo 0 = (0, w0.2)`.
  have hfst : (splitHomeo hec (0 : Fin (flatDim H) → ℝ)).1 = (0 : Fin m → ℝ) := by
    funext k; rw [splitHomeo_fst_apply hec 0 k]; rfl
  have hsh : splitHomeo hec (0 : Fin (flatDim H) → ℝ)
      = ((0 : Fin m → ℝ), (splitHomeo hec 0).2) := Prod.ext hfst rfl
  have hw0eq : ((0 : Fin m → ℝ), w0.2) = w0 := by rw [hw0def, hsh]
  refine ⟨q, w0.2, hqCD, ?_, ?_, ?_⟩
  · -- slice-vanishing: `q (0, t0) = q w0 = rawResidVec … 0 = 0`.
    rw [hw0eq]
    have hqw0 : q w0 = rawResidVec B v er Ψsymm ((splitHomeo hec).symm w0) := hqeq.self_of_nhds
    rw [hqw0, hw0def, Homeomorph.symm_apply_apply,
      rawResidVec_zero_of_optimal hopt Ψsymm hΨ0]
  · -- the RLCT chart transfer (verbatim the `dln_hchart_residual_c2` assembly).
    set F : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) → ℝ :=
      fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2) with hFdef
    have hkey : (fun w => F (splitHomeo hec w)) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
        fun w => lossFlatShift H B v (Ψsymm w) := by
      have hqpull : (fun w => q (splitHomeo hec w)) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
          fun w => rawResidVec B v er Ψsymm w := by
        have hcont : ContinuousAt (splitHomeo hec) 0 := (splitHomeo hec).continuous.continuousAt
        have := hcont.eventually hqeq
        filter_upwards [this] with w hw
        rw [hw, Homeomorph.symm_apply_apply]
      have hgA := germA hopt her hec Ψsymm hrinv
      filter_upwards [hqpull, hgA] with w hwq hwA
      change (∑ i, (splitHomeo hec w).1 i ^ 2) + (∑ i, q (splitHomeo hec w) i ^ 2)
        = lossFlatShift H B v (Ψsymm w)
      have hsel : (∑ i, (splitHomeo hec w).1 i ^ 2) = ∑ k : Fin m, (w (ec k)) ^ 2 := by
        apply Finset.sum_congr rfl; intro k _; rw [splitHomeo_fst_apply hec w k]
      have hresid : (∑ i, q (splitHomeo hec w) i ^ 2)
          = ∑ ij : Fin (H 0) × Fin (H 2), (rawResid B v er Ψsymm w ij) ^ 2 := by
        rw [show (fun i => q (splitHomeo hec w) i ^ 2)
            = fun i => rawResidVec B v er Ψsymm w i ^ 2 from by rw [hwq]]
        rw [show (∑ i, rawResidVec B v er Ψsymm w i ^ 2)
            = ∑ i, (rawResid B v er Ψsymm w ((entryIdx H).symm i)) ^ 2 from by
          apply Finset.sum_congr rfl; intro i _; rw [rawResidVec_apply]]
        exact Equiv.sum_comp (entryIdx H).symm (fun ij => (rawResid B v er Ψsymm w ij) ^ 2)
      rw [hsel, hresid, ← hwA]
    rw [rlctAt_eq_rlctAtOn_lossFlatShift H B v, hrlcttransfer]
    rw [← rlctAtOn_congr_germ (fun w => F (splitHomeo hec w))
      (fun w => lossFlatShift H B v (Ψsymm w)) 0 hkey]
    rw [rlctAtOn_comp_homeomorph (splitHomeo hec) (splitHomeo_mp hec) (splitHomeo_emb hec) F 0]
    rw [hsh]
  · -- THE DERIVATIVE: chain-rule `residPolyZeroVec ∘ Ψsymm ∘ sliceMap`, congr to `q (0, ·)`.
    -- base points: `sliceMap w0.2 = 0`, `Ψsymm 0 = 0`.
    have hslice0 : (splitHomeo hec).symm ((0 : Fin m → ℝ), w0.2) = 0 := by
      rw [hw0eq, hw0def, Homeomorph.symm_apply_apply]
    -- `HasFDerivAt sliceMap (sliceMapCLM) w0.2`.
    have hsliceFD : HasFDerivAt (fun t : Fin (flatDim H - m) → ℝ =>
        (splitHomeo hec).symm ((0 : Fin m → ℝ), t)) (sliceMapCLM hec) w0.2 := by
      have h := (sliceMapCLM hec).hasFDerivAt (x := w0.2)
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with t
      rw [sliceMapCLM_apply, sliceMapLin_eq_splitHomeo_symm]
    -- `HasFDerivAt Ψsymm f'.symm (sliceMap w0.2 = 0)`.
    have hΨFD : HasFDerivAt Ψsymm (f'.symm : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
        ((splitHomeo hec).symm ((0 : Fin m → ℝ), w0.2)) := by
      rw [hslice0]; exact hΨsymm_deriv
    -- `HasFDerivAt residPolyZeroVec dResidPolyZero (Ψsymm (sliceMap w0.2) = 0)`.
    have hGFD : HasFDerivAt (residPolyZeroVec B v er) (dResidPolyZero B v er)
        (Ψsymm ((splitHomeo hec).symm ((0 : Fin m → ℝ), w0.2))) := by
      rw [hslice0, hΨ0]; exact hasFDerivAt_residPolyZeroVec
    -- compose
    have hcompFD : HasFDerivAt
        (fun t : Fin (flatDim H - m) → ℝ =>
          residPolyZeroVec B v er (Ψsymm ((splitHomeo hec).symm ((0 : Fin m → ℝ), t))))
        (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor) w0.2 := by
      have hcomp := (hGFD.comp w0.2 (hΨFD.comp w0.2 hsliceFD))
      -- identify the composite CLM with `residDerivL`.
      have hLeq : (dResidPolyZero B v er).comp
          ((f'.symm : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ)).comp (sliceMapCLM hec))
          = residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor := by
        rw [residDerivL, hf'def]
      rw [← hLeq]; exact hcomp
    -- germ: `q (0, ·) =ᶠ residPolyZeroVec ∘ Ψsymm ∘ sliceMap` near `w0.2`.
    refine hcompFD.congr_of_eventuallyEq ?_
    -- `t ↦ (0, t)` continuous, sends `w0.2 ↦ (0, w0.2) = w0`; pull back `q =ᶠ g₁`.
    have hcontIncl : ContinuousAt (fun t : Fin (flatDim H - m) → ℝ => ((0 : Fin m → ℝ), t)) w0.2 :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hqeq0 : (fun p => q p)
        =ᶠ[𝓝 ((0 : Fin m → ℝ), w0.2)]
          fun p => rawResidVec B v er Ψsymm ((splitHomeo hec).symm p) := by
      rw [hw0eq]; exact hqeq
    have hpull : (fun t : Fin (flatDim H - m) → ℝ => q ((0 : Fin m → ℝ), t))
        =ᶠ[𝓝 w0.2]
          fun t => rawResidVec B v er Ψsymm ((splitHomeo hec).symm ((0 : Fin m → ℝ), t)) :=
      hcontIncl.eventually hqeq0
    refine hpull.trans ?_
    filter_upwards with t
    rw [rawResidVec_eq_residPolyZeroVec]

end DLNFibre.DLN.RLCT
