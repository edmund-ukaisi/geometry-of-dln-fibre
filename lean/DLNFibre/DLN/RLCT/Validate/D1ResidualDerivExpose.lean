import DLNFibre.DLN.RLCT.Validate.D1HChartResidualC2
import DLNFibre.DLN.RLCT.Validate.D1ResidualJacobianRank
import DLNFibre.Core.ResidualRank

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ResidualDerivExpose` — the `b1` derivative-exposing first peel

The banked first-peel producer `dln_hchart_residual_c2` (`D1HChartResidualC2`) DISCARDS the residual's
Fréchet derivative: it returns only `(q, t0, ContDiff, q(0,t0)=0, RLCT-transfer)`, from which the
Jacobian cannot be recovered. This module builds the `b1` brick of the L = 2 D1 `≥`-leg gate `hrank₂`:
it re-runs the same construction but ADDITIONALLY exposes

    HasFDerivAt (fun t => q (0, t)) L t0

with `L` the explicit composite `readout(DG(0)) ∘ f'.symm ∘ sliceMap` (the residual-vector
differential ∘ the inverse chart derivative ∘ the flat-complement injection), feeds it through the
banked `b1 → b2` bridge (`jacResid_rank_eq_of_hasFDerivAt`), and closes with the network-free `b2`
rank identity (`DLNFibre.Core.residual_finrank_eq`) to get

    (jacResid (q(0,·)) t0).rank = finrank ℝ (range Tresid) − m,

where `Tresid` is the (un-zeroed) flat residual-polynomial Jacobian at the origin. `m = nRegL2 H r`
at the use-site (the number of selected regular directions). The remaining `finrank(range Tresid) − m =
extraCountRect …` count is the separate `b3` middle-stratum piece.

## The chain (locality: `q =ᶠ g₁` near `w0 = splitHomeo 0`, so the slice residual `= g₁(0,·)` near `t0`)

  * `sliceMap t := (splitHomeo hec).symm (0, t)` — LINEAR (a `ContinuousLinearMap`), range exactly the
    flat complement subspace `W = {z : z (ec j) = 0}`; base `sliceMap t0 = 0`.
  * `Ψsymm` — the IFT inverse chart, `HasFDerivAt Ψsymm f'.symm 0` (re-exposed here; the banked
    `_fix` corollary drops it).
  * `G z := rawResidVec … Ψsymm`-as-a-function-of-the-flat-point — `= (residual poly vector) ∘ Ψsymm`,
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

`rlctAtOn_eq_of_contDiff_chart_rinv_fix` (banked) returns `Ψsymm`, its `C²`-ness, `Ψsymm 0 = 0`, the
local right-inverse germ, and the RLCT transfer — but NOT `HasFDerivAt Ψsymm f'.symm 0`. This variant
additionally surfaces that derivative (the `hsymm_hfderiv` internal to the bounded-unit chart). -/

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

end DLNFibre.DLN.RLCT
