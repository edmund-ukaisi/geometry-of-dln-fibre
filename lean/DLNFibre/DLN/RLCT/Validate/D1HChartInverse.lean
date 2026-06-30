import DLNFibre.DLN.RLCT.Foundations.S1IFTChart

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartInverse` — the right-inverse-exposing chart corollary

The banked `S1IFTChart.rlctAtOn_eq_of_contDiff_chart_inv` exposes the IFT inverse `Ψsymm` with the
LEFT-inverse identity `Ψsymm (Φ w) = w` (on an open `V ∋ wstar`) and the RLCT transfer
`rlctAtOn f wstar = rlctAtOn (f ∘ Ψsymm) wstar`. The DLN `hchart` wire (#231) needs, in addition,
the RIGHT-inverse germ `Φ (Ψsymm w) = w` *near* `wstar` — what turns the selected loss entries of
`F = lossFlatShift ∘ Ψsymm` into plain coordinates
(`g_{er k}(Ψsymm w) = (Φ (Ψsymm w))_{ec k} = w_{ec k}`).

This corollary supplies it. Both facts come from the SAME public bounded-unit chart
(`exists_boundedUnit_chart_of_contDiffAt`): `Ψsymm wstar = wstar` (the left inverse at `wstar`) and
`Ψsymm` continuous at `wstar` give `Ψsymm w ∈ V` near `wstar`, where `hright` and
`hΨΦ` (`Ψ = Φ` on `V`) combine to `Φ (Ψsymm w) = w`. A bounded re-derivation from the public chart —
no new analytic content beyond the banked IFT chart. STATUS: built sorry-free, axiom-clean.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The right-inverse-exposing chart corollary.** For a `ContDiff ℝ 2` self-map `Φ` of `E` fixing
`wstar` with invertible derivative `f'`, there is a total inverse `Ψsymm : E → E` with the
RIGHT-inverse germ `Φ (Ψsymm w) = w` *eventually near* `wstar`, and
`rlctAtOn f wstar = rlctAtOn (f ∘ Ψsymm) wstar` for any `f`. (Strengthens
`rlctAtOn_eq_of_contDiff_chart_inv`, which exposes only the left inverse `Ψsymm (Φ w) = w`.) The
right-inverse germ is what reads the selected loss entries of `F = f ∘ Ψsymm` off as coordinates. -/
theorem rlctAtOn_eq_of_contDiff_chart_rinv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    (f : E → ℝ) (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar) :
    ∃ (Ψsymm : E → E) (V : Set E), IsOpen V ∧ wstar ∈ V ∧
      ContDiffOn ℝ 2 Ψsymm V ∧
      (∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w) ∧
      rlctAtOn f wstar = rlctAtOn (fun w => f (Ψsymm w)) wstar := by
  obtain ⟨Ψ, Ψsymm, DΨ, DΨsymm, V, hVopen, hwV, hΨfix, hleft, hright, hΨcont, hsymmcont,
    hderiv, hderivsymm, hdetmeas, hdetmeassymm, hbdd, hbddsymm, hΨΦ, hsymmCD⟩ :=
    exists_boundedUnit_chart_of_contDiffAt Φ wstar f' hΦ hΦ' hfix
  -- `Ψsymm wstar = wstar` (the left inverse at `wstar`, with `Ψ wstar = wstar`).
  have hsymmfix : Ψsymm wstar = wstar := by
    have := hleft wstar hwV; rwa [hΨfix] at this
  have hsymmCA : ContinuousAt Ψsymm wstar :=
    (hsymmcont.continuousWithinAt hwV).continuousAt (hVopen.mem_nhds hwV)
  -- `Ψsymm w ∈ V` for `w` near `wstar` (continuity + `Ψsymm wstar = wstar ∈ V`).
  have h2 : ∀ᶠ w in 𝓝 wstar, Ψsymm w ∈ V := by
    have hmem : Ψsymm wstar ∈ V := by rw [hsymmfix]; exact hwV
    exact hsymmCA (hVopen.mem_nhds hmem)
  -- the right-inverse germ: `Φ (Ψsymm w) = Ψ (Ψsymm w) = w`.
  have hrinv : ∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w := by
    filter_upwards [hVopen.mem_nhds hwV, h2] with w hwVmem hsymmVmem
    rw [← hΨΦ _ hsymmVmem]; exact hright w hwVmem
  refine ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hrinv, ?_⟩
  -- the RLCT transfer (the `_inv` body, with these witnesses): germ `f =ᶠ (f∘Ψsymm)∘Φ` on `V`.
  have hinv : ∀ w ∈ V, Ψsymm (Φ w) = w := by
    intro w hw; rw [← hΨΦ w hw]; exact hleft w hw
  have hgerm : f =ᶠ[𝓝 wstar] fun w => (fun w => f (Ψsymm w)) (Φ w) := by
    filter_upwards [hVopen.mem_nhds hwV] with w hwV'
    show f w = f (Ψsymm (Φ w))
    rw [hinv w hwV']
  exact rlctAtOn_eq_of_contDiff_chart f (fun w => f (Ψsymm w)) Φ wstar f' hΦ hΦ' hfix hgerm

end DLNFibre.DLN.RLCT
