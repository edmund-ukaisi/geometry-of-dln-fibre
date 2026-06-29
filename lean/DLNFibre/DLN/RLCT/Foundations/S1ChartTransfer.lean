import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1ChartTransfer` — the abstract chart-transfer atom

The network-free core of the D1 `hchart` (Altitude-B): given a loss `f` that, NEAR a basepoint
`wstar`, equals the post-chart form `F ∘ Ψ` for a **bounded-unit local diffeo** `Ψ` FIXING `wstar`,
the RLCT transfers:

    rlctAtOn f wstar = rlctAtOn F wstar.

This is the thin combination of a germ-congruence (`rlctAtOn` is a germ at `wstar`) with the banked
`rlctAtOn_boundedUnit_localHomeomorph` (which strips the bounded-unit chart). The DLN use-site supplies
`Ψ` as the selected-minor IFT chart (`ContDiffAt.toOpenPartialHomeomorph`) and `F = ∑s² + ∑q²` as the
post-chart loss, with the germ equality `f =ᶠ F∘Ψ` from the on-image identity `g_k∘Ψ.symm = s_k`. The
basepoint is the chart-origin once the loss is flattened + translated so `wstar = 0` (the IFT chart
fixes the origin). STATUS: built sorry-free, axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **`rlctAtOn` germ-congruence** (public form of `S1NonMPTransport`'s private
`weightedThreshold_congr_germ_one`). If `f =ᶠ[𝓝 wstar] g`, they have the same local RLCT — `rlctAtOn`
reads only the germ at `wstar`. -/
theorem rlctAtOn_congr_germ {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    [OpensMeasurableSpace M] (f g : M → ℝ) (wstar : M) (hfg : f =ᶠ[𝓝 wstar] g) :
    rlctAtOn f wstar = rlctAtOn g wstar := by
  obtain ⟨U₀, hU₀mem, hU₀⟩ := Filter.eventually_iff_exists_mem.1 hfg
  unfold rlctAtOn weightedThreshold
  have key : ∀ (P Q : M → ℝ), (∀ w ∈ U₀, P w = Q w) → ∀ c : ENNReal,
      (∃ c' : NNReal, c = (c' : ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |P w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) Ω volume) →
      (∃ c' : NNReal, c = (c' : ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |Q w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) Ω volume) := by
    rintro P Q hPQ c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
    have hw0 : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hw0) hU₀mem)
    refine ⟨c', rfl, V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    apply (hint.mono_set (fun x hx => (hVsub hx).1)).congr
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with w hw
    rw [hPQ w (hVsub hw).2]
  congr 1; ext c
  exact ⟨key f g hU₀ c, key g f (fun w hw => (hU₀ w hw).symm) c⟩

/-- **The abstract chart-transfer** (the D1 `hchart` core). If the loss `f` equals the post-chart form
`F ∘ Ψ` on a neighbourhood of `wstar` (`hgerm`), and `Ψ` is a bounded-unit local diffeo fixing `wstar`
(the raw-data `rlctAtOn_boundedUnit_localHomeomorph` package), then `rlctAtOn f wstar = rlctAtOn F
wstar`. The germ-congruence rewrites `f` to `F∘Ψ`; the banked bounded-unit transport strips `Ψ`. -/
theorem rlctAtOn_eq_of_boundedUnit_chart {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (f F : M → ℝ) (wstar : M) (Ψ Ψsymm : M → M)
    (DΨ DΨsymm : M → (M →L[ℝ] M)) (V : Set M)
    (hVopen : IsOpen V) (hwV : wstar ∈ V)
    (hfix : Ψ wstar = wstar)
    (hleft : ∀ w ∈ V, Ψsymm (Ψ w) = w) (hright : ∀ w ∈ V, Ψ (Ψsymm w) = w)
    (hΨcont : ContinuousOn Ψ V) (hsymmcont : ContinuousOn Ψsymm V)
    (hderiv : ∀ w ∈ V, HasFDerivAt Ψ (DΨ w) w)
    (hderivsymm : ∀ w ∈ V, HasFDerivAt Ψsymm (DΨsymm w) w)
    (hdetmeas : Measurable fun w => |(DΨ w).det|)
    (hdetmeassymm : Measurable fun w => |(DΨsymm w).det|)
    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΨ w).det| ∧ |(DΨ w).det| ≤ b)
    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΨsymm w).det| ∧ |(DΨsymm w).det| ≤ b)
    (hgerm : f =ᶠ[𝓝 wstar] fun w => F (Ψ w)) :
    rlctAtOn f wstar = rlctAtOn F wstar := by
  rw [rlctAtOn_congr_germ f (fun w => F (Ψ w)) wstar hgerm]
  exact rlctAtOn_boundedUnit_localHomeomorph F wstar Ψ Ψsymm DΨ DΨsymm V
    hVopen hwV hfix hleft hright hΨcont hsymmcont hderiv hderivsymm
    hdetmeas hdetmeassymm hbdd hbddsymm

end DLNFibre.DLN.RLCT
