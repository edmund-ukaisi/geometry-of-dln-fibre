import DLNFibre.DLN.RLCT.Foundations.S1ChartTransfer
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1IFTChart` — the bounded-unit IFT chart constructor

The constructor leg of the D1 `hchart` (Altitude-B, spec §SEL): from a `C¹` map `Φ : E → E` (`E` a
finite-dim real normed space) with an INVERTIBLE derivative `f' : E ≃L[ℝ] E` at `wstar`, package the
C^r inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`) into the bounded-unit local
diffeo data the `rlctAtOn_boundedUnit_localHomeomorph` / `rlctAtOn_eq_of_boundedUnit_chart` consume.

The `det DΨ ≠ 0` near `wstar` is PROVEN, not posited: `Φ`'s fderiv at `wstar` is the equiv `f'`
(`det f' ≠ 0`), `fderiv ℝ Φ` is continuous (`C¹`), so `|det (fderiv ℝ Φ ·)|` is continuous and
nonzero at `wstar` — hence bounded above & below by positives on a small closed ball ⊆ the source
(continuity + `ContinuousAt.eventually_ne` + compact-ball inf/sup). This is the §SEL "denominator-D
nonvanishing" obligation, discharged generically from the IFT (no rank-exact-pivot dependence).

STATUS: built sorry-free, axiom-clean. The DLN use-site supplies `Φ = (selected gradient minors,
complement projection)` with `f'` the block-invertible derivative (the (H_indep) content).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **Bounded-unit `|d|` on a ball from local continuity + nonvanishing-at-a-point.** A function
`d : E → ℝ` (`E` finite-dim) continuous on an open `U ∋ wstar` with `d wstar ≠ 0` is bounded away
from
`0` and above on a small closed ball ⊆ `U`: `∃ V open ∋ wstar, ∃ a b, 0 < a ∧ ∀ w ∈ V, a ≤ |d w| ∧
|d w| ≤ b`. (`ContinuousWithinAt`/`eventually_ne` gives a sub-ball where `|d| ≠ 0`; shrink to a
compact
closed ball `B ⊆ U`; `|d|` continuous on `B` attains a positive min and a max.) The reusable
det-bound
kernel for the IFT chart — local because `fderiv` is only continuous on a nbhd of `wstar`. -/
theorem exists_boundedUnit_nbhd_of_continuousOn_ne {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E → ℝ) (U : Set E) (hUopen : IsOpen U) (wstar : E) (hwU : wstar ∈ U)
    (hd : ContinuousOn d U) (hne : d wstar ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ wstar ∈ V ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |d w| ∧ |d w| ≤ b := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hdabs : ContinuousOn (fun w => |d w|) U := hd.abs
  have hne_abs : |d wstar| ≠ 0 := abs_ne_zero.mpr hne
  -- `|d| ≠ 0` near `wstar` within `U`; intersect with `U` to get an open `V₀ ⊆ U` where `|d| ≠ 0`.
  have hev : ∀ᶠ w in 𝓝 wstar, |d w| ≠ 0 := by
    have hca : ContinuousAt (fun w => |d w|) wstar :=
      (hdabs.continuousWithinAt hwU).continuousAt (hUopen.mem_nhds hwU)
    exact hca.eventually_ne hne_abs
  obtain ⟨V₁, hV₁sub, hV₁open, hwV₁⟩ := mem_nhds_iff.1 hev
  set V₀ : Set E := U ∩ V₁ with hV₀
  have hV₀open : IsOpen V₀ := hUopen.inter hV₁open
  have hwV₀ : wstar ∈ V₀ := ⟨hwU, hwV₁⟩
  -- a closed ball `B = closedBall wstar ρ' ⊆ V₀`, compact.
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hV₀open wstar hwV₀
  set ρ' : ℝ := ρ / 2 with hρ'
  have hρ'pos : 0 < ρ' := by positivity
  set B : Set E := Metric.closedBall wstar ρ' with hB
  have hBsub : B ⊆ V₀ := by
    intro w hw
    rw [hB, Metric.mem_closedBall] at hw
    exact hρsub (by rw [Metric.mem_ball]; linarith)
  have hBcompact : IsCompact B := isCompact_closedBall _ _
  have hBne : B.Nonempty := ⟨wstar, Metric.mem_closedBall_self (le_of_lt hρ'pos)⟩
  -- `|d|` is continuous on `B ⊆ U`; attains a min `a` and max `b`.
  have hdabsB : ContinuousOn (fun w => |d w|) B :=
    hdabs.mono (fun w hw => (hBsub hw).1)
  obtain ⟨xmin, hxminB, hxmin⟩ := hBcompact.exists_isMinOn hBne hdabsB
  obtain ⟨xmax, hxmaxB, hxmax⟩ := hBcompact.exists_isMaxOn hBne hdabsB
  set a : ℝ := |d xmin| with ha
  set b : ℝ := |d xmax| with hb
  have hapos : 0 < a := by
    rw [ha]
    refine lt_of_le_of_ne (abs_nonneg _) (Ne.symm ?_)
    exact (hV₁sub (hBsub hxminB).2)
  refine ⟨Metric.ball wstar ρ', Metric.isOpen_ball, Metric.mem_ball_self hρ'pos, a, b, hapos, ?_⟩
  intro w hw
  have hwB : w ∈ B := Metric.ball_subset_closedBall hw
  exact ⟨hxmin hwB, hxmax hwB⟩

/-- **The bounded-unit IFT chart package.** From a `C¹` (here `C^∞`-friendly) map `Φ : E → E`
with an
invertible derivative `f' : E ≃L[ℝ] E` at `wstar`, the C^r IFT gives an `OpenPartialHomeomorph` `Ψ`
with `Ψ = Φ` on its (open) source `∋ wstar` and a `ContDiff` inverse; its `|det (fderiv Φ ·)|` is
bounded-unit on a nbhd of `wstar`. This bundles EXACTLY the raw data
`rlctAtOn_eq_of_boundedUnit_chart` consumes:

    ∃ Ψ Ψsymm DΨ DΨsymm V, IsOpen V ∧ wstar ∈ V ∧ Ψ wstar = wstar ∧ (inverse identities on V) ∧
      ContinuousOn Ψ V ∧ ContinuousOn Ψsymm V ∧ (HasFDerivAt on V, both) ∧
      (|det| measurable, both) ∧ (bounded-unit on V, both) ∧ (∀ w ∈ V, Ψ w = Φ w).

`hfix` (`Φ wstar = wstar`) is carried: the DLN use-site translates so the basepoint is the origin
and
arranges `Φ 0 = 0`. The chart `Ψ`'s forward `= Φ` on `V` (`hΨΦ`) lets the use-site identify the
post-chart loss `F∘Ψ = F∘Φ` for the germ equality. -/
theorem exists_boundedUnit_chart_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar) :
    ∃ (Ψ Ψsymm : E → E) (DΨ DΨsymm : E → (E →L[ℝ] E)) (V : Set E),
      IsOpen V ∧ wstar ∈ V ∧ Ψ wstar = wstar ∧
      (∀ w ∈ V, Ψsymm (Ψ w) = w) ∧ (∀ w ∈ V, Ψ (Ψsymm w) = w) ∧
      ContinuousOn Ψ V ∧ ContinuousOn Ψsymm V ∧
      (∀ w ∈ V, HasFDerivAt Ψ (DΨ w) w) ∧ (∀ w ∈ V, HasFDerivAt Ψsymm (DΨsymm w) w) ∧
      (Measurable fun w => |(DΨ w).det|) ∧ (Measurable fun w => |(DΨsymm w).det|) ∧
      (∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΨ w).det| ∧ |(DΨ w).det| ≤ b) ∧
      (∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(DΨsymm w).det| ∧ |(DΨsymm w).det| ≤ b) ∧
      (∀ w ∈ V, Ψ w = Φ w) ∧
      ContDiffOn ℝ 2 Ψsymm V ∧
      HasFDerivAt Ψsymm (f'.symm : E →L[ℝ] E) wstar := by
  classical
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by decide
  have hΦat : ContDiffAt ℝ 2 Φ wstar := hΦ.contDiffAt
  -- the IFT chart `h : OpenPartialHomeomorph E E`, `h = Φ` on `h.source`.
  set h := hΦat.toOpenPartialHomeomorph Φ hΦ' hn with hh
  have hcoe : (h : E → E) = Φ := hΦat.toOpenPartialHomeomorph_coe hΦ' hn
  have hwsrc : wstar ∈ h.source := hΦat.mem_toOpenPartialHomeomorph_source hΦ' hn
  have hΦwtgt : Φ wstar ∈ h.target := hΦat.image_mem_toOpenPartialHomeomorph_target hΦ' hn
  have hwtgt : wstar ∈ h.target := by rw [← hfix]; exact hΦwtgt
  -- `Φ` is `C¹` globally ⟹ `fderiv ℝ Φ` is globally continuous (kills the `Ψ`-side
  -- measurability/diff).
  have hΦcont1 : Continuous (fun w => fderiv ℝ Φ w) :=
    hΦ.continuous_fderiv (by decide)
  have hΦdiffG : Differentiable ℝ Φ := hΦ.differentiable (by decide)
  -- the inverse `h.symm` is `C²` at `Φ wstar = wstar` (IFT) (GAP-5: term-mode `▸`, avoids motive
  -- error).
  have hsymmAt : ContDiffAt ℝ 2 (h.symm : E → E) wstar := hfix ▸ hΦat.to_localInverse hΦ' hn
  -- a nbhd `Usymm'` where `h.symm` is `ContDiffOn` (GAP-2: `ContDiffAt.contDiffOn`).
  obtain ⟨Usymm, hUsymm_mem, hUsymm_cd⟩ := hsymmAt.contDiffOn (le_refl 2) (by decide)
  obtain ⟨Usymm', hUsymm'sub, hUsymm'open, hwUsymm'⟩ := mem_nhds_iff.1 hUsymm_mem
  have hUsymm'_cd : ContDiffOn ℝ 2 (h.symm : E → E) Usymm' := hUsymm_cd.mono hUsymm'sub
  -- `h.symm`'s fderiv is continuous on `Usymm'` (GAP-3), and its det at `wstar` is `det f'.symm
  -- ≠ 0`.
  have hsymm_fderiv_contOn : ContinuousOn (fun w => fderiv ℝ (h.symm : E → E) w) Usymm' :=
    hUsymm'_cd.continuousOn_fderiv_of_isOpen hUsymm'open (by norm_num)
  -- the IFT inverse derivative at `Φ wstar` is `f'.symm` (GAP-1a).
  have hsymm_hfderiv : HasFDerivAt (h.symm : E → E) (f'.symm : E →L[ℝ] E) wstar := by
    have hstrict : HasStrictFDerivAt (hΦat.localInverse hΦ' hn) (f'.symm : E →L[ℝ] E) (Φ wstar) :=
      (hΦat.hasStrictFDerivAt' hΦ' hn).to_localInverse
    have : HasFDerivAt (h.symm : E → E) (f'.symm : E →L[ℝ] E) (Φ wstar) := hstrict.hasFDerivAt
    rwa [hfix] at this
  -- both det-bound nbhds, computed UP FRONT so they fold into `V`.
  have hdetΦ_ne : (fderiv ℝ Φ wstar).det ≠ 0 := by
    rw [hΦ'.fderiv]
    have : (f' : E →L[ℝ] E).det = LinearMap.det (f'.toLinearEquiv : E →ₗ[ℝ] E) := rfl
    rw [this]; exact (LinearEquiv.isUnit_det' f'.toLinearEquiv).ne_zero
  have hdetS_ne : (fderiv ℝ (h.symm : E → E) wstar).det ≠ 0 := by
    rw [hsymm_hfderiv.fderiv]
    have : (f'.symm : E →L[ℝ] E).det = LinearMap.det (f'.symm.toLinearEquiv : E →ₗ[ℝ] E) := rfl
    rw [this]; exact (LinearEquiv.isUnit_det' f'.symm.toLinearEquiv).ne_zero
  obtain ⟨VΦ, hVΦopen, hwVΦ, aΦ, bΦ, haΦpos, hbndΦ⟩ :=
    exists_boundedUnit_nbhd_of_continuousOn_ne (fun w => (fderiv ℝ Φ w).det) Set.univ isOpen_univ
      wstar (Set.mem_univ _) (ContinuousLinearMap.continuous_det.comp hΦcont1).continuousOn hdetΦ_ne
  obtain ⟨VS, hVSopen, hwVS, aS, bS, haSpos, hbndS⟩ :=
    exists_boundedUnit_nbhd_of_continuousOn_ne (fun w => (fderiv ℝ (h.symm : E → E) w).det) Usymm'
      hUsymm'open wstar hwUsymm'
      (ContinuousLinearMap.continuous_det.comp_continuousOn' hsymm_fderiv_contOn) hdetS_ne
  -- `V := source ∩ target ∩ Usymm' ∩ VΦ ∩ VS` (open, `∋ wstar`; the det bounds hold on `V` by ⊆).
  set V : Set E := ((h.source ∩ h.target ∩ Usymm') ∩ VΦ) ∩ VS with hV
  have hVopen : IsOpen V :=
    (((h.open_source.inter h.open_target).inter hUsymm'open).inter hVΦopen).inter hVSopen
  have hwV : wstar ∈ V := ⟨⟨⟨⟨hwsrc, hwtgt⟩, hwUsymm'⟩, hwVΦ⟩, hwVS⟩
  -- the symm-side derivative choice: `fderiv h.symm` on `Usymm'`, `0` outside (globally
  -- measurable).
  set DΨs : E → (E →L[ℝ] E) :=
    fun w => if w ∈ Usymm' then fderiv ℝ (h.symm : E → E) w else 0 with hDΨs
  refine ⟨(h : E → E), (h.symm : E → E), (fun w => fderiv ℝ Φ w), DΨs, V, hVopen, hwV,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact hfix
  · intro w hw; exact h.left_inv hw.1.1.1.1
  · intro w hw; exact h.right_inv hw.1.1.1.2
  · exact h.continuousOn.mono (fun w hw => hw.1.1.1.1)
  · exact h.continuousOn_symm.mono (fun w hw => hw.1.1.1.2)
  · -- `HasFDerivAt Ψ (fderiv Φ w) w` on `V`: `Ψ = Φ`, `Φ` differentiable.
    intro w _
    have : HasFDerivAt (h : E → E) (fderiv ℝ Φ w) w := by
      rw [hcoe]; exact (hΦdiffG w).hasFDerivAt
    exact this
  · -- `HasFDerivAt Ψsymm (DΨs w) w` on `V`: `w ∈ Usymm'`, so `DΨs w = fderiv h.symm w`.
    intro w hw
    have hwU : w ∈ Usymm' := hw.1.1.2
    have hdiff : DifferentiableAt ℝ (h.symm : E → E) w :=
      (hUsymm'_cd.differentiableOn (by norm_num)).differentiableAt (hUsymm'open.mem_nhds hwU)
    rw [hDΨs]; simp only [hwU, if_true]; exact hdiff.hasFDerivAt
  · -- `|det (fderiv Φ ·)|` measurable (global continuity of `fderiv Φ`).
    exact ((ContinuousLinearMap.continuous_det.comp hΦcont1).abs).measurable
  · -- `|det (DΨs ·)|` measurable: piecewise — `fderiv h.symm` on open `Usymm'`, `0` outside.
    have hcontOn : ContinuousOn (fun w => |(fderiv ℝ (h.symm : E → E) w).det|) Usymm' :=
      (ContinuousLinearMap.continuous_det.comp_continuousOn' hsymm_fderiv_contOn).abs
    have hcont0 : Continuous (fun _ : E => |(0 : E →L[ℝ] E).det|) := continuous_const
    have heq : (fun w => |(DΨs w).det|)
        = Usymm'.piecewise (fun w => |(fderiv ℝ (h.symm : E → E) w).det|)
            (fun _ => |(0 : E →L[ℝ] E).det|) := by
      funext w; rw [hDΨs, Set.piecewise]; by_cases hw : w ∈ Usymm' <;> simp [hw]
    rw [heq]
    exact hcontOn.measurable_piecewise hcont0.continuousOn hUsymm'open.measurableSet
  · -- bounded-unit `|det (fderiv Φ ·)|` on `V ⊆ VΦ`.
    exact ⟨aΦ, bΦ, haΦpos, fun w hw => hbndΦ w hw.1.2⟩
  · -- bounded-unit `|det (DΨs ·)|` on `V ⊆ Usymm' ∩ VS`: `DΨs = fderiv h.symm` there.
    refine ⟨aS, bS, haSpos, fun w hw => ?_⟩
    have hwU : w ∈ Usymm' := hw.1.1.2
    have hdeq : (DΨs w).det = (fderiv ℝ (h.symm : E → E) w).det := by
      rw [hDΨs]; simp only [hwU, if_true]
    rw [hdeq]; exact hbndS w hw.2
  · intro w _; rw [hcoe]
  · -- `ContDiffOn ℝ 2 Ψsymm V`: `Ψsymm = h.symm` is `C²` on `Usymm' ⊇ V`.
    exact hUsymm'_cd.mono (fun w hw => hw.1.1.2)
  · -- `HasFDerivAt Ψsymm (f'.symm) wstar`: the IFT inverse derivative (already computed above).
    exact hsymm_hfderiv

/-! ## The abstract `hchart` — chart-transfer from a `ContDiff` map with invertible derivative

Chains the IFT-chart constructor with the banked chart-transfer atom: a `ContDiff ℝ 2` map `Φ`
fixing `wstar` with invertible derivative, plus the post-chart germ identity `f =ᶠ F∘Φ`, gives the
RLCT transfer `rlctAtOn f wstar = rlctAtOn F wstar`. This is the network-free `hchart` the DLN
use-site instantiates with `Φ = (selected gradient minors − minors(v), complement projection)` (the
§SEL selected-minor map) and `F = ∑s² + ∑q²` (the post-chart loss). -/

/-- **The abstract `hchart`.** For a `ContDiff ℝ 2` self-map `Φ : E → E` (`E` finite-dim real
normed) fixing `wstar` with an invertible derivative `f' : E ≃L[ℝ] E` there, if the loss `f` equals
the post-chart form `F ∘ Φ` on a neighbourhood of `wstar` (`hgerm`), then `rlctAtOn f wstar =
rlctAtOn F wstar`. The IFT chart `Ψ` (= `Φ` on its source) is a bounded-unit local diffeo (`det ≠ 0`
proven from `f'`); the germ `f =ᶠ F∘Φ =ᶠ F∘Ψ` (since `Ψ = Φ` on the open source) feeds the
transport. -/
theorem rlctAtOn_eq_of_contDiff_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    (f F : E → ℝ) (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar)
    (hgerm : f =ᶠ[𝓝 wstar] fun w => F (Φ w)) :
    rlctAtOn f wstar = rlctAtOn F wstar := by
  obtain ⟨Ψ, Ψsymm, DΨ, DΨsymm, V, hVopen, hwV, hΨfix, hleft, hright, hΨcont, hsymmcont,
    hderiv, hderivsymm, hdetmeas, hdetmeassymm, hbdd, hbddsymm, hΨΦ, _, _⟩ :=
    exists_boundedUnit_chart_of_contDiffAt Φ wstar f' hΦ hΦ' hfix
  -- the germ `f =ᶠ F∘Ψ`: on the open `V ∋ wstar`, `Ψ = Φ`, and `f =ᶠ F∘Φ` (hgerm).
  have hgermΨ : f =ᶠ[𝓝 wstar] fun w => F (Ψ w) := by
    filter_upwards [hgerm, hVopen.mem_nhds hwV] with w hw hwV'
    rw [hw, hΨΦ w hwV']
  exact rlctAtOn_eq_of_boundedUnit_chart f F wstar Ψ Ψsymm DΨ DΨsymm V hVopen hwV hΨfix
    hleft hright hΨcont hsymmcont hderiv hderivsymm hdetmeas hdetmeassymm hbdd hbddsymm hgermΨ

/-- **The inverse-exposing `hchart`** (route (3), Codex's design pass). For a `ContDiff ℝ 2`
self-map `Φ : E → E` fixing `wstar` with invertible derivative `f' : E ≃L[ℝ] E`, the IFT inverse
`Ψsymm`
exists as a total `E → E` map that locally inverts `Φ` on an open `V ∋ wstar` (`hinv`), and for ANY
`f`, `rlctAtOn f wstar = rlctAtOn (f ∘ Ψsymm) wstar`. So the post-chart form is `f ∘ Ψsymm` — the
chart inverse is EXPOSED, letting the DLN use-site read off the selected-coordinate structure (the
selected `g_k ∘ Ψsymm = π_k` identity) rather than supply an `F` and re-prove the germ. The germ is
automatic: on `V`, `Φ = Ψ` and `Ψsymm (Ψ w) = w`, so `(f ∘ Ψsymm)(Φ w) = f w`. -/
theorem rlctAtOn_eq_of_contDiff_chart_inv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    (f : E → ℝ) (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar) :
    ∃ (Ψsymm : E → E) (V : Set E), IsOpen V ∧ wstar ∈ V ∧
      (∀ w ∈ V, Ψsymm (Φ w) = w) ∧
      rlctAtOn f wstar = rlctAtOn (fun w => f (Ψsymm w)) wstar := by
  obtain ⟨Ψ, Ψsymm, DΨ, DΨsymm, V, hVopen, hwV, hΨfix, hleft, hright, hΨcont, hsymmcont,
    hderiv, hderivsymm, hdetmeas, hdetmeassymm, hbdd, hbddsymm, hΨΦ, _, _⟩ :=
    exists_boundedUnit_chart_of_contDiffAt Φ wstar f' hΦ hΦ' hfix
  -- the inverse identity on `V`: `Ψsymm (Φ w) = Ψsymm (Ψ w) = w`.
  have hinv : ∀ w ∈ V, Ψsymm (Φ w) = w := by
    intro w hw; rw [← hΨΦ w hw]; exact hleft w hw
  refine ⟨Ψsymm, V, hVopen, hwV, hinv, ?_⟩
  -- the germ `f =ᶠ (f∘Ψsymm)∘Φ`: on `V`, `(f∘Ψsymm)(Φ w) = f w` by `hinv`.
  have hgerm : f =ᶠ[𝓝 wstar] fun w => (fun w => f (Ψsymm w)) (Φ w) := by
    filter_upwards [hVopen.mem_nhds hwV] with w hwV'
    show f w = f (Ψsymm (Φ w))
    rw [hinv w hwV']
  exact rlctAtOn_eq_of_contDiff_chart f (fun w => f (Ψsymm w)) Φ wstar f' hΦ hΦ' hfix hgerm

end DLNFibre.DLN.RLCT
