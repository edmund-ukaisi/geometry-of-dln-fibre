import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Transport` — S1.1 weighted-threshold transport

The S1.1 linchpin: the weighted RLCT threshold `θ(F, φ; {w*})` transports under a proper
a.e.-analytic map `π`, with the Jacobian `|det Dπ|` entering as a weight. Proven standalone here
(Foundations), to be wired into the goal skeleton. Feeds D1/L2, R1.

## Fidelity finding (the heaviest analytic rung, fm-2)
The bare-hypothesis equality of `weightedThreshold_transport` (`Skeleton.lean`) is **only the `≤`
direction** (`weightedThreshold_le_transport`, proven sorry-free here): the change-of-variables on
`Eᶜ` plus monotonicity gives `θ(F, φ; {w*}) ≤ θ(F∘π, (φ∘π)·|det Dπ|; π⁻¹{w*})` unconditionally.

The reverse `≥` is **false** under the bare hypotheses; two extra hypotheses are needed and are
**sufficient** (full equality: `weightedThreshold_transport_aux`, sorry-free):
* `Function.Surjective π` — else, with `w* ∉ range π`, the fibre `π⁻¹{w*}` is empty, the RHS
  open-cover constraint is vacuous, and the RHS threshold jumps to `⊤` while the LHS is finite.
* `volume (π '' E) = 0` (Luzin-N for the null set `E`) — else a singular monotone `π` (e.g.
  `id + Cantor staircase`) sends the null `E` to a positive-measure set `π(E)`, where a singularity
  of `F` adds mass to the LHS integral that the RHS (computed off `E`) never sees, breaking `≥`.

`volume (π '' E) = 0` follows from Mathlib's Luzin-N
(`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`) once `π` is differentiable **on**
`E` too, which `hderiv : ∀ m ∈ Eᶜ, …` does not provide. The `Skeleton.lean` docstring assumed
"`π(E)` null available" but the hypotheses do not encode it. Recommendation to the controller:
either add `hsurj`/`hImE` to the `Skeleton.lean` statement, or strengthen `hderiv` to all of `M`
(then `hsurj` still needs invariance-of-domain, absent from Mathlib v4.29).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set

/-- The admissible exponent set behind `weightedThreshold G ρ K`: the `c : ℝ≥0∞` realised by some
`c' : ℝ≥0` with `|G|^{−c'}·ρ` integrable on an open `Ω ⊇ K`. `weightedThreshold` is its `sSup`. -/
private def admissible {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    (G ρ : M → ℝ) (K : Set M) : Set ENNReal :=
  { c : ENNReal | ∃ c' : NNReal, c = (c' : ENNReal) ∧
      ∃ Ω : Set M, IsOpen Ω ∧ K ⊆ Ω ∧
        IntegrableOn (fun w ↦ |G w| ^ (-(c' : ℝ)) * ρ w) Ω volume }

/-- `weightedThreshold G ρ K` is the `sSup` of its admissible exponent set (definitional unfold). -/
private theorem weightedThreshold_eq_sSup_admissible {M : Type*} [MeasureSpace M]
    [TopologicalSpace M] (G ρ : M → ℝ) (K : Set M) :
    weightedThreshold G ρ K = sSup (admissible G ρ K) := rfl

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
  [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]

/-- The forward admissible-set inclusion (LHS ⊆ RHS): every exponent admissible for `θ(F, φ; {w*})`
is admissible for `θ(F∘π, (φ∘π)·|det Dπ|; π⁻¹{w*})`. Change of variables on `Eᶜ` plus the
null-set restoration; needs only properness, injectivity and differentiability off the null `E`. -/
private theorem admissible_subset_transport
    (F φ : M → ℝ) (wstar : M) (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π) (hE_meas : MeasurableSet E) (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ) (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m) :
    admissible F φ {wstar}
      ⊆ admissible (F ∘ π) (fun m ↦ φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by
  rintro c ⟨c', rfl, Ω, hΩopen, hwΩ, hint⟩
  refine ⟨c', rfl, π ⁻¹' Ω, hΩopen.preimage hproper.continuous, ?_, ?_⟩
  · intro x hx; simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [mem_preimage, hx]; exact hwΩ rfl
  · -- Work on `s := π⁻¹Ω \ E`: there `π` is injective and differentiable.
    set s : Set M := π ⁻¹' Ω \ E with hs
    have hΩ'_meas : MeasurableSet (π ⁻¹' Ω) := (hΩopen.preimage hproper.continuous).measurableSet
    have hs_meas : MeasurableSet s := hΩ'_meas.diff hE_meas
    have hs_sub : s ⊆ Eᶜ := fun x hx ↦ hx.2
    have hderiv_s : ∀ x ∈ s, HasFDerivWithinAt π (Dπ x) s x :=
      fun x hx ↦ (hderiv x (hs_sub hx)).hasFDerivWithinAt
    have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hs_meas hderiv_s (hinj.mono hs_sub) (fun w ↦ |F w| ^ (-(c' : ℝ)) * φ w)
    have himg_sub : π '' s ⊆ Ω := by rintro y ⟨x, hx, rfl⟩; exact hx.1
    have hg_img := hint.mono_set himg_sub
    have hint_eq : (fun x ↦ |(Dπ x).det| • (|F (π x)| ^ (-(c' : ℝ)) * φ (π x)))
        = fun m ↦ |F (π m)| ^ (-(c' : ℝ)) * (φ (π m) * |(Dπ m).det|) := by
      funext x; simp only [smul_eq_mul]; ring
    have hh_s : IntegrableOn
        (fun m ↦ |F (π m)| ^ (-(c' : ℝ)) * (φ (π m) * |(Dπ m).det|)) s volume := by
      rw [← hint_eq]; exact hcov.1 hg_img
    exact (integrableOn_congr_set_ae (diff_null_ae_eq_self hE_null)).1 hh_s

/-- **S1.1, the unconditional half (`≤`).** Under properness, injectivity and differentiability off
a null measurable set `E`, the weighted threshold satisfies `θ(F, φ; {w*}) ≤ θ(F∘π, (φ∘π)·|det Dπ|;
π⁻¹{w*})`. This direction needs no surjectivity or Luzin-N (see the file header). -/
theorem weightedThreshold_le_transport
    (F φ : M → ℝ) (wstar : M) (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π) (hE_meas : MeasurableSet E) (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ) (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m) :
    weightedThreshold F φ {wstar}
      ≤ weightedThreshold (F ∘ π) (fun m ↦ φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by
  rw [weightedThreshold_eq_sSup_admissible, weightedThreshold_eq_sSup_admissible]
  exact sSup_le_sSup
    (admissible_subset_transport F φ wstar π Dπ E hproper hE_meas hE_null hinj hderiv)

/-- **S1.1 (weighted-threshold transport, full equality).** The **wire-in target** for Skeleton's
`weightedThreshold_transport` (distinct `_aux` name to avoid the shared-FQN collision; conclusion
verbatim, so the wire-in is `exact`). With the two extra hypotheses the bare statement lacks — `π`
surjective and `volume (π '' E) = 0` (Luzin-N) — the weighted threshold
transports with the Jacobian weight: `θ(F, φ; {w*}) = θ(F∘π, (φ∘π)·|det Dπ|; π⁻¹{w*})`. Forward via
`admissible_subset_transport`; reverse via the proper-map tube `Ω = (π '' Ω'ᶜ)ᶜ` and CoV on
`π⁻¹Ω \ E`, with `Ω =ᵐ π '' (π⁻¹Ω \ E)` (the difference lies in the null `π '' E`). -/
theorem weightedThreshold_transport_aux
    (F φ : M → ℝ) (wstar : M) (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π) (hE_meas : MeasurableSet E) (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ) (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m)
    (hsurj : Function.Surjective π) (hImE : volume (π '' E) = 0) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m ↦ φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by
  rw [weightedThreshold_eq_sSup_admissible, weightedThreshold_eq_sSup_admissible]
  refine le_antisymm
    (sSup_le_sSup
      (admissible_subset_transport F φ wstar π Dπ E hproper hE_meas hE_null hinj hderiv))
    (sSup_le_sSup ?_)
  -- REVERSE: every RHS-admissible exponent is LHS-admissible.
  rintro c ⟨c', rfl, Ω', hΩ'open, hwΩ', hint'⟩
  -- The proper-map tube `Ω := (π '' Ω'ᶜ)ᶜ` is open and contains `w*`, with `π⁻¹Ω ⊆ Ω'`.
  set Ω : Set M := (π '' Ω'ᶜ)ᶜ with hΩdef
  have hΩopen : IsOpen Ω := (hproper.isClosedMap _ hΩ'open.isClosed_compl).isOpen_compl
  refine ⟨c', rfl, Ω, hΩopen, ?_, ?_⟩
  · -- `w* ∈ Ω`: any preimage of `w*` lies in `Ω'` (since `π⁻¹{w*} ⊆ Ω'`).
    intro x hx; simp only [mem_singleton_iff] at hx; subst hx
    simp only [hΩdef, mem_compl_iff, mem_image, not_exists, not_and]
    rintro y hy rfl; exact hy (hwΩ' rfl)
  · -- Pull back to `s := π⁻¹Ω \ E ⊆ Ω'`, change variables, restore the null `π '' E`.
    set s : Set M := π ⁻¹' Ω \ E with hs
    have hΩ_meas : MeasurableSet (π ⁻¹' Ω) := (hΩopen.preimage hproper.continuous).measurableSet
    have hs_meas : MeasurableSet s := hΩ_meas.diff hE_meas
    have hs_sub : s ⊆ Eᶜ := fun x hx ↦ hx.2
    -- `x ∈ Ω'ᶜ ⟹ π x ∈ π '' Ω'ᶜ ⟹ π x ∉ Ω`.
    have hpre_sub : π ⁻¹' Ω ⊆ Ω' := by
      intro x hx; by_contra hxΩ'
      exact (hx (mem_image_of_mem π hxΩ'))
    have hs_sub_Ω' : s ⊆ Ω' := fun x hx ↦ hpre_sub hx.1
    have hderiv_s : ∀ x ∈ s, HasFDerivWithinAt π (Dπ x) s x :=
      fun x hx ↦ (hderiv x (hs_sub hx)).hasFDerivWithinAt
    have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hs_meas hderiv_s (hinj.mono hs_sub) (fun w ↦ |F w| ^ (-(c' : ℝ)) * φ w)
    -- `h` is integrable on `s ⊆ Ω'`.
    have hint_eq : (fun x ↦ |(Dπ x).det| • (|F (π x)| ^ (-(c' : ℝ)) * φ (π x)))
        = fun m ↦ |F (π m)| ^ (-(c' : ℝ)) * (φ (π m) * |(Dπ m).det|) := by
      funext x; simp only [smul_eq_mul]; ring
    have hh_s : IntegrableOn
        (fun x ↦ |(Dπ x).det| • (|F (π x)| ^ (-(c' : ℝ)) * φ (π x))) s volume := by
      rw [hint_eq]; exact hint'.mono_set hs_sub_Ω'
    have hg_img : IntegrableOn (fun w ↦ |F w| ^ (-(c' : ℝ)) * φ w) (π '' s) volume := hcov.2 hh_s
    -- `Ω =ᵐ π '' s`: the difference lies in the null `π '' E`.
    have himg_sub : π '' s ⊆ Ω := by rintro y ⟨x, hx, rfl⟩; exact hx.1
    have hdiff_sub : Ω \ π '' s ⊆ π '' E := by
      rintro y ⟨hyΩ, hyns⟩
      obtain ⟨x, rfl⟩ := hsurj y
      have hxΩ : x ∈ π ⁻¹' Ω := hyΩ
      by_cases hxE : x ∈ E
      · exact mem_image_of_mem π hxE
      · have hxs : x ∈ s := ⟨hxΩ, hxE⟩
        exact absurd (mem_image_of_mem π hxs) hyns
    have hae : Ω =ᵐ[volume] π '' s := by
      refine (ae_eq_set).2 ⟨measure_mono_null hdiff_sub hImE, ?_⟩
      simp [diff_eq_empty.2 himg_sub]
    exact (integrableOn_congr_set_ae hae).2 hg_img

end DLNFibre.DLN.RLCT
