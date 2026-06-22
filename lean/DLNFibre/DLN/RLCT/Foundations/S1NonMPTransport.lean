import DLNFibre.DLN.RLCT.Skeleton

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport` — the non-measure-preserving RLCT transport (S1)

A genuine change of variables (a homeomorphism with a **bounded-unit** Jacobian, `det ≠ ±1`) transports
the RLCT — the NON-MP companion to `rlctAtOn_comp_homeomorph` (which needs measure preservation,
`det = 1`). For a homeomorphism `π` with `0 < a ≤ |det Dπ| ≤ b` near the basepoint,

    rlctAtOn (F ∘ π) (π⁻¹ wstar) = rlctAtOn F wstar.

Two ingredients: `weightedThreshold_transport` (S1.1) carries the `|det Dπ|` weight, and
`weightedThreshold_weight_unit_invariant` (here) strips a bounded-unit weight. Used by L2
(`DeepestGaugeChart`'s deepest-gauge slice, `deepest_nonMP_chart_transport_unit`) and shared with D1
(the homogeneous-residual chart). The bounded-unit Jacobian is the exact distinction from the MP/blow-up
work flagged in the g150 cert.
-/

open MeasureTheory Set
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {M : Type*} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]

/-- **Weight-slot unit invariance.** `weightedThreshold F φ {wstar} = weightedThreshold F 1 {wstar}`
when the weight `φ` is a bounded unit `0 < a ≤ |φ| ≤ b` near `wstar` (measurable). The weight-slot
companion of `rlctAtOn_unit_invariant_aux` (which strips a unit on the *function*): here the bounded
weight is absorbed by `Integrable.bdd_mul` both directions. -/
theorem weightedThreshold_weight_unit_invariant (F φ : M → ℝ) (wstar : M)
    (a b : ℝ) (ha : 0 < a) (hmeas : Measurable φ)
    (hφ : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |φ w| ∧ |φ w| ≤ b) :
    weightedThreshold F φ {wstar} = weightedThreshold F (fun _ => 1) {wstar} := by
  obtain ⟨U₀, hU₀, hbnd⟩ := hφ
  -- Forward: `(F, 1)` admissible at `c'` ⟹ `(F, φ)` admissible (bounded weight `|φ| ≤ b`).
  have fwd : ∀ c' : NNReal, (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) →
      (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * φ w) Ω volume) := by
    rintro c' ⟨Ω, hΩopen, hKΩ, hint⟩
    have hwΩ : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ :=
      mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hwΩ) hU₀)
    refine ⟨V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    have hVΩ : V ⊆ Ω := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |φ w| ∧ |φ w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    have hintF : IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) V volume :=
      ((hint.mono_set hVΩ).congr (by filter_upwards with w; rw [mul_one]))
    -- `φ` bounded ⟹ `Integrable (fun w => φ w * |F|^{−c'})`; commute to the goal shape.
    refine (Integrable.bdd_mul (c := b) hintF hmeas.aestronglyMeasurable ?_).congr ?_
    · filter_upwards [hbound] with w hw; rw [Real.norm_eq_abs]; exact hw.2
    · filter_upwards with w; show φ w * |F w| ^ (-(c' : ℝ)) = |F w| ^ (-(c' : ℝ)) * φ w; ring
  -- Backward: `(F, φ)` admissible at `c'` ⟹ `(F, 1)` admissible (weight `≥ a > 0`, divide).
  have bwd : ∀ c' : NNReal, (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * φ w) Ω volume) →
      (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) := by
    rintro c' ⟨Ω, hΩopen, hKΩ, hint⟩
    have hwΩ : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ :=
      mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hwΩ) hU₀)
    refine ⟨V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    have hVΩ : V ⊆ Ω := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |φ w| ∧ |φ w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    -- `|F|^{−c'}·1 = φ⁻¹ · (|F|^{−c'}·φ)`, and `|φ⁻¹| ≤ a⁻¹` (bounded) near `wstar`.
    refine (Integrable.bdd_mul (c := a⁻¹) (hint.mono_set hVΩ)
      ((hmeas.inv).aestronglyMeasurable) ?_).congr ?_
    · filter_upwards [hbound] with w hw
      rw [Real.norm_eq_abs, abs_inv]
      rw [inv_le_inv₀ (lt_of_lt_of_le ha hw.1) ha]; exact hw.1
    · filter_upwards [hbound] with w hw
      have hpos : (0:ℝ) < |φ w| := lt_of_lt_of_le ha hw.1
      have hne : φ w ≠ 0 := fun h => by simp [h] at hpos
      show (φ w)⁻¹ * (|F w| ^ (-(c' : ℝ)) * φ w) = |F w| ^ (-(c' : ℝ)) * 1
      rw [mul_one, mul_comm (|F w| ^ (-(c' : ℝ))) (φ w), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  unfold weightedThreshold
  congr 1
  ext c
  constructor
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, bwd c' hadm⟩
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, fwd c' hadm⟩

/-- **RLCT monotone under germ domination.** If `|G| ≤ |F|` and `G = 0 → F = 0` near `wstar`, then
`rlctAtOn G ≤ rlctAtOn F` (a more-singular `F` has a larger threshold). The `weightedThreshold`
admissible set for `F` includes that for `G` (`abs_rpow_neg_mono` on the integrand). Foundations-grade
S1 primitive — used by `rlctAtOn_squeeze` here and the D1≥ two-point domination. -/
theorem rlctAtOn_mono (F G : M → ℝ) (wstar : M) (hFmeas : Measurable F)
    (hdom : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, |G w| ≤ |F w| ∧ (G w = 0 → F w = 0)) :
    rlctAtOn G wstar ≤ rlctAtOn F wstar := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
  obtain ⟨V, hV, hVdom⟩ := hdom
  obtain ⟨W, hWV, hWopen, hwW⟩ := mem_nhds_iff.mp hV
  have hwΩ : wstar ∈ Ω := hKΩ rfl
  refine ⟨c', rfl, Ω ∩ W, hΩopen.inter hWopen, Set.singleton_subset_iff.2 ⟨hwΩ, hwW⟩, ?_⟩
  have hmeasF : AEStronglyMeasurable (fun w => |F w| ^ (-(c' : ℝ)) * (1 : ℝ))
      (volume.restrict (Ω ∩ W)) :=
    ((((continuous_abs.measurable).comp hFmeas).pow_const _).mul_const _).aestronglyMeasurable
  apply MeasureTheory.Integrable.mono (hint.mono_set Set.inter_subset_left) hmeasF
  have hΩW_meas : MeasurableSet (Ω ∩ W) := (hΩopen.inter hWopen).measurableSet
  refine (ae_restrict_iff' hΩW_meas).mpr ?_
  filter_upwards with w hw
  have hd := hVdom w (hWV hw.2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_one, mul_one, mul_one,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_rpow_neg_mono (F w) (G w) c' c'.2 hd.1 hd.2

/-- **The SQUEEZE RLCT-equality.** If `F, Φ ≥ 0` near `wstar`, both measurable, and `c₁·Φ ≤ F ≤ c₂·Φ`
with `0 < c₁, c₂`, then `rlctAtOn F wstar = rlctAtOn Φ wstar`. The positive constants `c₁, c₂` are units
stripped by `rlctAtOn_unit_invariant_aux`; the two inequalities give `rlctAtOn_mono` both ways (the
`F = 0 ⟺ Φ = 0` vanishing from the two-sided bound). NO change of variables, NO measure Jacobian — `F`
and `Φ` compared at the SAME point. The local non-MP transport tool for the deepest-gauge squeeze
(`DeepestGaugeChart`) and the per-node `schur_recursion_step_squeeze`. -/
theorem rlctAtOn_squeeze (F Φ : M → ℝ) (wstar : M) (hFmeas : Measurable F) (hΦmeas : Measurable Φ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsq : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, 0 ≤ Φ w ∧ c₁ * Φ w ≤ F w ∧ F w ≤ c₂ * Φ w) :
    rlctAtOn F wstar = rlctAtOn Φ wstar := by
  obtain ⟨U, hU, hbnd⟩ := hsq
  refine le_antisymm ?_ ?_
  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₂ * Φ w) wstar from
      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₂) wstar c₂ c₂ hc₂ (by fun_prop)
        ⟨U, hU, fun w _ => by rw [abs_of_pos hc₂]; exact ⟨le_refl _, le_refl _⟩⟩).symm]
    refine rlctAtOn_mono (fun w => c₂ * Φ w) F wstar (by fun_prop) ⟨U, hU, fun w hw => ?_⟩
    obtain ⟨hΦ, hlo, hhi⟩ := hbnd w hw
    have hF0 : 0 ≤ F w := le_trans (mul_nonneg hc₁.le hΦ) hlo
    refine ⟨?_, fun hFeq => ?_⟩
    · rw [abs_of_nonneg hF0, abs_of_nonneg (mul_nonneg hc₂.le hΦ)]; exact hhi
    · show c₂ * Φ w = 0
      have hΦ0 : Φ w = 0 := le_antisymm (by nlinarith [hFeq ▸ hlo]) hΦ
      rw [hΦ0, mul_zero]
  · rw [show rlctAtOn Φ wstar = rlctAtOn (fun w => c₁ * Φ w) wstar from
      (rlctAtOn_unit_invariant_aux Φ (fun _ => c₁) wstar c₁ c₁ hc₁ (by fun_prop)
        ⟨U, hU, fun w _ => by rw [abs_of_pos hc₁]; exact ⟨le_refl _, le_refl _⟩⟩).symm]
    refine rlctAtOn_mono F (fun w => c₁ * Φ w) wstar hFmeas ⟨U, hU, fun w hw => ?_⟩
    obtain ⟨hΦ, hlo, hhi⟩ := hbnd w hw
    have hF0 : 0 ≤ F w := le_trans (mul_nonneg hc₁.le hΦ) hlo
    refine ⟨?_, fun hcF0 => ?_⟩
    · rw [abs_of_nonneg (mul_nonneg hc₁.le hΦ), abs_of_nonneg hF0]; exact hlo
    · have hΦ0 : Φ w = 0 := by
        rcases mul_eq_zero.1 hcF0 with h | h
        · exact absurd h (ne_of_gt hc₁)
        · exact h
      nlinarith [hhi, hΦ0]

/-- **The bounded-unit-Jacobian homeomorphism RLCT peel** (the non-MP companion to
`rlctAtOn_comp_homeomorph`, generalising `rlctAtOn_ray_scaling_invariant` off the scaling map). For a
homeomorphism `π` FIXING the basepoint (`π wstar = wstar`), with derivative `Dπ` everywhere and a
**bounded-unit** Jacobian `0 < a ≤ |det Dπ| ≤ b` near `wstar`,

    rlctAtOn (F ∘ π) wstar = rlctAtOn F wstar.

The `det ≠ ±1` is exactly the distinction from the measure-preserving `rlctAtOn_comp_homeomorph`. Two
ingredients: `weightedThreshold_transport` (S1.1, `E = ∅`) deposits the `|det Dπ|` weight, then
`weightedThreshold_weight_unit_invariant` strips the bounded unit. The producer supplies the concrete
`π` + `Dπ` + the Jacobian bound (the "global homeomorphism + Jacobian" obligation); this lemma CONSUMES
them — so it discharges the gauge-absorption RLCT peels (`coreAbsorb_rlct`, `regAbsorb_rlct`) whose
maps fix the complementary slots and have a bounded-unit gauge Jacobian (`det(I−VY)⁻ᴹ⁰ ≈ 1`) at the
deepest point. -/
theorem rlctAtOn_boundedUnit_homeomorph {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F : M → ℝ) (wstar : M) (π : M ≃ₜ M) (Dπ : M → (M →L[ℝ] M))
    (hfix : π wstar = wstar)
    (hderiv : ∀ x, HasFDerivAt (fun w => π w) (Dπ x) x)
    (hdetmeas : Measurable fun w => |(Dπ w).det|)
    (hbdd : ∃ U ∈ 𝓝 wstar, ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ U, a ≤ |(Dπ w).det| ∧ |(Dπ w).det| ≤ b) :
    rlctAtOn (fun w => F (π w)) wstar = rlctAtOn F wstar := by
  -- the basepoint preimage is `{wstar}` (π injective + fixes wstar).
  have hpre : (fun w => π w) ⁻¹' {wstar} = {wstar} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact π.injective (h.trans hfix.symm)
    · intro h; rw [h]; exact hfix
  -- Step 1 (S1.1, `E = ∅`): `wThr F 1 {wstar} = wThr (F∘π) (1·|det Dπ|) {π⁻¹wstar}`.
  have htrans := weightedThreshold_transport F (fun _ => (1 : ℝ)) wstar (fun w => π w) Dπ ∅
    π.isProperMap MeasurableSet.empty (by simp) (Set.injOn_of_injective π.injective)
    (fun x _ => hderiv x) π.surjective (by simp)
  rw [hpre] at htrans
  -- the transported weight is `1 · |det Dπ|`; strip the bounded unit.
  have hwfun : (fun w => (fun _ => (1 : ℝ)) ((fun w => π w) w) * |(Dπ w).det|)
      = fun w => |(Dπ w).det| := by funext w; rw [one_mul]
  have hcompfun : (F ∘ fun w => π w) = fun w => F (π w) := rfl
  rw [hwfun, hcompfun] at htrans
  obtain ⟨U, hU, a, b, hapos, hbnd⟩ := hbdd
  have hpeel := weightedThreshold_weight_unit_invariant (fun w => F (π w))
    (fun w => |(Dπ w).det|) wstar a b hapos hdetmeas
    ⟨U, hU, fun w hw => by rw [abs_of_nonneg (abs_nonneg _)]; exact hbnd w hw⟩
  -- `rlctAtOn (F∘π) = wThr (F∘π) 1 = wThr (F∘π) |det| [hpeel.symm] = wThr F 1 [htrans.symm] = rlctAtOn F`.
  rw [rlctAtOn, rlctAtOn, ← hpeel, ← htrans]

end DLNFibre.DLN.RLCT
