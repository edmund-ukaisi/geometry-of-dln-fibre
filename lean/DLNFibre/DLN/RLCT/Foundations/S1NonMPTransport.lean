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
deepest point. **GLOBAL `π : M ≃ₜ M` form** — for a producer whose diffeo is defined only on a
neighbourhood (e.g. an IFT `OpenPartialHomeomorph`), use `rlctAtOn_boundedUnit_localHomeomorph`
below (bare `π/πsymm`, inverses + derivs + det-bound on an open `V ∋ wstar`, no global `≃ₜ`/cutoff). -/
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

/-- **The local `≤` transport** (the forward admissible-set inclusion, restricted to `V`). For `π`
continuous + injective (via the partial inverse `πsymm`) + differentiable on the open `V ∋ wstar` with
`π wstar = wstar`: `θ(F, 1; {wstar}) ≤ θ(F∘π, |det Dπ|; {wstar})`. The local adaptation of
`admissible_subset_transport` (which needs only `hproper.continuous`, NOT full properness): the witness
`Ω` restricts to `Ω ∩ V`, the change of variables runs on `s = πsymm '' (Ω ∩ V) = V ∩ π⁻¹'(Ω ∩ V)` (open,
`π '' s = Ω ∩ V ⊆ Ω`, `π` inj+diff on `s ⊆ V`). Applied to `π` (forward) and to `πsymm` (reverse) it
gives the two-sided transport. Needs ONLY the left-inverse `hleft` (for injectivity on `s`) — NOT
`π '' V ⊆ V` (the working set `s` lands `π` in `Ω`, never asking `π` to preserve `V`), so a diffeo
`π : V → V'` with `V ≠ V'` feeds it directly (g162: bi-invariance is infeasible from the IFT). -/
private theorem weightedThreshold_le_transport_local {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F : M → ℝ) (wstar : M) (π πsymm : M → M) (Dπ : M → (M →L[ℝ] M)) (V : Set M)
    (hVopen : IsOpen V) (hwV : wstar ∈ V) (hfix : π wstar = wstar)
    (hleft : ∀ w ∈ V, πsymm (π w) = w)
    (hπcont : ContinuousOn π V)
    (hderiv : ∀ w ∈ V, HasFDerivAt (fun w => π w) (Dπ w) w) :
    weightedThreshold F (fun _ => (1 : ℝ)) {wstar}
      ≤ weightedThreshold (fun w => F (π w)) (fun w => |(Dπ w).det|) {wstar} := by
  unfold weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
  have hwΩ : wstar ∈ Ω := hKΩ rfl
  set s : Set M := V ∩ π ⁻¹' (Ω ∩ V) with hs
  have hsopen : IsOpen s := hπcont.isOpen_inter_preimage hVopen (hΩopen.inter hVopen)
  refine ⟨c', rfl, s, hsopen, ?_, ?_⟩
  · refine Set.singleton_subset_iff.2 ⟨hwV, ?_⟩
    show π wstar ∈ Ω ∩ V
    rw [hfix]; exact ⟨hwΩ, hwV⟩
  · have hs_sub_V : s ⊆ V := fun x hx => hx.1
    have hs_meas : MeasurableSet s := hsopen.measurableSet
    have hderiv_s : ∀ x ∈ s, HasFDerivWithinAt (fun w => π w) (Dπ x) s x :=
      fun x hx => (hderiv x (hs_sub_V hx)).hasFDerivWithinAt
    have hinj_s : Set.InjOn π s := by
      intro a ha b hb hab
      have := congrArg πsymm hab
      rwa [hleft a (hs_sub_V ha), hleft b (hs_sub_V hb)] at this
    have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hs_meas hderiv_s hinj_s (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w)
    have himg : π '' s ⊆ Ω := by rintro y ⟨x, hx, rfl⟩; exact hx.2.1
    have hg_img : IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) (π '' s) volume :=
      hint.mono_set himg
    have hh_s := hcov.1 hg_img
    refine hh_s.congr ?_
    filter_upwards with x
    simp only [smul_eq_mul, mul_one]; ring

/-- **Germ-locality of the trivial-weight `weightedThreshold`.** If `f =ᶠ[𝓝 wstar] g` then
`weightedThreshold f 1 {wstar} = weightedThreshold g 1 {wstar}` — the admissible sets agree (any open
`Ω ∋ wstar` shrinks to `Ω ∩ U` where `f = g`). The `weightedThreshold`-level twin of
`rlctAtOn_germ_local` (which lives downstream); inlined here to avoid the import cycle. -/
private theorem weightedThreshold_congr_germ_one {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    [OpensMeasurableSpace M] (f g : M → ℝ) (wstar : M) (hfg : f =ᶠ[𝓝 wstar] g) :
    weightedThreshold f (fun _ => (1 : ℝ)) {wstar} = weightedThreshold g (fun _ => (1 : ℝ)) {wstar} := by
  obtain ⟨U₀, hU₀mem, hU₀⟩ := Filter.eventually_iff_exists_mem.1 hfg
  unfold weightedThreshold
  have key : ∀ (P Q : M → ℝ), (∀ w ∈ U₀, P w = Q w) → ∀ c : ENNReal,
      (∃ c' : NNReal, c = (c':ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |P w| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) →
      (∃ c' : NNReal, c = (c':ENNReal) ∧ ∃ Ω, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |Q w| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) := by
    rintro P Q hPQ c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
    have hw0 : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hw0) hU₀mem)
    refine ⟨c', rfl, V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    apply (hint.mono_set (fun x hx => (hVsub hx).1)).congr
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with w hw
    rw [hPQ w (hVsub hw).2]
  congr 1; ext c
  exact ⟨key f g hU₀ c, key g f (fun w hw => (hU₀ w hw).symm) c⟩

/-- **The LOCAL bounded-unit-Jacobian RLCT peel** (the germ-level companion of
`rlctAtOn_boundedUnit_homeomorph`, for a diffeomorphism defined only NEAR the basepoint). `rlctAtOn` is
a germ at `wstar` (the admissible `c'` quantify over open `Ω ∋ wstar`), so a change of variables valid
only on a neighbourhood `V ∋ wstar` suffices — no GLOBAL proper/surjective hypotheses. For a `π` that is
a diffeomorphism on `V` (with inverse `πsymm`, both differentiable, bounded-unit Jacobians), fixing
`wstar`,

    rlctAtOn (F ∘ π) wstar = rlctAtOn F wstar.

This is the right altitude for the gauge absorptions: the implicit-function-theorem gives them as
`OpenPartialHomeomorph`s (local diffeos, source a `𝓝 wstar`, BOTH `π` and `πsymm` differentiable), with
`dE(wstar) = id` ⟹ `|det Dπ(wstar)| = 1` ⟹ bounded-unit by continuity. The producer (cobuild-sub34)
supplies the local data for both directions; this lemma CONSUMES it to discharge `coreAbsorb_rlct`/
`regAbsorb_rlct`. (Raw-data form, decoupled from the `OpenPartialHomeomorph` API.)

**No bi-invariance (g162 fix).** The IFT diffeo maps `π : V → V'` with `V ≠ V'` (a diffeo pushes
points out of its source), and no finite intersection of `source/target` preimages is both invariant
AND open (the missing forward-preimage clause recurs at every iterate). So `π '' V ⊆ V` is INFEASIBLE
and is NOT required: each direction's change of variables runs on its own working set
`s = V ∩ π⁻¹'(Ω ∩ V)`, which lands `π` in `Ω` without ever asking `π` to preserve `V`. The minimal
data is just the two inverse identities + both maps `C¹` on the SAME `V` — take
`V = h.source ∩ h.target` (open, `∋ wstar`, `⊆ source ∩ target` so both `π`, `πsymm` are `C¹` there). -/
theorem rlctAtOn_boundedUnit_localHomeomorph {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F : M → ℝ) (wstar : M) (π : M → M) (πsymm : M → M)
    (Dπ : M → (M →L[ℝ] M)) (Dπsymm : M → (M →L[ℝ] M)) (V : Set M)
    (hVopen : IsOpen V) (hwV : wstar ∈ V)
    (hfix : π wstar = wstar)
    (hleft : ∀ w ∈ V, πsymm (π w) = w) (hright : ∀ w ∈ V, π (πsymm w) = w)
    (hπcont : ContinuousOn π V) (hsymmcont : ContinuousOn πsymm V)
    (hderiv : ∀ w ∈ V, HasFDerivAt (fun w => π w) (Dπ w) w)
    (hderivsymm : ∀ w ∈ V, HasFDerivAt (fun w => πsymm w) (Dπsymm w) w)
    (hdetmeas : Measurable fun w => |(Dπ w).det|)
    (hdetmeassymm : Measurable fun w => |(Dπsymm w).det|)
    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(Dπ w).det| ∧ |(Dπ w).det| ≤ b)
    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(Dπsymm w).det| ∧ |(Dπsymm w).det| ≤ b) :
    rlctAtOn (fun w => F (π w)) wstar = rlctAtOn F wstar := by
  have hfixsymm : πsymm wstar = wstar := by
    conv_lhs => rw [← hfix]
    exact hleft wstar hwV
  -- strip the bounded-unit weight `|det Dπ|` (fwd) / `|det Dπsymm|` (rev) — both via the V-bound.
  have hVnhds : V ∈ 𝓝 wstar := hVopen.mem_nhds hwV
  have hstrip : weightedThreshold (fun w => F (π w)) (fun w => |(Dπ w).det|) {wstar}
      = weightedThreshold (fun w => F (π w)) (fun _ => 1) {wstar} := by
    obtain ⟨a, b, hapos, hbnd⟩ := hbdd
    exact weightedThreshold_weight_unit_invariant (fun w => F (π w)) (fun w => |(Dπ w).det|)
      wstar a b hapos hdetmeas ⟨V, hVnhds, fun w hw => by
        rw [abs_of_nonneg (abs_nonneg _)]; exact hbnd w hw⟩
  have hstripsymm : weightedThreshold (fun w => F (π (πsymm w))) (fun w => |(Dπsymm w).det|) {wstar}
      = weightedThreshold (fun w => F (π (πsymm w))) (fun _ => 1) {wstar} := by
    obtain ⟨a, b, hapos, hbnd⟩ := hbddsymm
    exact weightedThreshold_weight_unit_invariant (fun w => F (π (πsymm w)))
      (fun w => |(Dπsymm w).det|) wstar a b hapos hdetmeassymm ⟨V, hVnhds, fun w hw => by
        rw [abs_of_nonneg (abs_nonneg _)]; exact hbnd w hw⟩
  -- `(F∘π)∘πsymm = F` on `V` (a nbhd of wstar, via `hright`): the two weightedThresholds agree.
  have hcomp : weightedThreshold (fun w => F (π (πsymm w))) (fun _ => 1) {wstar}
      = weightedThreshold F (fun _ => 1) {wstar} :=
    weightedThreshold_congr_germ_one (fun w => F (π (πsymm w))) F wstar
      (Filter.eventuallyEq_of_mem hVnhds (fun w hw => by rw [hright w hw]))
  -- FORWARD: `rlctAtOn F = wThr F 1 ≤ wThr (F∘π) |det Dπ| = wThr (F∘π) 1 = rlctAtOn (F∘π)`.
  -- `hleft` is the left-inverse on `V` (for injectivity on the working set); no `π '' V ⊆ V`.
  have hfwd := weightedThreshold_le_transport_local F wstar π πsymm Dπ V hVopen hwV hfix
    hleft hπcont hderiv
  -- REVERSE (via `πsymm`): `wThr (F∘π) 1 ≤ wThr ((F∘π)∘πsymm) |det Dπsymm| = wThr F 1`.
  -- here the roles swap: `πsymm`'s left-inverse on `V` is `hright` (`π (πsymm w) = w`).
  have hrev := weightedThreshold_le_transport_local (fun w => F (π w)) wstar πsymm π Dπsymm V
    hVopen hwV hfixsymm hright hsymmcont hderivsymm
  rw [hstrip] at hfwd
  rw [hstripsymm, hcomp] at hrev
  -- assemble: `rlctAtOn (F∘π) = wThr (F∘π) 1`, `rlctAtOn F = wThr F 1`; le_antisymm of hrev/hfwd.
  rw [rlctAtOn, rlctAtOn]
  exact le_antisymm hrev hfwd

end DLNFibre.DLN.RLCT
