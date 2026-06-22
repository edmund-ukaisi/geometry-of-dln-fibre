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

end DLNFibre.DLN.RLCT
