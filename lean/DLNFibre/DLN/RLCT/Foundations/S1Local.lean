import DLNFibre.DLN.RLCT.Foundations.Rlct

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Local` — S1.3 (ideal invariance) + S1.4 (germ-locality)

The two local S1 corollaries, proven standalone (the `(B)` proof-module pattern; distinct `_aux`
names, verbatim Skeleton statements; the controller wires `Skeleton.<rung> := <rung>_aux …`). Both
are germ arguments on `rlctAt`'s `∃ U ∈ 𝓝 w*` admissibility.

**S1.3 FIDELITY FLAG (gap-class, like S1.1):** the *bare* `rlct_unit_invariant` statement (no
measurability on the unit `u`) is **FALSE** — for a non-measurable `u` bounded in `[a,b]`, `u·F` is
non-measurable, so `|u·F|^{−c'}` is never `Integrable` (Mathlib `Integrable ⟹
AEStronglyMeasurable`), hence `rlctAt (u·F) = sSup ∅ = 0`, while `rlctAt F` is generically positive.
The honest statement needs `Measurable u` (holds at every use-site: the unit is analytic). With
`Measurable u` added (controller-approved contract, 11th finding; rv-2 confirmed), S1.3 is
**PROVEN**: on a neighbourhood where `a ≤ |u| ≤ b` (`a > 0`),
`|u·F|^{−c'} = |u|^{−c'}·|F|^{−c'}` with the
unit-factor bounded between `b^{−c'}` and `a^{−c'}` (positive constants), so each integrand
dominates the other by a bounded measurable factor (`Integrable.bdd_mul`) — the admissibility
down-sets, hence the `sSup`s, coincide. S1.4 has no such gap (it transports an
already-integrable function's measurability) and is proven.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal Topology

variable {L : ℕ}

/-- **S1.3 (ideal invariance core).** The RLCT is invariant under multiplying `F` by a measurable
unit `u` bounded away from `0` in `[a,b]` (`a > 0`) on a neighbourhood of `w*`. (Wire-in target for
`Skeleton.rlct_unit_invariant`.) The `Measurable u` hypothesis is the 11th fidelity fix (see module
docstring; holds at every use-site, the unit being analytic). Proof: on a neighbourhood where
`a ≤ |u| ≤ b`, `|u·F|^{−c'} = |u|^{−c'}·|F|^{−c'}` with the unit-factor bounded by positive
constants both ways, so the admissibility down-sets coincide (`Integrable.bdd_mul`), hence so do
the `sSup`s. -/
theorem rlct_unit_invariant_aux (H : Fin (L + 1) → ℕ) (F u : Params H → ℝ) (wstar : Params H)
    (a b : ℝ) (ha : 0 < a) (hmeas : Measurable u)
    (hu : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b) :
    rlctAt H (fun w => u w * F w) wstar = rlctAt H F wstar := by
  haveI : OpensMeasurableSpace (Params H) :=
    inferInstanceAs (OpensMeasurableSpace
      (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))
  obtain ⟨U₀, hU₀, hbnd⟩ := hu
  -- Forward: `F` admissible at `c'` ⟹ `u·F` admissible (unit-factor `|u|^{−c'} ≤ a^{−c'}`).
  have fwd : ∀ c' : NNReal, (∃ U ∈ 𝓝 wstar,
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) U volume) →
      (∃ U ∈ 𝓝 wstar, IntegrableOn (fun w => |u w * F w| ^ (-(c' : ℝ))) U volume) := by
    rintro c' ⟨U, hU, hint⟩
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hU₀)
    refine ⟨V, hVopen.mem_nhds hwV, ?_⟩
    have hVU : V ⊆ U := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |u w| ∧ |u w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    have hrw : (fun w => |u w * F w| ^ (-(c' : ℝ)))
        = (fun w => |u w| ^ (-(c' : ℝ)) * |F w| ^ (-(c' : ℝ))) := by
      funext w; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    rw [hrw]
    refine Integrable.bdd_mul (c := a ^ (-(c' : ℝ))) (hint.mono_set hVU)
      ((by fun_prop : Measurable (fun w => |u w| ^ (-(c' : ℝ)))).aestronglyMeasurable) ?_
    filter_upwards [hbound] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow_of_nonpos ha hw.1 (by simp)
  -- Backward: `u·F` admissible ⟹ `F` admissible (factor `|u|^{c'} ≤ b^{c'}`, with `|u| > 0`).
  have bwd : ∀ c' : NNReal, (∃ U ∈ 𝓝 wstar,
        IntegrableOn (fun w => |u w * F w| ^ (-(c' : ℝ))) U volume) →
      (∃ U ∈ 𝓝 wstar, IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) U volume) := by
    rintro c' ⟨U, hU, hint⟩
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hU₀)
    refine ⟨V, hVopen.mem_nhds hwV, ?_⟩
    have hVU : V ⊆ U := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |u w| ∧ |u w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    refine (Integrable.bdd_mul (c := b ^ (c' : ℝ)) (hint.mono_set hVU)
      ((by fun_prop : Measurable (fun w => |u w| ^ (c' : ℝ))).aestronglyMeasurable) ?_).congr ?_
    · filter_upwards [hbound] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) hw.2 (by positivity)
    · filter_upwards [hbound] with w hw
      have hupos : (0:ℝ) < |u w| := lt_of_lt_of_le ha hw.1
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc,
        ← Real.rpow_add hupos]
      simp
  unfold rlctAt
  congr 1
  ext c
  constructor
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, bwd c' hadm⟩
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, fwd c' hadm⟩

/-- **S1.4 (germ-locality / φ-independence).** The RLCT depends only on the germ of `F` at `w*`: if
`F` and `G` agree on a neighbourhood of `w*`, their RLCTs are equal. (Wire-in target for
`Skeleton.rlct_germ_local`; verbatim statement, distinct name.) -/
theorem rlct_germ_local_aux (H : Fin (L + 1) → ℕ) (F G : Params H → ℝ) (wstar : Params H)
    (hFG : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, F w = G w) :
    rlctAt H F wstar = rlctAt H G wstar := by
  haveI : OpensMeasurableSpace (Params H) :=
    inferInstanceAs (OpensMeasurableSpace
      (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))
  obtain ⟨U₀, hU₀, hFGU₀⟩ := hFG
  have key : ∀ (P Q : Params H → ℝ), (∀ w ∈ U₀, P w = Q w) →
      ∀ c : ENNReal, (∃ c' : NNReal, c = c' ∧ ∃ U ∈ 𝓝 wstar,
          IntegrableOn (fun w => |P w| ^ (-(c' : ℝ))) U volume) →
        (∃ c' : NNReal, c = c' ∧ ∃ U ∈ 𝓝 wstar,
          IntegrableOn (fun w => |Q w| ^ (-(c' : ℝ))) U volume) := by
    rintro P Q hPQ c ⟨c', rfl, U, hU, hint⟩
    obtain ⟨V, hVsub, hVopen, hwV⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hU₀)
    refine ⟨c', rfl, V, hVopen.mem_nhds hwV, ?_⟩
    have hVU : V ⊆ U := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    apply (hint.mono_set hVU).congr
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with w hw
    rw [hPQ w (hVU₀ hw)]
  unfold rlctAt
  congr 1
  ext c
  exact ⟨key F G hFGU₀ c, key G F (fun w hw => (hFGU₀ w hw).symm) c⟩

/-! ## S1.3 on a general domain — `rlctAtOn` unit-invariance

The `rlctAt`/`Params H` unit-invariance above does not reach the general-M resolution tree: a
chart-local reduction lives on `rlctAtOn` over a PRODUCT domain `(Fin n → ℝ) × Params M'`, not on
`Params H`. The version below is `rlct_unit_invariant_aux` restated at the `weightedThreshold` /
`rlctAtOn` level over a general `[MeasureSpace] [TopologicalSpace] [OpensMeasurableSpace]` source —
the proof is the same germ argument (`Integrable.bdd_mul` both ways, the admissibility down-sets
coincide), with the `Params H` skin replaced by the typeclass hypotheses. Reusable bedrock: every
node's `g' := wᵢ · (g ∘ φᵢ)` recursion in the general-M tree strips a unit through this. (Same `_aux`
proof-module pattern; the general statement carries no separate Skeleton wire — it is the engine the
general-M rungs consume directly.) -/

/-- **S1.3 (general domain).** The RLCT threshold `rlctAtOn` is invariant under multiplying the
integrand by a measurable unit `u` bounded in `[a,b]` (`a > 0`) on a neighbourhood of `w*`:
`rlctAtOn (u·F) w* = rlctAtOn F w*`. The general-domain twin of `rlct_unit_invariant_aux` (drops the
`Params H` skin for typeclass hypotheses). On `Params` it agrees with the latter via
`rlctAtOn_eq_rlctAt`. -/
theorem rlctAtOn_unit_invariant_aux {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    [OpensMeasurableSpace M] (F u : M → ℝ) (wstar : M)
    (a b : ℝ) (ha : 0 < a) (hmeas : Measurable u)
    (hu : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b) :
    rlctAtOn (fun w => u w * F w) wstar = rlctAtOn F wstar := by
  obtain ⟨U₀, hU₀, hbnd⟩ := hu
  -- Forward: `F` admissible at `c'` ⟹ `u·F` admissible (unit-factor `|u|^{−c'} ≤ a^{−c'}`).
  have fwd : ∀ c' : NNReal, (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) →
      (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |u w * F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) := by
    rintro c' ⟨Ω, hΩopen, hKΩ, hint⟩
    have hwΩ : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ :=
      mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hwΩ) hU₀)
    refine ⟨V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    have hVΩ : V ⊆ Ω := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |u w| ∧ |u w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    have hrw : (fun w => |u w * F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w)
        = (fun w => |u w| ^ (-(c' : ℝ)) * (|F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w)) := by
      funext w; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]; ring
    rw [hrw]
    refine Integrable.bdd_mul (c := a ^ (-(c' : ℝ))) (hint.mono_set hVΩ)
      ((by fun_prop : Measurable (fun w => |u w| ^ (-(c' : ℝ)))).aestronglyMeasurable) ?_
    filter_upwards [hbound] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow_of_nonpos ha hw.1 (by simp)
  -- Backward: `u·F` admissible ⟹ `F` admissible (factor `|u|^{c'} ≤ b^{c'}`).
  have bwd : ∀ c' : NNReal, (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |u w * F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) →
      (∃ Ω : Set M, IsOpen Ω ∧ {wstar} ⊆ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1:ℝ)) w) Ω volume) := by
    rintro c' ⟨Ω, hΩopen, hKΩ, hint⟩
    have hwΩ : wstar ∈ Ω := hKΩ rfl
    obtain ⟨V, hVsub, hVopen, hwV⟩ :=
      mem_nhds_iff.1 (Filter.inter_mem (hΩopen.mem_nhds hwΩ) hU₀)
    refine ⟨V, hVopen, Set.singleton_subset_iff.2 hwV, ?_⟩
    have hVΩ : V ⊆ Ω := fun x hx => (hVsub hx).1
    have hVU₀ : V ⊆ U₀ := fun x hx => (hVsub hx).2
    have hbound : ∀ᵐ w ∂(volume.restrict V), a ≤ |u w| ∧ |u w| ≤ b :=
      (ae_restrict_mem hVopen.measurableSet).mono fun w hw => hbnd w (hVU₀ hw)
    refine (Integrable.bdd_mul (c := b ^ (c' : ℝ)) (hint.mono_set hVΩ)
      ((by fun_prop : Measurable (fun w => |u w| ^ (c' : ℝ))).aestronglyMeasurable) ?_).congr ?_
    · filter_upwards [hbound] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) hw.2 (by positivity)
    · filter_upwards [hbound] with w hw
      have hupos : (0:ℝ) < |u w| := lt_of_lt_of_le ha hw.1
      show |u w| ^ (c' : ℝ) * (|u w * F w| ^ (-(c' : ℝ)) * 1) = |F w| ^ (-(c' : ℝ)) * 1
      rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_one, mul_one, ← mul_assoc,
        ← Real.rpow_add hupos]
      simp
  unfold rlctAtOn weightedThreshold
  congr 1
  ext c
  constructor
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, bwd c' hadm⟩
  · rintro ⟨c', rfl, hadm⟩; exact ⟨c', rfl, fwd c' hadm⟩

end DLNFibre.DLN.RLCT
