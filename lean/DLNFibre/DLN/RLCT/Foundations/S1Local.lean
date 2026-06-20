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
The honest statement needs `Measurable u` (holds at every use-site: the unit is analytic). S1.3 is
carried as a
named `sorry` pending the controller's contract decision; S1.4 has no such gap (it transports an
already-integrable function's measurability) and is proven.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal Topology

variable {L : ℕ}

/-- **S1.3 (ideal invariance core).** The RLCT is invariant under multiplying `F` by a unit `u`
bounded away from `0` in `[a,b]` (`a > 0`) on a neighbourhood of `w*`. (Wire-in target for
`Skeleton.rlct_unit_invariant`.) FIDELITY FLAG: the bare statement is false without `Measurable u`
(see module docstring); carried as `sorry` pending the contract decision. -/
theorem rlct_unit_invariant_aux (H : Fin (L + 1) → ℕ) (F u : Params H → ℝ) (wstar : Params H)
    (a b : ℝ) (ha : 0 < a)
    (hu : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, a ≤ |u w| ∧ |u w| ≤ b) :
    rlctAt H (fun w => u w * F w) wstar = rlctAt H F wstar := by
  sorry

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

end DLNFibre.DLN.RLCT
