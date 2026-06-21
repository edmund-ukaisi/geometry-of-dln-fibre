import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Foundations.S1G5

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Cover` — the cover → `rlctAtOn` connection

The R1 resolution covers a threshold integral by a finite chart family
(`g5_pivotNode`): `∫⁻_U |F|^{−c} = Σ_leaves ∫⁻_leaf |det φ|·|F∘φ|^{−c}`. This file turns that
integral identity into the RLCT VALUE, via two reusable bridges:

- **`cover_integral_lt_top_iff`** — the `ℝ≥0∞` sum-finiteness atom: the `U`-integral is finite iff
  every leaf integral is finite (`ENNReal.sum_lt_top`).
- **`rlctAtOn_ge_of_integral_lt`** (the `≥` half) — if the threshold integral over a fixed open
  `U ∋ 0` is finite for every `c' < t`, then `rlctAtOn F 0 ≥ t` (each such `c'` is admissible with
  witness `U`).
- **`rlctAtOn_le_of_adm_le`** (the `≤` reduction) — `rlctAtOn F 0 ≤ t` reduces to: every admissible
  `c'` (integrable on some open `Ω ∋ 0`) satisfies `c' ≤ t`.

The consumer (the `(2,2,2)` cover) discharges these from the concrete cover + the per-leaf
`monomialThreshold` values: `≥` from "all leaves converge below `⨅`", `≤` from "one leaf diverges
above `⨅`". The `≤`-direction's neighbourhood quantifier (admissibility on *any* `Ω`, not just `U`)
is handled at the use-site by the leaf divergence localising at the origin.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **Cover sum-finiteness.** For a `g5`-style cover `∫⁻_U g = Σᵢ ∫⁻_{leaf i} wᵢ`, the integral over
`U` is finite iff every leaf integral is finite (`ENNReal.sum_lt_top`). The core of "threshold
finite ⟺ all leaves below threshold". -/
theorem cover_integral_lt_top_iff {E : Type*} [MeasurableSpace E] {ι : Type*} (s : Finset ι)
    (μ : Measure E) (U : Set E) (leafSet : ι → Set E) (g : E → ℝ≥0∞) (w : ι → E → ℝ≥0∞)
    (hcov : ∫⁻ x in U, g x ∂μ = ∑ i ∈ s, ∫⁻ x in leafSet i, w i x ∂μ) :
    (∫⁻ x in U, g x ∂μ < ⊤) ↔ ∀ i ∈ s, ∫⁻ x in leafSet i, w i x ∂μ < ⊤ := by
  rw [hcov]; exact ENNReal.sum_lt_top

/-- **The `≥` half.** If the threshold integral over a fixed open `U ∋ 0` is finite for every
`c' < t`, then `t ≤ rlctAtOn F 0`. Each such `c'` is admissible (integrable on `U` via
`hasFiniteIntegral_iff_ofReal`), witness `Ω = U`; `sSup` over `c' < t` gives `≥ t`. -/
theorem rlctAtOn_ge_of_integral_lt {E : Type*} [MeasureSpace E] [TopologicalSpace E] [Zero E]
    (F : E → ℝ) (hFm : Measurable F) (U : Set E) (hU : IsOpen U) (h0 : (0 : E) ∈ U) (t : ℝ≥0∞)
    (hfin : ∀ c' : NNReal, (c' : ℝ≥0∞) < t →
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) < ⊤) :
    t ≤ rlctAtOn F 0 := by
  apply le_of_forall_lt_imp_le_of_dense
  intro q hq
  have hqfin : q ≠ ⊤ := hq.ne_top
  set c' := q.toNNReal with hc'
  have hc'e : (c' : ℝ≥0∞) = q := ENNReal.coe_toNNReal hqfin
  have hfin' := hfin c' (hc'e ▸ hq)
  have hint : IntegrableOn (fun x => |F x| ^ (-(c' : ℝ))) U volume := by
    rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
    exact ⟨(by fun_prop : Measurable (fun x => |F x| ^ (-(c' : ℝ)))).aestronglyMeasurable, hfin'⟩
  have hint1 : IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) U volume := by
    simpa only [mul_one] using hint
  rw [← hc'e]
  exact le_sSup ⟨c', rfl, U, hU, Set.singleton_subset_iff.2 h0, hint1⟩

/-- **The `≤` reduction.** `rlctAtOn F 0 ≤ t` reduces to: every admissible `c'` (integrable on some
open `Ω ∋ 0`) satisfies `c' ≤ t` (`sSup_le`). The consumer discharges the hypothesis from "a leaf
diverges above `t`" (the divergence localises at the origin, killing admissibility on any `Ω`). -/
theorem rlctAtOn_le_of_adm_le {E : Type*} [MeasureSpace E] [TopologicalSpace E] [Zero E]
    (F : E → ℝ) (t : ℝ≥0∞)
    (hadm : ∀ c' : NNReal, (∃ Ω : Set E, IsOpen Ω ∧ (0 : E) ∈ Ω ∧
        IntegrableOn (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) Ω volume) →
      (c' : ℝ≥0∞) ≤ t) :
    rlctAtOn F 0 ≤ t := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le
  rintro c ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
  exact hadm c' ⟨Ω, hΩopen, hKΩ rfl, hint⟩

end DLNFibre.DLN.RLCT
