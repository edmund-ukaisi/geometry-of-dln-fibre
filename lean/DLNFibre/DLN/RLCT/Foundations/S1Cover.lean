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

/-! ## The neighbourhood-quantifier crux (the `≤`-direction localisation)

`rlctAtOn_le_of_adm_le` reduces `rlctAtOn F 0 ≤ t` to: every `c'` integrable on *some* open `Ω ∋ 0`
satisfies `c' ≤ t`. The cover (`g5_pivotNode`) only gives divergence on a *fixed* domain — so the
quantifier over *all* `Ω` is genuinely extra content (NOT discharged by `rlctAtOn_comp_homeomorph`:
the pivot blow-up is not a homeomorphism at the exceptional divisor, where `0` is not a regular
value — the divisor collapses to `0`, so there is no local inverse and no admissible-nbhd bijection;
Codex 2026-06-21). The sound route (Codex Q3) pushes all the geometry into one **ε-independent**
monomial-divergence lemma, then localises by extracting a small box from any open `Ω ∋ 0`.

The argument, made explicit (the controller's "report the actual `∃Ω ↔ fixed-U` argument"):

1. **Box-from-nbhd.** Any open `Ω ∋ 0` in `Fin N → ℝ` contains a closed cube `[−ε, ε]^N` for some
   `ε > 0` (`Metric.mem_nhds_iff` ⟹ a ball ⟹ a sub-cube; the `Pi`-`sup`-metric makes a cube a ball).
2. **ε-independent divergence.** For a leaf monomial with `c' ≥` its `monomialThreshold`, the leaf
   integral over the chart-preimage of `[0, ε]^N` is `⊤` for *every* `ε > 0` — the singularity sits
   on a coordinate hyperplane through `0`, and the box always reaches it (scale-invariance of the
   one-variable test `∫₀^ε u^{h − 2kc} du = ⊤` for `c ≥ (h+1)/(2k)`, ε-uniform).
3. **Localise.** Given admissible `c'` on `Ω`: `IntegrableOn |F|^{−c'} Ω` ⟹ finite on the sub-box ⟹
   (cover on the box) every leaf finite ⟹ every leaf-threshold `> c'` ⟹ `c' ≤ ⨅ thresholds = t`.

`rlctAtOn_le_of_box_diverges` packages steps 1+3 (proven here — the abstract localisation is pure
measure logic: `cubeBox_subset_of_isOpen` + `lintegral_mono_set` against the `hdiv` hypothesis). The
step-2 atom (`monomialIntegrand_lintegral_box_eq_top`, the ε-uniform monomial divergence) lives in
the `Skeleton`-dependent `Case222Cover` — it is the genuine analytic content the consumer supplies.
-/

open scoped BigOperators in
/-- **The closed cube `[−ε, ε]^N`** (the box extracted from an open nbhd of the origin). -/
def cubeBox (N : ℕ) (ε : ℝ) : Set (Fin N → ℝ) := Set.univ.pi (fun _ => Set.Icc (-ε) ε)

/-- The cube `[−ε, ε]^N` (`ε > 0`) is a neighbourhood-witness: any open `Ω ∋ 0` contains such a
cube. The sup-metric ball `Metric.ball 0 ε` in `Fin N → ℝ` is `Set.univ.pi (Ioo (−ε) ε)` (the
`Pi.sup` metric), so a smaller cube sits inside it; `Metric.mem_nhds_iff` extracts the ball from the
open set (`Pi.lintegral`/`cubeBox` measurable). -/
theorem cubeBox_subset_of_isOpen {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (h0 : (0 : Fin N → ℝ) ∈ Ω) :
    ∃ ε > 0, cubeBox N ε ⊆ Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hΩ.mem_nhds h0)
  refine ⟨r / 2, by linarith, ?_⟩
  intro x hx
  apply hball
  rw [Metric.mem_ball]
  simp only [cubeBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left] at hx
  rw [dist_pi_lt_iff hr]
  intro i
  rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_lt]
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

/-- **The `≤`-direction localisation (the nbhd-quantifier discharge).** `rlctAtOn F 0 ≤ t` from a
single ε-independent divergence hypothesis: if for every `ε > 0`, `∫⁻_{cubeBox ε} |F|^{−c'} = ⊤`
whenever `c' > t`, then no `c' > t` is admissible on any open `Ω ∋ 0` (each `Ω` contains a cube
`cubeBox ε`; finiteness on `Ω` would force finiteness on the cube by `lintegral_mono_set`,
contradicting the hypothesis), so `rlctAtOn F 0 ≤ t`. This is the abstract packaging of the crux —
the consumer (`Case222Cover`) supplies `hdiv` from the cover + the per-leaf ε-independent monomial
divergence (`monomialIntegrand_lintegral_box_eq_top`). -/
theorem rlctAtOn_le_of_box_diverges {N : ℕ} (F : (Fin N → ℝ) → ℝ) (hFm : Measurable F) (t : ℝ≥0∞)
    (hdiv : ∀ c' : NNReal, t < (c' : ℝ≥0∞) → ∀ ε > 0,
      ∫⁻ x in cubeBox N ε, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) = ⊤) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ t := by
  apply rlctAtOn_le_of_adm_le F t
  intro c' ⟨Ω, hΩopen, h0, hint⟩
  by_contra hgt
  rw [not_le] at hgt
  -- strip the trivial weight; `|F|^{−c'}` is integrable on `Ω`
  have hintF : IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Ω volume := by
    simpa only [mul_one] using hint
  -- extract a cube `[−ε, ε]^N ⊆ Ω`
  obtain ⟨ε, hε, hsub⟩ := cubeBox_subset_of_isOpen hΩopen h0
  -- `∫⁻_Ω ofReal|F|^{−c'} < ⊤` (finite-integral of the nonneg integrand)
  have hΩfin : ∫⁻ x in Ω, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) ∂volume < ⊤ := by
    rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
    exact hintF.2
  -- monotone over the subset `cubeBox N ε ⊆ Ω`, contradicting the ε-divergence
  have hbox : ∫⁻ x in cubeBox N ε, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) ∂volume < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hsub) hΩfin
  rw [hdiv c' hgt ε hε] at hbox
  exact lt_irrefl _ hbox

end DLNFibre.DLN.RLCT
