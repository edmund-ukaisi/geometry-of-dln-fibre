import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.S1Additive
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Fubini` — the smooth-block Fubini RLCT lemma (S1.5 restated)

L2's analytic engine (pp's `l2-architecture-card.md`, re-adjudicated 2026-06-21): adding a regular
quadratic block `∑_i x_i²` to a core `H(z)` shifts the chart's RLCT by exactly `n/2`:
`rlctAt (∑ x_i² + H) = n/2 + λ_core`. This replaces the abstract disjoint-block additivity (the 12th
fidelity finding showed that false two ways + needs uncitable Laplace machinery).

## Route B (iterated-1D), per the controller's bridge-minimising tie-breaker
L2's regular coords live on the **Params-flat product measure** (`Fin N → ℝ`), not EuclideanSpace
Haar measure. So this file works on the product `ℝ × W` and proves the **`n = 1` step**
`rlctAt (x² + H) = 1/2 + λ_core`, to be iterated over the `n` regular coordinates — staying on the
product measure throughout, with **no EuclideanSpace↔Params-flat bridge**. The smooth-block side is
the `1`-D integrability `|x|^{−2a}` (cf. `S1Additive`), and the cusp side uses
the elementary `1`-D interval volume `vol{x : x² ≤ s} = 2√s` (not `addHaar` on `ℝⁿ`).

## The two directions are NOT symmetric (fm-2 SPECIFY-phase de-risk, Codex-confirmed)
- **`≥` / integrability (LIGHT):** for `c = a + b` with `a < 1/2`, `b < λ_core`, the a.e. pointwise
  comparison `(x² + H)^{−c} ≤ |x|^{−2a}·H^{−b}` (both nonneg) dominates the joint density by a
  product, integrable by `Integrable.mul_prod`. Delivered here: `cmpF` + `step_integrableOn`.
- **`≤` / non-integrability (the cusp):** the naive comparison goes the wrong way; needs the cusp
  lower bound (`x² + H ≤ 2H` on `{x² ≤ H}`, the exact `1`-D interval volume `2√s`, Tonelli, then the
  core's divergence at the shifted exponent). Atoms here (`oneDimCuspVol`, `cusp_lower_bound`); the
  full divergence assembly is a follow-on.

## HYGIENE — the core must be nonzero a.e. (the 12th-finding trap, threaded as a hypothesis)
The lemma is FALSE for abstract `H ≥ 0, ≢ 0` (germ-vanishing `H ⟹ rlctAt H = ⊤`). The honest
statement uses `hHne : H ≠ 0 a.e.` (true for the monomial core `∏_j |z_j|^{2k_j}`, vanishing only
on the null coordinate hyperplanes), threaded as a hypothesis rather than left implicit; the
monomial-specific facts live in the core's own threshold (S2's domain) at the R1 use-site.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

/-! ## RLCT invariance under a measure-preserving homeomorphism (iteration infrastructure)

`rlctAtOn` is unchanged by precomposition with a measure-preserving homeomorphism `e`: the
admissible nbhds and their integrals transport across `e` (open-image / preimage + the measure-
change-of-variables `MeasurePreserving.integrableOn_image`). This is what lets the `n = 1` step
`step_rlct` be iterated over the regular coordinates via the `Fin`-peeling chart
`(Fin (n+1) → ℝ) × Y ≃ ℝ × ((Fin n → ℝ) × Y)`, staying on the product (Params-flat) measure. -/

/-- **RLCT is invariant under a measure-preserving homeomorphism.** For `e : M ≃ₜ M'` measure-
preserving (a `MeasurableEmbedding`), `rlctAtOn (F ∘ e) w0 = rlctAtOn F (e w0)`. The admissible sets
biject: `Ω ↦ e '' Ω` (open, `e.isOpenMap`) with `MeasurePreserving.integrableOn_image`, and back via
`e ⁻¹' Ω'` with `integrableOn_comp_preimage`. -/
theorem rlctAtOn_comp_homeomorph {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
    [MeasureSpace M'] [TopologicalSpace M']
    (e : M ≃ₜ M') (he : MeasurePreserving e volume volume) (hemb : MeasurableEmbedding e)
    (F : M' → ℝ) (w0 : M) :
    rlctAtOn (fun w => F (e w)) w0 = rlctAtOn F (e w0) := by
  unfold rlctAtOn weightedThreshold
  congr 1
  ext c
  constructor
  · rintro ⟨c', rfl, Ω, hΩopen, hw0, hint⟩
    refine ⟨c', rfl, e '' Ω, e.isOpenMap _ hΩopen, ?_, ?_⟩
    · exact Set.singleton_subset_iff.2 ⟨w0, hw0 rfl, rfl⟩
    · rw [he.integrableOn_image hemb]; convert hint using 2
  · rintro ⟨c', rfl, Ω, hΩopen, hw0, hint⟩
    refine ⟨c', rfl, e ⁻¹' Ω, hΩopen.preimage e.continuous, ?_, ?_⟩
    · exact Set.singleton_subset_iff.2 (hw0 rfl)
    · rw [show (fun w => |(fun w => F (e w)) w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w)
          = (fun w => |F w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) ∘ e from rfl]
      rw [he.integrableOn_comp_preimage hemb]; exact hint

/-! ## The `Fin`-peeling chart (iteration infrastructure)

To iterate `step_rlct` over the `n` regular coordinates, peel one coordinate per step via a
measure-preserving homeomorphism `(Fin (n+1) → ℝ) × Y ≃ₜ ℝ × ((Fin n → ℝ) × Y)`. The peel itself is
`MeasurableEquiv.piFinSuccAbove 0` (forward `x ↦ (x 0, x ∘ succAbove 0)`, inverse `Fin.cons`), made
a `Homeomorph` (both maps continuous) and measure-preserving (`volume_preserving_piFinSuccAbove`);
the `× Y` factor and re-association are `prodCongr`/`prodAssoc` + `MeasurePreserving.prod`/
`measurePreserving_prodAssoc`. Stays on the product (Params-flat) measure — no Haar bridge. -/

/-- `(Fin (n+1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ)`, peeling the `0`-th coordinate. Forward `x ↦ (x 0, x ∘
succAbove 0)` (continuous); inverse `Fin.cons` (continuous, `Continuous.finCons`).
Measure-preserving (`finPeel_mp`). -/
noncomputable def finPeel (n : ℕ) : (Fin (n + 1) → ℝ) ≃ₜ (ℝ × (Fin n → ℝ)) where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).toEquiv
  continuous_toFun :=
    Continuous.prodMk (continuous_apply 0) (continuous_pi (fun j => continuous_apply _))
  continuous_invFun := by
    have hinv : ⇑(((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1))).toEquiv).symm)
        = fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2 := by
      funext p
      show (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1))).symm p = _
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact Fin.insertNth_zero' p.1 p.2
    show Continuous
      (⇑(((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1))).toEquiv).symm))
    rw [hinv]; exact Continuous.finCons continuous_fst continuous_snd

/-- `finPeel` is measure-preserving (`volume_preserving_piFinSuccAbove`). -/
theorem finPeel_mp (n : ℕ) : MeasurePreserving (finPeel n) :=
  volume_preserving_piFinSuccAbove (fun _ => ℝ) 0

/-- The `Fin`-peeling product chart `(Fin (n+1) → ℝ) × Y ≃ₜ ℝ × ((Fin n → ℝ) × Y)`:
`finPeel` on the first factor, then re-associate. Measure-preserving (`chartN_mp`). -/
noncomputable def chartN (n : ℕ) (Y : Type*) [TopologicalSpace Y] [MeasureSpace Y] :
    ((Fin (n + 1) → ℝ) × Y) ≃ₜ (ℝ × ((Fin n → ℝ) × Y)) :=
  ((finPeel n).prodCongr (Homeomorph.refl Y)).trans (Homeomorph.prodAssoc ℝ (Fin n → ℝ) Y)

/-- The `Fin`-peeling product chart is measure-preserving (`MeasurePreserving.prod` of `finPeel_mp`
and the identity, then `measurePreserving_prodAssoc`; the ambient `volume`s are products by
`Measure.volume_eq_prod`). -/
theorem chartN_mp {Y : Type*} [TopologicalSpace Y] [MeasureSpace Y]
    [SigmaFinite (volume : Measure Y)] (n : ℕ) : MeasurePreserving (chartN n Y) := by
  have h1 : MeasurePreserving (Prod.map (finPeel n) (id : Y → Y)) (volume) (volume) := by
    rw [show (volume : Measure ((Fin (n + 1) → ℝ) × Y)) = (volume).prod (volume) from
        Measure.volume_eq_prod _ _,
      show (volume : Measure ((ℝ × (Fin n → ℝ)) × Y)) = (volume).prod (volume) from
        Measure.volume_eq_prod _ _]
    exact (finPeel_mp n).prod (MeasurePreserving.id volume)
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × (Fin n → ℝ)) × Y ≃ᵐ ℝ × ((Fin n → ℝ) × Y)) (volume)
      (volume) := by
    rw [show (volume : Measure ((ℝ × (Fin n → ℝ)) × Y))
          = ((volume).prod (volume)).prod (volume) from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
      show (volume : Measure (ℝ × ((Fin n → ℝ) × Y)))
          = (volume).prod ((volume).prod (volume)) from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
    exact measurePreserving_prodAssoc volume volume volume
  exact h2.comp h1

/-! ## Admissible-exponent down-set (for the threshold-lift `≥` direction)

The set of exponents `c'` for which `|H|^{−c'}` is locally integrable at `w0` is a **down-set**: a
smaller exponent stays admissible. The catch under Lean's `rpow` convention is that `|g|^{−c'}`
*increases* in `c'` where `|g| < 1` (near the singularity) — so the bound is the two-sided
`|g|^{−b'} ≤ |g|^{−d'} + 1` (`rpow_neg_le_add_one`), integrable on a **bounded** (finite-measure)
neighbourhood. This is what turns `b' < rlctAtOn H w0` into "`b'` is admissible" inside the lift. -/

/-- The pointwise down-set bound: `|g|^{−b'} ≤ |g|^{−d'} + 1` for `0 ≤ b' ≤ d'`. Cases: `|g| ≥ 1`
(`≤ 1`), `0 < |g| < 1` (`|g|^{−b'} ≤ |g|^{−d'}`, exponent-antitone), `g = 0` (`0`, the rpow
convention). The `+1` absorbs the `|g| ≥ 1` regime where the `−d'` power alone is too small. -/
theorem rpow_neg_le_add_one (b' d' : ℝ) (g : ℝ) (hb : 0 ≤ b') (hbd : b' ≤ d') :
    |g| ^ (-b') ≤ |g| ^ (-d') + 1 := by
  rcases eq_or_lt_of_le (abs_nonneg g) with h0 | hpos
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0, neg_zero, Real.rpow_zero]; linarith [Real.rpow_nonneg (abs_nonneg g) (-d')]
    · rw [← h0, Real.zero_rpow (by linarith : -b' ≠ 0)]; positivity
  · rcases le_or_gt 1 |g| with h1 | h1
    · have : |g| ^ (-b') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      linarith [Real.rpow_nonneg hpos.le (-d')]
    · have : |g| ^ (-b') ≤ |g| ^ (-d') := Real.rpow_le_rpow_of_exponent_ge hpos h1.le (by linarith)
      linarith

/-- **Admissibility is a down-set.** On a core space with locally-finite volume (`ProperSpace` +
`IsFiniteMeasureOnCompacts` — e.g. `Fin d → ℝ`), if `|H|^{−d'}` is integrable on some open `Ω ∋ w0`
and `0 ≤ b' ≤ d'`, then `|H|^{−b'}` is integrable on some open `Ω' ∋ w0`. Shrink to the bounded
`Ω ∩ ball w0 1` (finite measure), where `rpow_neg_le_add_one` dominates `|H|^{−b'}` by the
`|H|^{−d'} + 1`. -/
theorem admissible_downset {M : Type*} [PseudoMetricSpace M] [MeasureSpace M] [ProperSpace M]
    [IsFiniteMeasureOnCompacts (volume : Measure M)] [OpensMeasurableSpace M]
    (H : M → ℝ) (hHmeas : Measurable H) (w0 : M) (b' d' : ℝ) (hb : 0 ≤ b') (hbd : b' ≤ d')
    (hd : ∃ Ω : Set M, IsOpen Ω ∧ w0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-d')) Ω volume) :
    ∃ Ω : Set M, IsOpen Ω ∧ w0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-b')) Ω volume := by
  obtain ⟨Ω, hΩopen, hw0, hint⟩ := hd
  refine ⟨Ω ∩ Metric.ball w0 1, hΩopen.inter Metric.isOpen_ball,
    ⟨hw0, Metric.mem_ball_self one_pos⟩, ?_⟩
  have hfin : volume (Ω ∩ Metric.ball w0 1) ≠ ⊤ :=
    (Metric.isBounded_ball.subset inter_subset_right).measure_lt_top.ne
  have hd' : IntegrableOn (fun w => |H w| ^ (-d')) (Ω ∩ Metric.ball w0 1) volume :=
    hint.mono_set inter_subset_left
  apply Integrable.mono' (g := fun w => |H w| ^ (-d') + 1)
    (hd'.add (integrableOn_const (hs := hfin)))
    ((by fun_prop : Measurable (fun w => |H w| ^ (-b'))).aestronglyMeasurable)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact rpow_neg_le_add_one b' d' (H w) hb hbd

/-- **Below-threshold ⟹ admissible.** If `(b : ℝ≥0∞) < rlctAtOn H y0` then `b` is an admissible core
exponent: `|H|^{−b}` is integrable on some open `Ω ∋ y0`. Via `lt_sSup` (extract a strictly-larger
admissible `d'`) + `admissible_downset` (`b ≤ d'`). The bridge feeding the threshold-lift's `≥`
direction. -/
theorem core_admissible_of_lt {M : Type*} [PseudoMetricSpace M] [MeasureSpace M] [ProperSpace M]
    [IsFiniteMeasureOnCompacts (volume : Measure M)] [OpensMeasurableSpace M]
    (H : M → ℝ) (hHmeas : Measurable H) (y0 : M) (b : NNReal)
    (hb : (b : ℝ≥0∞) < rlctAtOn H y0) :
    ∃ Ω : Set M, IsOpen Ω ∧ y0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-(b : ℝ))) Ω volume := by
  unfold rlctAtOn weightedThreshold at hb
  obtain ⟨c, hc_mem, hbc⟩ := lt_sSup_iff.1 hb
  obtain ⟨d', rfl, Ω, hΩopen, hKΩ, hint⟩ := hc_mem
  have hbd : (b : ℝ) ≤ (d' : ℝ) := by
    have : b < d' := by exact_mod_cast hbc
    exact_mod_cast this.le
  have hintd : IntegrableOn (fun w => |H w| ^ (-(d' : ℝ))) Ω volume := by
    apply hint.congr_fun _ hΩopen.measurableSet; intro w _; simp
  exact admissible_downset H hHmeas y0 (b : ℝ) (d' : ℝ) (by positivity) hbd
    ⟨Ω, hΩopen, by simpa using hKΩ, hintd⟩

/-- **Exponent `0` is always admissible.** `|H|^{−0} = 1` is integrable on the bounded `ball y0 1`
(finite measure). The base case of the `≥` direction when the core threshold is `0`. -/
theorem core_admissible_zero {M : Type*} [PseudoMetricSpace M] [MeasureSpace M] [ProperSpace M]
    [IsFiniteMeasureOnCompacts (volume : Measure M)] (H : M → ℝ) (y0 : M) :
    ∃ Ω : Set M, IsOpen Ω ∧ y0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-(0 : ℝ))) Ω volume := by
  refine ⟨Metric.ball y0 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_⟩
  have hone : (fun w : M => |H w| ^ (-(0 : ℝ))) = (fun _ => (1 : ℝ)) := by
    funext w; rw [neg_zero, Real.rpow_zero]
  rw [hone]
  exact integrableOn_const (hs := Metric.isBounded_ball.measure_lt_top.ne)

/-! ## The pointwise comparison (the `≥`-direction engine) -/

/-- **The sum-power comparison.** For `s, t > 0` and `a, b ≥ 0`,
`(s + t)^{−(a+b)} ≤ s^{−a}·t^{−b}`. From `(s+t)^a ≥ s^a` and `(s+t)^b ≥ t^b` (monotonicity of `rpow`
in the base, `a, b ≥ 0`) so `(s+t)^{a+b} ≥ s^a t^b`, then invert. The bound that splits the
joint density `(x² + H)^{−c}` into the smooth-block factor `|x|^{−2a}` and the core factor `H^{−b}`
with `a + b = c`. -/
theorem cmpF (s t a b : ℝ) (hs : 0 < s) (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (s + t) ^ (-(a + b)) ≤ s ^ (-a) * t ^ (-b) := by
  have hst : 0 < s + t := by linarith
  have h1 : s ^ a ≤ (s + t) ^ a := Real.rpow_le_rpow hs.le (by linarith) ha
  have h2 : t ^ b ≤ (s + t) ^ b := Real.rpow_le_rpow ht.le (by linarith) hb
  have hprod : s ^ a * t ^ b ≤ (s + t) ^ (a + b) := by
    calc s ^ a * t ^ b ≤ (s + t) ^ a * (s + t) ^ b :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (s + t) ^ (a + b) := by rw [← Real.rpow_add hst]
  rw [Real.rpow_neg hst.le, Real.rpow_neg hs.le, Real.rpow_neg ht.le, ← mul_inv]
  exact inv_anti₀ (by positivity) hprod

/-! ## The `n = 1` joint integrability (the `≥` direction) -/

/-- **The weighted joint density is integrable on a product neighbourhood** (the `n = 1`
`≥`-direction keystone, to be iterated over the regular coordinates). If the smooth-block density
`|x|^{−2a}` is integrable on `Icc (-ε) ε` (`a < 1/2`) and the weighted core density `|H|^{−b}·wt`
is integrable on `V` (i.e. `b` below the weighted core threshold), then the joint weighted density
`|x² + H(z)|^{−(a+b)}·wt(z)` is integrable on `Icc (-ε) ε ×ˢ V`. Proof: the a.e. comparison `cmpF`
(valid where `x, H > 0` — both a.e., the sets `{x = 0}` and `{H = 0}` null, the latter by
`hHne`) dominates the target by `|x|^{−2a}·(|H|^{−b}·wt)`, which is `Integrable.mul_prod` of the two
halves. The weight `wt ≥ 0` factors through. -/
theorem step_integrableOn
    {W : Type*} [MeasureSpace W] [SigmaFinite (volume : Measure W)]
    (H wt : W → ℝ) (hH : ∀ z, 0 ≤ H z) (hwt : ∀ z, 0 ≤ wt z)
    (hHmeas : Measurable H) (hwtmeas : Measurable wt)
    (a b ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (V : Set W)
    (hHne : ∀ᵐ z ∂(volume.restrict V), H z ≠ 0)
    (hx : IntegrableOn (fun x : ℝ => |x| ^ (-(2 * a))) (Icc (-ε) ε) volume)
    (hz : IntegrableOn (fun z : W => |H z| ^ (-b) * wt z) V volume) :
    IntegrableOn (fun p : ℝ × W => |p.1 ^ 2 + H p.2| ^ (-(a + b)) * wt p.2)
      ((Icc (-ε) ε) ×ˢ V) volume := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hdom : Integrable (fun p : ℝ × W => |p.1| ^ (-(2 * a)) * (|H p.2| ^ (-b) * wt p.2))
      ((volume.restrict (Icc (-ε) ε)).prod (volume.restrict V)) :=
    Integrable.mul_prod hx hz
  refine hdom.mono' ((by fun_prop : Measurable _).aestronglyMeasurable) ?_
  have hxne0 : ∀ᵐ x ∂(volume.restrict (Icc (-ε) ε)), x ≠ 0 := by
    apply ae_restrict_of_ae; exact ae_iff.2 (by simp [measure_singleton])
  have hxne' := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Icc (-ε) ε)) (ν := volume.restrict V)).tendsto_ae.eventually hxne0
  have hHne' := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Icc (-ε) ε)) (ν := volume.restrict V)).tendsto_ae.eventually hHne
  filter_upwards [hxne', hHne'] with p hxp hgp
  have hsx : 0 < p.1 ^ 2 := by positivity
  have htg : 0 < H p.2 := lt_of_le_of_ne (hH p.2) (Ne.symm hgp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (hwt p.2), abs_of_nonneg (by positivity : (0 : ℝ) ≤ p.1 ^ 2 + H p.2)]
  have hcmp : (p.1 ^ 2 + H p.2) ^ (-(a + b)) ≤ |p.1| ^ (-(2 * a)) * |H p.2| ^ (-b) := by
    calc (p.1 ^ 2 + H p.2) ^ (-(a + b)) ≤ (p.1 ^ 2) ^ (-a) * (H p.2) ^ (-b) :=
          cmpF _ _ a b hsx htg ha hb
      _ = |p.1| ^ (-(2 * a)) * |H p.2| ^ (-b) := by
          rw [abs_of_nonneg (hH p.2), ← sq_abs p.1, ← Real.rpow_natCast |p.1| 2,
              ← Real.rpow_mul (abs_nonneg _)]
          ring_nf
  calc (p.1 ^ 2 + H p.2) ^ (-(a + b)) * wt p.2
      ≤ (|p.1| ^ (-(2 * a)) * |H p.2| ^ (-b)) * wt p.2 :=
        mul_le_mul_of_nonneg_right hcmp (hwt p.2)
    _ = |p.1| ^ (-(2 * a)) * (|H p.2| ^ (-b) * wt p.2) := by ring

/-! ## The `n = 1` cusp lower bound (the `≤` direction)

The elementary `1`-D ingredients for the non-integrability direction (Route B keeps this off
EuclideanSpace: the `x`-slice volume is a plain interval, `Real.volume_Icc`). -/

/-- **The `1`-D cusp slice volume.** `vol{x : ℝ | x² ≤ s} = 2√s` for `s ≥ 0` — the set is the
interval `[-√s, √s]`. The elementary replacement for the `n`-dim ball volume (no `addHaar`,
no EuclideanSpace), the key shave that keeps Route B on the product measure. -/
theorem oneDimCuspVol (s : ℝ) (hs : 0 ≤ s) :
    volume {x : ℝ | x ^ 2 ≤ s} = ENNReal.ofReal (2 * Real.sqrt s) := by
  have hset : {x : ℝ | x ^ 2 ≤ s} = Icc (-Real.sqrt s) (Real.sqrt s) := by
    ext x; simp only [mem_setOf_eq, mem_Icc]
    constructor
    · intro h
      have h2 := Real.sqrt_le_sqrt h
      rw [Real.sqrt_sq_eq_abs] at h2
      exact abs_le.1 h2
    · rintro ⟨h1, h2⟩; nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg s]
  rw [hset, Real.volume_Icc]; ring_nf

/-- **The cusp inner slice.** For `s ≤ R²` (so the cusp `{x² ≤ s}` sits inside `Icc (-R) R`), the
`x`-integral of a constant-`k` integrand supported on `{x² ≤ s}` is `k · 2√s`. Combines the cusp
containment (`{x² ≤ s} ⊆ Icc (-R) R`) with `oneDimCuspVol`. The inner step of the cusp Tonelli. -/
theorem inner_slice (s R : ℝ) (hs : 0 ≤ s) (hR : 0 ≤ R) (hsR : s ≤ R ^ 2) (k : ℝ≥0∞) :
    ∫⁻ x in Icc (-R) R, (if x ^ 2 ≤ s then k else 0)
      = k * ENNReal.ofReal (2 * Real.sqrt s) := by
  have hsub : {x : ℝ | x ^ 2 ≤ s} ⊆ Icc (-R) R := by
    intro x hx; simp only [mem_setOf_eq] at hx; simp only [mem_Icc]
    have : |x| ≤ R := by
      rw [← Real.sqrt_sq hR]
      exact (Real.sqrt_sq_eq_abs x) ▸ Real.sqrt_le_sqrt (le_trans hx hsR)
    exact abs_le.1 this
  have hms : MeasurableSet {x : ℝ | x ^ 2 ≤ s} := measurableSet_le (by fun_prop) measurable_const
  have hind : (fun x : ℝ => if x ^ 2 ≤ s then k else 0)
      = Set.indicator {x : ℝ | x ^ 2 ≤ s} (fun _ => k) := by
    funext x; simp only [Set.indicator_apply, mem_setOf_eq]
  rw [hind, lintegral_indicator hms, setLIntegral_const, Measure.restrict_apply hms,
      inter_eq_self_of_subset_left hsub, oneDimCuspVol s hs, mul_comm]

/-- **The cusp pointwise lower bound.** On `{x² ≤ H z}`, `x² + H ≤ 2H`, so (exponent `−c < 0`,
antitone) `(2 H)^{−c} ≤ (x² + H)^{−c}`; weighted forms compare via `wt ≥ 0`. The `H = 0` corner is
handled directly (both sides vanish, the `≡0`-loss convention). The lower bound that drives the
non-integrability direction once integrated against the core. -/
theorem cusp_lower_bound {W : Type*} (H wt : W → ℝ) (hH : ∀ z, 0 ≤ H z) (hwt : ∀ z, 0 ≤ wt z)
    (c : ℝ) (hc : 0 < c) (p : ℝ × W) (hcusp : p.1 ^ 2 ≤ H p.2) :
    ENNReal.ofReal ((2 * H p.2) ^ (-c) * wt p.2)
      ≤ ENNReal.ofReal (|p.1 ^ 2 + H p.2| ^ (-c) * wt p.2) := by
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (hwt p.2)
  rcases eq_or_lt_of_le (hH p.2) with hg0 | hgpos
  · have hxn : p.1 ^ 2 = 0 := le_antisymm (hcusp.trans hg0.ge) (by positivity)
    rw [← hg0, hxn]; simp [Real.zero_rpow (by linarith : -c ≠ 0)]
  · have hFle : p.1 ^ 2 + H p.2 ≤ 2 * H p.2 := by linarith
    have hFpos : 0 < p.1 ^ 2 + H p.2 := by positivity
    rw [abs_of_nonneg hFpos.le]
    exact Real.rpow_le_rpow_of_nonpos hFpos hFle (by linarith)

/-! ## The `n = 1` cusp divergence (the `≤` direction) -/

/-- **The `n = 1` cusp divergence.** If the core diverges at the shifted exponent —
`∫_V (2^{1−c}·(H z)^{1/2−c}·wt z) = ⊤` (the core's own weighted threshold `< c − 1/2`) — then
the joint density `|x² + H(z)|^{−c}·wt(z)` is non-integrable on `Icc (-R) R ×ˢ V`. The cusp lower
bound: restrict the integrand below by `[x² ≤ H z]·(2 H z)^{−c}·wt z` (`cusp_lower_bound`), Tonelli
(`setLIntegral_prod_symm`, `y`-outer), the inner `x`-slice `= (2 H z)^{−c}·wt z · 2√(H z)`
(`inner_slice`, using `hHle` so the cusp `{x² ≤ H z}` sits in `Icc (-R) R`), which equals
`2^{1−c}·(H z)^{1/2−c}·wt z`, so the `y`-integral is exactly the divergent core integral. The
`hHne : H ≠ 0 a.e.` hypothesis (as in `step_integrableOn`) dodges the `H = 0` corner where the inner
identity fails at `c = 1/2`. Stated as `lintegral = ⊤`; `IntegrableOn` failure follows by
`IntegrableOn.setLIntegral_lt_top`. -/
theorem step_lintegral_top
    {W : Type*} [MeasureSpace W] [SigmaFinite (volume : Measure W)]
    (H wt : W → ℝ) (hH : ∀ z, 0 ≤ H z) (hwt : ∀ z, 0 ≤ wt z)
    (hHmeas : Measurable H) (hwtmeas : Measurable wt)
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (V : Set W) (hVmeas : MeasurableSet V)
    (hHne : ∀ᵐ z ∂(volume.restrict V), H z ≠ 0)
    (hHle : ∀ z ∈ V, H z ≤ R ^ 2)
    (hcore_top : ∫⁻ z in V, ENNReal.ofReal (2 ^ (1 - c) * (H z) ^ (1 / 2 - c) * wt z) = ⊤) :
    ∫⁻ p in (Icc (-R) R) ×ˢ V, ENNReal.ofReal (|p.1 ^ 2 + H p.2| ^ (-c) * wt p.2) = ⊤ := by
  classical
  set LBf : ℝ × W → ℝ≥0∞ :=
    fun p => if p.1 ^ 2 ≤ H p.2 then ENNReal.ofReal ((2 * H p.2) ^ (-c) * wt p.2) else 0 with hLBf
  have hmeasLB : Measurable LBf := by
    apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
  have hmono : ∫⁻ p in (Icc (-R) R) ×ˢ V, LBf p
      ≤ ∫⁻ p in (Icc (-R) R) ×ˢ V, ENNReal.ofReal (|p.1 ^ 2 + H p.2| ^ (-c) * wt p.2) := by
    apply lintegral_mono; intro p
    by_cases hcusp : p.1 ^ 2 ≤ H p.2
    · simp only [hLBf, if_pos hcusp]; exact cusp_lower_bound H wt hH hwt c hc p hcusp
    · simp only [hLBf, if_neg hcusp]; exact zero_le _
  suffices hLBtop : ∫⁻ p in (Icc (-R) R) ×ˢ V, LBf p = ⊤ by
    rw [hLBtop] at hmono; exact top_le_iff.1 hmono
  rw [Measure.volume_eq_prod, setLIntegral_prod_symm LBf (hmeasLB.aemeasurable.restrict),
    ← hcore_top]
  apply lintegral_congr_ae
  filter_upwards [hHne, ae_restrict_mem hVmeas] with y hyne hyV
  have hgpos : 0 < H y := lt_of_le_of_ne (hH y) (Ne.symm hyne)
  have hinner : ∫⁻ x in Icc (-R) R, LBf (x, y)
      = ENNReal.ofReal ((2 * H y) ^ (-c) * wt y) * ENNReal.ofReal (2 * Real.sqrt (H y)) := by
    simp only [hLBf]; exact inner_slice (H y) R (hH y) hR.le (hHle y hyV) _
  rw [hinner, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hwt y))]
  congr 1
  have hsqrt : Real.sqrt (H y) = (H y) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (H y)
  have e2 : ((2 : ℝ) * (H y)) ^ (-c) = (2 : ℝ) ^ (-c) * (H y) ^ (-c) :=
    Real.mul_rpow (by norm_num) hgpos.le
  have c2 : (2 : ℝ) ^ (-c) * (2 : ℝ) = 2 ^ (1 - c) := by
    rw [show (1 : ℝ) - c = -c + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have chy : (H y) ^ (-c) * (H y) ^ ((1 : ℝ) / 2) = (H y) ^ ((1 : ℝ) / 2 - c) := by
    rw [← Real.rpow_add hgpos]; ring_nf
  rw [hsqrt, e2]
  calc (2 : ℝ) ^ (-c) * (H y) ^ (-c) * wt y * (2 * (H y) ^ ((1 : ℝ) / 2))
      = ((2 : ℝ) ^ (-c) * 2) * ((H y) ^ (-c) * (H y) ^ ((1 : ℝ) / 2)) * wt y := by ring
    _ = 2 ^ (1 - c) * (H y) ^ ((1 : ℝ) / 2 - c) * wt y := by rw [c2, chy]

/-! ## The threshold-lift, `≤` direction (`n = 1`) — the cusp contrapositive -/

/-- **Joint-integrable ⟹ core-integrable at the shifted exponent** (the `≤`-direction key, the
contrapositive of `step_lintegral_top`). If `|x² + H|^{−c}` is integrable on the rectangle
`Icc (-R) R ×ˢ V` (with `H ≤ R²` on `V`, so the cusp sits inside, and `H ≠ 0` a.e. on `V`), then
`|H|^{−(c − 1/2)}` is integrable on `V`. Proof: were it not, its `lintegral` on `V` would be `⊤`, so
(factoring `2^{1−c}`) the cusp hypothesis `hcore_top` holds, and `step_lintegral_top` forces
the joint `lintegral` to `⊤` — contradicting `IntegrableOn.setLIntegral_lt_top`. -/
theorem core_int_of_joint_int {Y : Type*} [MeasureSpace Y] [SigmaFinite (volume : Measure Y)]
    (H : Y → ℝ) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H)
    (c R : ℝ) (hc : 1 / 2 < c) (hR : 0 < R) (V : Set Y) (hVmeas : MeasurableSet V)
    (hHne : ∀ᵐ z ∂(volume.restrict V), H z ≠ 0) (hHle : ∀ z ∈ V, H z ≤ R ^ 2)
    (hjoint : IntegrableOn (fun p : ℝ × Y => |p.1 ^ 2 + H p.2| ^ (-c) * (1 : ℝ))
      ((Icc (-R) R) ×ˢ V) volume) :
    IntegrableOn (fun z => |H z| ^ (-(c - 1 / 2))) V volume := by
  by_contra hcon
  have htop : ∫⁻ z in V, ENNReal.ofReal (|H z| ^ (-(c - 1 / 2))) = ⊤ := by
    by_contra h
    refine hcon ⟨(by fun_prop : Measurable (fun z => |H z| ^ (-(c - 1 / 2)))).aemeasurable
      |>.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hz : ∀ z, ‖|H z| ^ (-(c - 1 / 2))‖ₑ = ENNReal.ofReal (|H z| ^ (-(c - 1 / 2))) :=
      fun z => by
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    simp_rw [hz]; exact lt_top_iff_ne_top.2 h
  have hcore_top : ∫⁻ z in V, ENNReal.ofReal (2 ^ (1 - c) * (H z) ^ (1 / 2 - c) *
      (fun _ => (1 : ℝ)) z) = ⊤ := by
    have heq : ∀ z, ENNReal.ofReal (2 ^ (1 - c) * (H z) ^ (1 / 2 - c) * (1 : ℝ))
        = ENNReal.ofReal (2 ^ (1 - c)) * ENNReal.ofReal (|H z| ^ (-(c - 1 / 2))) := fun z => by
      rw [mul_one, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_of_nonneg (hH z), show (1 : ℝ) / 2 - c = -(c - 1 / 2) by ring]
    simp only [heq]
    rw [lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (2 ^ (1 - c)) ≠ ⊤), htop,
      ENNReal.mul_top (by simp [show (0 : ℝ) < 2 ^ (1 - c) from by positivity])]
  have hjtop := step_lintegral_top H (fun _ => 1) hH (fun _ => zero_le_one) hHmeas measurable_const
    c R (by linarith) hR V hVmeas hHne hHle hcore_top
  have hjfin := hjoint.setLIntegral_lt_top
  rw [hjtop] at hjfin
  exact (lt_irrefl ⊤) hjfin

/-! ## The threshold-lift, `≥` direction (`n = 1`)

Assembling the integral `≥` engine into the RLCT inequality `½ + λ_H ≤ rlctAtOn(x² + H)`. The core
space `Y` has locally-finite volume (`ProperSpace` + `IsFiniteMeasureOnCompacts` — holds for
`Fin d → ℝ`) so the down-set lemma applies. -/

/-- A split exponent `a + b` (`a < 1/2` smooth side, `b` core-admissible) is joint-admissible:
some open `Ω ∋ (0, y0)` carries `|x² + H|^{−(a+b)}` integrably. `step_integrableOn` on the rectangle
`Icc (-1) 1 ×ˢ V` (`V = Ω_core ∩` an open nbhd witnessing `hHne`), restricted to the open
`Ioo (-1) 1 ×ˢ V`. -/
theorem joint_admissible_of_split {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y]
    [SigmaFinite (volume : Measure Y)]
    (H : Y → ℝ) (y0 : Y) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H)
    (hHne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), H z ≠ 0)
    (a b : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hb0 : 0 ≤ b)
    (hbadm : ∃ Ω : Set Y, IsOpen Ω ∧ y0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-b)) Ω volume) :
    ∃ Ω : Set (ℝ × Y), IsOpen Ω ∧ (0, y0) ∈ Ω ∧
      IntegrableOn (fun p : ℝ × Y => |p.1 ^ 2 + H p.2| ^ (-(a + b)) * (1 : ℝ)) Ω volume := by
  obtain ⟨Ωc, hΩcopen, hy0c, hcint⟩ := hbadm
  obtain ⟨U, hU, hUne⟩ := hHne
  have hxint : IntegrableOn (fun x : ℝ => |x| ^ (-(2 * a))) (Icc (-1 : ℝ) 1) volume := by
    rw [abs_rpow_integrableOn_Icc_symm _ _ (by norm_num : (0 : ℝ) < 1)]; linarith
  obtain ⟨U₀, hU₀sub, hU₀open, hy0U₀⟩ := _root_.mem_nhds_iff.1 hU
  set V := Ωc ∩ U₀ with hV
  have hVopen : IsOpen V := hΩcopen.inter hU₀open
  have hcintV : IntegrableOn (fun w => |H w| ^ (-b) * (1 : ℝ)) V volume := by
    simp only [mul_one]; exact hcint.mono_set (inter_subset_left : V ⊆ Ωc)
  have hHneV : ∀ᵐ z ∂(volume.restrict V), H z ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun x hx => hU₀sub hx.2) hUne
  have hstep := step_integrableOn H (fun _ => 1) hH (fun _ => zero_le_one) hHmeas measurable_const
    a b 1 ha0 hb0 V hHneV hxint hcintV
  exact ⟨Ioo (-1 : ℝ) 1 ×ˢ V, isOpen_Ioo.prod hVopen, ⟨by norm_num, hy0c, hy0U₀⟩,
    hstep.mono_set (Set.prod_mono Ioo_subset_Icc_self (subset_refl V))⟩

/-- **The threshold-lift, `≥` direction.** `½ + rlctAtOn H y0 ≤ rlctAtOn (x² + H) (0, y0)`. By
`le_of_forall_lt_imp_le_of_dense`: any `q < ½ + λ_H` splits (`ENNReal.exists_lt_add_of_lt_add`, or
`lt_iff_exists_nnreal_btwn` when `λ_H = 0`) as `a + b` with `a < 1/2`, `b` core-admissible
(`core_admissible_of_lt` / `core_admissible_zero`); `joint_admissible_of_split` then puts `a + b` in
the joint admissible set, so `q ≤ a + b ≤ sSup`. -/
theorem step_rlct_ge {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [OpensMeasurableSpace Y]
    (H : Y → ℝ) (y0 : Y) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H)
    (hHne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), H z ≠ 0) :
    (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 ≤ rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) := by
  have half_ne_top : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]; exact ENNReal.coe_ne_top
  have half_ne_zero : (1 / 2 : ℝ≥0∞) ≠ 0 := by
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
    exact_mod_cast (by norm_num : (1 / 2 : NNReal) ≠ 0)
  have half_toReal : ((1 / 2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]; simp
  apply le_of_forall_lt_imp_le_of_dense
  intro q hq
  set lamH := rlctAtOn H y0 with hlamH
  have push : ∀ (a b : ℝ), 0 ≤ a → a < 1 / 2 → 0 ≤ b → q ≤ ENNReal.ofReal (a + b) →
      (∃ Ω : Set Y, IsOpen Ω ∧ y0 ∈ Ω ∧ IntegrableOn (fun w => |H w| ^ (-b)) Ω volume) →
      q ≤ rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) := by
    intro a b ha0 ha hb0 hqle hadm
    obtain ⟨Ω, hΩopen, hmem, hint⟩ :=
      joint_admissible_of_split H y0 hH hHmeas hHne a b ha0 ha hb0 hadm
    apply hqle.trans
    unfold rlctAtOn weightedThreshold
    apply le_sSup
    refine ⟨(a + b).toNNReal, ?_, Ω, hΩopen, by simpa using hmem, ?_⟩
    · rw [ENNReal.ofReal]
    · rw [Real.coe_toNNReal _ (by linarith)]; exact hint
  by_cases hlam0 : lamH = 0
  · have hqhalf : q < (1 / 2 : ℝ≥0∞) := by simpa [hlam0] using hq
    obtain ⟨r, hqr, hrhalf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqhalf
    refine push (r : ℝ) 0 (by positivity) ?_ (le_refl 0) ?_ ?_
    · have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top half_ne_top).2 hrhalf
      rwa [half_toReal] at this
    · simpa using hqr.le
    · simpa using core_admissible_zero H y0
  · obtain ⟨u, huhalf, v, hvlam, hquv⟩ := ENNReal.exists_lt_add_of_lt_add hq half_ne_zero hlam0
    have hvfin : v ≠ ⊤ := hvlam.ne_top
    have ha_lt : (u.toReal) < 1 / 2 := by
      have := (ENNReal.toReal_lt_toReal huhalf.ne_top half_ne_top).2 huhalf
      rwa [half_toReal] at this
    have hb_lt : ((v.toNNReal : ℝ≥0∞)) < lamH := by rwa [ENNReal.coe_toNNReal hvfin]
    have hqle : q ≤ ENNReal.ofReal (u.toReal + (v.toNNReal : ℝ)) := by
      have hsum : ENNReal.ofReal (u.toReal + (v.toNNReal : ℝ)) = u + v := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity : 0 ≤ ((v.toNNReal : ℝ)))]
        rw [ENNReal.ofReal_toReal huhalf.ne_top]
        congr 1
        rw [show ENNReal.ofReal (v.toNNReal : ℝ) = ((v.toNNReal : ℝ≥0∞)) by
              rw [ENNReal.ofReal_coe_nnreal], ENNReal.coe_toNNReal hvfin]
      exact hquv.le.trans_eq hsum.symm
    exact push u.toReal (v.toNNReal : ℝ) ENNReal.toReal_nonneg ha_lt (by positivity) hqle
      (core_admissible_of_lt H hHmeas y0 v.toNNReal hb_lt)

/-! ## The threshold-lift, `≤` direction (`n = 1`) — the open-witness wrapper -/

/-- The cusp `≤`-direction's "high-`H`" piece: on `W ⊆ {H > R²}` of finite measure, `|H|^{−(c−1/2)}`
is bounded by `(R²)^{−(c−1/2)}` (the negative power is decreasing, `H > R² > 0`), hence integrable.
The harmless half of the `V₀ = {H ≤ R²} ∪ {H > R²}` split. -/
theorem core_int_high {Y : Type*} [MeasureSpace Y] (H : Y → ℝ) (hHmeas : Measurable H)
    (c R : ℝ) (hc : 1 / 2 < c) (hR : 0 < R) (W : Set Y) (hWmeas : MeasurableSet W)
    (hWfin : volume W ≠ ⊤) (hWsub : ∀ z ∈ W, R ^ 2 < H z) :
    IntegrableOn (fun z => |H z| ^ (-(c - 1 / 2))) W volume := by
  apply Integrable.mono' (g := fun _ => (R ^ 2) ^ (-(c - 1 / 2)))
    (integrableOn_const (hs := hWfin))
    ((by fun_prop : Measurable (fun z => |H z| ^ (-(c - 1 / 2)))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hWmeas] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hHpos : R ^ 2 < H z := hWsub z hz
  have hHz0 : (0 : ℝ) < H z := lt_trans (by positivity) hHpos
  rw [abs_of_nonneg hHz0.le]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hHpos.le (by linarith)

/-- **Joint-admissible ⟹ core-admissible at the shifted exponent** (open-neighbourhood form). From a
joint admissibility witness (open `Ω ∋ (0, y0)`, `c > 1/2`), produce an open `Ω' ∋ y0` carrying
`|H|^{−(c−1/2)}` integrably. Shrink `Ω` to a product `Icc (-R/2) (R/2) ×ˢ V₀` (`V₀ = ball y0 δ ⊆`
the `H ≠ 0`-witness nbhd), split `V₀ = (V₀ ∩ {H ≤ (R/2)²}) ∪ (V₀ ∩ {H > (R/2)²})`: the low part is
`core_int_of_joint_int` (cusp inside the ball), the high part `core_int_high` (bounded integrand).
The split dodges the unboundedness of merely-measurable `H` near `y0` (Codex-confirmed: no
continuity needed). -/
theorem core_adm_of_joint_adm {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [OpensMeasurableSpace Y]
    (H : Y → ℝ) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H) (y0 : Y)
    (hHne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), H z ≠ 0)
    (c : ℝ) (hc : 1 / 2 < c)
    (hjadm : ∃ Ω : Set (ℝ × Y), IsOpen Ω ∧ (0, y0) ∈ Ω ∧
      IntegrableOn (fun p : ℝ × Y => |p.1 ^ 2 + H p.2| ^ (-c) * (1 : ℝ)) Ω volume) :
    ∃ Ω : Set Y, IsOpen Ω ∧ y0 ∈ Ω ∧ IntegrableOn (fun z => |H z| ^ (-(c - 1 / 2))) Ω volume := by
  obtain ⟨Ω, hΩopen, hmem, hint⟩ := hjadm
  obtain ⟨U, hU, hUne⟩ := hHne
  obtain ⟨A, Vbase, hAopen, hVbopen, h0A, hy0Vb, hsub⟩ := isOpen_prod_iff.1 hΩopen 0 y0 hmem
  obtain ⟨R, hRpos, hRA⟩ := Metric.isOpen_iff.1 hAopen 0 h0A
  obtain ⟨U₀, hU₀sub, hU₀open, hy0U₀⟩ := _root_.mem_nhds_iff.1 hU
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.1 (hVbopen.inter hU₀open) y0 ⟨hy0Vb, hy0U₀⟩
  set V₀ := Metric.ball y0 δ with hV₀
  have hV₀open : IsOpen V₀ := Metric.isOpen_ball
  have hV₀fin : volume V₀ ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hV₀Vb : V₀ ⊆ Vbase := fun z hz => (hδsub hz).1
  have hV₀U : V₀ ⊆ U := fun z hz => hU₀sub (hδsub hz).2
  set R2 := R / 2 with hR2
  have hR2pos : 0 < R2 := by positivity
  have hIccA : Icc (-R2) R2 ⊆ A := by
    intro x hx; apply hRA; rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    simp only [mem_Icc] at hx
    have : |x| ≤ R2 := abs_le.2 ⟨hx.1, hx.2⟩
    linarith [this, (by linarith : R2 < R)]
  have hjrect : IntegrableOn (fun p : ℝ × Y => |p.1 ^ 2 + H p.2| ^ (-c) * (1 : ℝ))
      ((Icc (-R2) R2) ×ˢ V₀) volume :=
    hint.mono_set (fun p hp => hsub ⟨hIccA hp.1, hV₀Vb hp.2⟩)
  set Vlo := V₀ ∩ {z | H z ≤ R2 ^ 2} with hVlo
  set Vhi := V₀ ∩ {z | R2 ^ 2 < H z} with hVhi
  have hVlomeas : MeasurableSet Vlo :=
    hV₀open.measurableSet.inter (measurableSet_le hHmeas measurable_const)
  have hVhimeas : MeasurableSet Vhi :=
    hV₀open.measurableSet.inter (measurableSet_lt measurable_const hHmeas)
  have hHneVlo : ∀ᵐ z ∂(volume.restrict Vlo), H z ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun z hz => hV₀U hz.1) hUne
  have hcore_lo : IntegrableOn (fun z => |H z| ^ (-(c - 1 / 2))) Vlo volume :=
    core_int_of_joint_int H hH hHmeas c R2 hc hR2pos Vlo hVlomeas hHneVlo (fun z hz => hz.2)
      (hjrect.mono_set (Set.prod_mono (subset_refl _) inter_subset_left))
  have hcore_hi : IntegrableOn (fun z => |H z| ^ (-(c - 1 / 2))) Vhi volume :=
    core_int_high H hHmeas c R2 hc hR2pos Vhi hVhimeas
      ((measure_mono inter_subset_left).trans_lt hV₀fin.lt_top).ne (fun z hz => hz.2)
  have hVunion : V₀ = Vlo ∪ Vhi := by
    ext z; simp only [hVlo, hVhi, mem_inter_iff, mem_union, mem_setOf_eq]
    constructor
    · intro hz; rcases le_or_gt (H z) (R2 ^ 2) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  exact ⟨V₀, hV₀open, Metric.mem_ball_self hδpos, hVunion ▸ hcore_lo.union hcore_hi⟩

/-- **The threshold-lift, `≤` direction.** `rlctAtOn (x² + H) (0, y0) ≤ ½ + rlctAtOn H y0`. By
`sSup_le`: a joint-admissible `c'` with `c' ≤ 1/2` is trivially `≤ ½ + λ_H`; for `c' > 1/2`,
`core_adm_of_joint_adm` gives core-admissibility at `c' − 1/2`, so `(c' − 1/2) ≤ λ_H` (`le_sSup`),
hence `c' = ½ + (c' − 1/2) ≤ ½ + λ_H`. -/
theorem step_rlct_le {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [OpensMeasurableSpace Y]
    (H : Y → ℝ) (y0 : Y) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H)
    (hHne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), H z ≠ 0) :
    rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) ≤ (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 := by
  rw [show rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0)
      = sSup { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ ∃ Ω : Set (ℝ × Y), IsOpen Ω ∧
          {((0 : ℝ), y0)} ⊆ Ω ∧
          IntegrableOn (fun w => |w.1 ^ 2 + H w.2| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w) Ω volume }
      from rfl]
  apply sSup_le
  rintro c ⟨c', rfl, Ω, hΩopen, hmem, hint⟩
  by_cases hc12 : (c' : ℝ) ≤ 1 / 2
  · apply le_trans _ le_self_add
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe]
    push_cast; linarith
  · push_neg at hc12
    obtain ⟨Ωc, hΩcopen, hy0c, hcint⟩ :=
      core_adm_of_joint_adm H hH hHmeas y0 hHne (c' : ℝ) hc12
        ⟨Ω, hΩopen, by simpa using hmem, hint⟩
    set bN := ((c' : ℝ) - 1 / 2).toNNReal with hbN
    have hbNcoe : (bN : ℝ) = (c' : ℝ) - 1 / 2 := Real.coe_toNNReal _ (by linarith)
    have hble : (bN : ℝ≥0∞) ≤ rlctAtOn H y0 := by
      unfold rlctAtOn weightedThreshold
      apply le_sSup
      refine ⟨bN, rfl, Ωc, hΩcopen, by simpa using hy0c, ?_⟩
      rw [hbNcoe]; simpa using hcint
    have hsum : (c' : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) + (bN : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp, ← ENNReal.coe_add]
      congr 1
      apply NNReal.coe_injective; push_cast [hbNcoe]; ring
    rw [hsum]; gcongr

/-- **The smooth-block Fubini RLCT lemma, `n = 1`** (`step_rlct`). Adding the coordinate `x²`
to a measurable, a.e.-nonvanishing core `H` shifts the RLCT by exactly `1/2`:
`rlctAtOn (x² + H) (0, y0) = 1/2 + rlctAtOn H y0`. The `le_antisymm` of the integrability (`≥`) and
cusp (`≤`) directions. Iterating over the `n` regular coordinates yields the general `n/2` shift
(`Skeleton.rlct_additive_smooth_block`). Axiom-clean; the `hHne` hygiene hypothesis (the 13th
fidelity fix) rules out the germ-vanishing counterexample. -/
theorem step_rlct {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [OpensMeasurableSpace Y]
    (H : Y → ℝ) (y0 : Y) (hH : ∀ z, 0 ≤ H z) (hHmeas : Measurable H)
    (hHne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), H z ≠ 0) :
    rlctAtOn (fun p : ℝ × Y => p.1 ^ 2 + H p.2) (0, y0) = (1 / 2 : ℝ≥0∞) + rlctAtOn H y0 :=
  le_antisymm (step_rlct_le H y0 hH hHmeas hHne) (step_rlct_ge H y0 hH hHmeas hHne)

/-! ## The general-`n` smooth-block Fubini lemma (the S1.5 deliverable)

Iterate `step_rlct` over the `n` regular coordinates via the `Fin`-peeling chart `chartN`: each step
transports along `chartN m Y` (measure-preserving, `rlctAtOn_comp_homeomorph`), peels one `xᵢ²` off
sum (`Fin.sum_univ_succ`), and applies the `n = 1` shift `step_rlct` to the intermediate core
`∑_{<m} xᵢ² + G²` (whose a.e.-nonvanishing `hHne_sumSq` follows from `hGne` since `∑+G² ≥ G²`).
base case `n = 0` collapses the empty regular block via the singleton chart `(Fin 0 → ℝ) × Y ≃ₜ Y`.
Result: `rlctAtOn (∑ᵢ xᵢ² + G²) (0, y0) = n/2 + rlctAtOn (G²) y0` — the S1.5 wire-in target. -/

section Iterate
variable {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]

instance instProbFin0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℝ)) :=
  ⟨by rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      Measure.pi_univ]; simp⟩

private theorem chartN_symm_app (n : ℕ) (a : ℝ) (f : Fin n → ℝ) (y : Y) :
    (chartN n Y).symm (a, (f, y)) = (Fin.cons a f, y) := by
  have h : (chartN n Y).symm (a, (f, y)) = ((finPeel n).symm (a, f), y) := rfl
  rw [h]; congr 1
  show (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0:Fin (n+1))).symm (a, f) = Fin.cons a f
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact Fin.insertNth_zero' a f

private theorem chartN_at_zero (n : ℕ) (y0 : Y) : (chartN n Y) (0, y0) = (0, (0, y0)) := by
  apply (chartN n Y).symm.injective
  rw [Homeomorph.symm_apply_apply, chartN_symm_app]
  congr 1; funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rw [Fin.cons_zero]; rfl
  · rw [Fin.cons_succ]; rfl

private theorem hHne_sumSq (m : ℕ) (G : Y → ℝ) (y0 : Y)
    (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0) :
    ∃ U ∈ 𝓝 ((0:Fin m → ℝ), y0), ∀ᵐ z ∂(volume.restrict U),
      ((∑ i, ((z:(Fin m→ℝ)×Y).1) i ^ 2) + G z.2 ^ 2) ≠ 0 := by
  obtain ⟨Ug, hUg, hGae⟩ := hGne
  refine ⟨Set.univ ×ˢ Ug, prod_mem_nhds Filter.univ_mem hUg, ?_⟩
  have hsnd : ∀ᵐ z ∂(volume.restrict (Set.univ ×ˢ Ug : Set ((Fin m→ℝ)×Y))), G z.2 ≠ 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.quasiMeasurePreserving_snd
      (μ := (volume:Measure (Fin m→ℝ)).restrict univ)
      (ν := (volume:Measure Y).restrict Ug)).tendsto_ae.eventually hGae
  filter_upwards [hsnd] with z hz
  have h1 : 0 < G z.2 ^ 2 := by positivity
  have h2 : 0 ≤ ∑ i, (z.1) i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  positivity

theorem rlct_additive_smooth_block_aux (G : Y → ℝ) (y0 : Y) (hGmeas : Measurable G)
    (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0) (n : ℕ) :
    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
      = (n : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) y0 := by
  induction n with
  | zero =>
    have hrhs : (↑(0:ℕ) : ℝ≥0∞) / 2 + rlctAtOn (fun y => G y ^ 2) y0
        = rlctAtOn (fun y => G y ^ 2) y0 := by simp
    rw [hrhs]
    set e : Y ≃ₜ ((Fin 0 → ℝ) × Y) := (Homeomorph.uniqueProd (Fin 0 → ℝ) Y).symm with he
    have hfwd : MeasurePreserving (Homeomorph.uniqueProd (Fin 0 → ℝ) Y) (volume) (volume) := by
      have hsnd : MeasurePreserving (Prod.snd : (Fin 0 → ℝ) × Y → Y) (volume) (volume) := by
        rw [Measure.volume_eq_prod]; exact measurePreserving_snd
      rw [show (Homeomorph.uniqueProd (Fin 0 → ℝ) Y : ((Fin 0→ℝ)×Y) → Y) = Prod.snd from rfl]
      exact hsnd
    have hMP : MeasurePreserving e :=
      MeasurePreserving.symm (Homeomorph.uniqueProd (Fin 0 → ℝ) Y).toMeasurableEquiv hfwd
    have hkey := rlctAtOn_comp_homeomorph e hMP e.measurableEmbedding
      (fun p : (Fin 0 → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) y0
    rw [show ((0:Fin 0→ℝ), y0) = e y0 from
          Prod.ext (Subsingleton.elim _ _) rfl, ← hkey]
    congr 1
    funext y
    show (∑ i : Fin 0, ((e y).1) i ^ 2) + G ((e y).2) ^ 2 = G y ^ 2
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    rfl
  | succ m ih =>
    have hMP : MeasurePreserving (chartN m Y).symm :=
      MeasurePreserving.symm (chartN m Y).toMeasurableEquiv (chartN_mp m)
    have hkey := rlctAtOn_comp_homeomorph (chartN m Y).symm hMP
      (chartN m Y).symm.measurableEmbedding
      (fun p : (Fin (m+1) → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, (0, y0))
    rw [show ((0:Fin (m+1)→ℝ), y0) = (chartN m Y).symm (0, (0, y0)) from by
          rw [← chartN_at_zero m y0, Homeomorph.symm_apply_apply], ← hkey]
    have hcomp : (fun q : ℝ × ((Fin m → ℝ) × Y) =>
          (∑ i, ((chartN m Y).symm q).1 i ^ 2) + G ((chartN m Y).symm q).2 ^ 2)
        = (fun q : ℝ × ((Fin m → ℝ) × Y) => q.1^2 + ((∑ i, q.2.1 i ^ 2) + G q.2.2 ^ 2)) := by
      funext q; obtain ⟨a, f, y⟩ := q
      rw [chartN_symm_app]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]; ring
    rw [hcomp, step_rlct (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0)
      (fun p => by positivity) (by fun_prop) (hHne_sumSq m G y0 hGne), ih, ← add_assoc]
    congr 1
    rw [← ENNReal.add_div]; congr 1; push_cast; ring

end Iterate

end DLNFibre.DLN.RLCT
