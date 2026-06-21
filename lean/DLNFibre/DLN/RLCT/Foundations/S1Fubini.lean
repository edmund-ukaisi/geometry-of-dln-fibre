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
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b)
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
          cmpF _ _ a b hsx htg ha.le hb.le
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

end DLNFibre.DLN.RLCT
