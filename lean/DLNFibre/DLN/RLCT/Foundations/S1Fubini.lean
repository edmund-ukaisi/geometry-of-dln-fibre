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

end DLNFibre.DLN.RLCT
