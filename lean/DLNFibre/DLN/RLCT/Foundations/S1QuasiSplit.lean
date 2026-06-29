import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit` — the constant-rank QUASI-splitting RLCT lower bound

The analytic gate for the D1 one-sided obligation (★)
`rlctAt(loss) v ≥ nReg/2 + rlctAtOn(core)(v−core)` (`Validate.DeepestMinRlct`, the
`deepest_le_of_optimal_via_L2_ge` consumer). Mathlib v4.29 has the `C^r` inverse function theorem
but **no** Morse / Morse–Bott / Gromoll–Meyer / constant-rank quadratic-split lemma. This module
supplies the **weaker thing the one-sided bound actually needs** — NOT the full splitting form.

## The route (decorrelated Codex xhigh, 2026-06-29): QUASI-split by constant comparison

For the loss `f = ∑_k g_k²` with a critical point at `v` and a positive-definite `m`-block on `m`
independent gradients `∇g_1(v),…,∇g_m(v)` (`m = nReg`): the `C^r` IFT change of coordinates
`Ψ(w) = (g_1(w)−g_1(v), …, g_m(w)−g_m(v), P(w))` (`P` a complementary projection) is a local diffeo
at `v` (its derivative is invertible — top rows the independent gradients, bottom rows the
complement). In the chart `u = (s, t) ∈ ℝ^m × ℝ^{N−m}`, the `m` active functions become
`g_k(Φ⁻¹(s,t)) = s_k + g_k(v)` EXACTLY, and (the active constraints vanishing at the optimal `v`,
`g_k(v) = 0`):

    f(Φ⁻¹(s,t)) = ∑_{k<m} s_k² + ∑_α q_α(s,t)²    (inactive squares `q_α`, still coupled to `s`).

The naive decoupling `∑ s² + ∑ q(0,t)² ≤ f` is **FALSE** (Codex counterexample `s² + (s+t²)²` at
`s = −t²/2`). The fix is a **CONSTANT comparison**, not a pointwise one: `q` is `C¹`, so locally
`‖q(s,t) − q(0,t)‖ ≤ L‖s‖`, whence the **slice residual** `R(t) = ∑_α q_α(0,t)²` and
`G(s,t) = ∑_{k<m} s_k² + R(t)` satisfy `G(s,t) ≤ C · f(Φ⁻¹(s,t))` near the origin for a positive
constant `C`. Then:

  * `rlctAtOn G ≤ rlctAtOn (f∘Φ⁻¹)`        [`rlctAtOn_mono` + constant-scale invariance]
  * `m/2 + rlctAtOn R 0 ≤ rlctAtOn G`      [iterate `step_rlct_ge` over the `m` regular coords]
  * `rlctAtOn (f∘Φ⁻¹) v = rlctAtOn f v`    [`rlctAtOn_boundedUnit_localHomeomorph`, the IFT chart]

giving (★): `m/2 + rlctAtOn R 0 ≤ rlctAtOn f v`. The residual core `R = ∑ q_α(0,·)²` is the
`v−core` term the D1 bridge compares via CORE-P1.

## Layering (matches the existing S1 engine)
- `rlct_smooth_block_ge` — ABSTRACT iterated `≥` over `m` regular coords with a GENERAL residual `R`
  (the `≥`-only, general-residual companion of `rlct_additive_smooth_block`'s sum-of-squares
  EQUALITY).
- `coupled_controls_slice` — the PURE quasi-splitting inequality
  `∑s² + b² ≤ C(∑s² + a²)` from the squared local Lipschitz bound `(a−b)² ≤ L²·∑s²`.
- `rlct_quasiSplit_ge` — the ABSTRACT post-chart lower bound (consumes the two above + the form
  `f∘Φ⁻¹ = ∑s² + Q`); the chart transfer is the banked `rlctAtOn_boundedUnit_localHomeomorph`.

All three are network-free real analysis (high value beyond D1); the IFT-chart producer (the
`g_k`→chart step, application-specific) lives at the D1 use site.

STATUS: SKELETON (signatures validated; sub-lemmas `sorry`). Built incrementally below.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

/-! ## The iterated `≥` over the regular block, general residual

`rlct_additive_smooth_block` gives the EQUALITY `n/2 + λ(G²)` but only for a residual of the special
form `G(t)²`. The one-sided route needs the iterated `≥` for a GENERAL nonneg residual `R(t)` —
exactly `m`-fold `step_rlct_ge` (an inequality atom valid for any a.e.-nonzero core), bypassing
the cusp `≤` half. Same `chartN`/`finPeel` peel as `rlct_additive_smooth_block_aux`. -/

section Iterate
variable {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]

/-- `(chartN m Y).symm (a, (f, y)) = (Fin.cons a f, y)` (re-derived; the S1Fubini twin is private). -/
private theorem qs_chartN_symm_app (m : ℕ) (a : ℝ) (f : Fin m → ℝ) (y : Y) :
    (chartN m Y).symm (a, (f, y)) = (Fin.cons a f, y) := by
  have h : (chartN m Y).symm (a, (f, y)) = ((finPeel m).symm (a, f), y) := rfl
  rw [h]; congr 1
  show (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (m + 1))).symm (a, f) = Fin.cons a f
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact Fin.insertNth_zero' a f

/-- `(chartN m Y) (0, y0) = (0, (0, y0))` (re-derived; the S1Fubini twin is private). -/
private theorem qs_chartN_at_zero (m : ℕ) (y0 : Y) : (chartN m Y) (0, y0) = (0, (0, y0)) := by
  apply (chartN m Y).symm.injective
  rw [Homeomorph.symm_apply_apply, qs_chartN_symm_app]
  congr 1; funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rw [Fin.cons_zero]; rfl
  · rw [Fin.cons_succ]; rfl

/-- The intermediate core `H_m(p) = (∑_{i<m} p.1 i²) + R p.2` is a.e.-nonzero near `(0, y0)` (since
`∑ + R ≥ R > 0` a.e.). The `≥`-route analog of S1Fubini's private `hHne_sumSq`. -/
private theorem qs_hHne_block (m : ℕ) (R : Y → ℝ) (y0 : Y) (hR : ∀ z, 0 ≤ R z)
    (hRne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0) :
    ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), y0), ∀ᵐ z ∂(volume.restrict U),
      ((∑ i, ((z : (Fin m → ℝ) × Y).1) i ^ 2) + R z.2) ≠ 0 := by
  obtain ⟨Ug, hUg, hRae⟩ := hRne
  refine ⟨Set.univ ×ˢ Ug, prod_mem_nhds Filter.univ_mem hUg, ?_⟩
  have hsnd : ∀ᵐ z ∂(volume.restrict (Set.univ ×ˢ Ug : Set ((Fin m → ℝ) × Y))), R z.2 ≠ 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Fin m → ℝ)).restrict univ)
      (ν := (volume : Measure Y).restrict Ug)).tendsto_ae.eventually hRae
  filter_upwards [hsnd] with z hz
  have h1 : 0 < R z.2 := lt_of_le_of_ne (hR z.2) (Ne.symm hz)
  have h2 : 0 ≤ ∑ i, (z.1) i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  positivity

/-- **The iterated regular-block RLCT LOWER bound** (general residual). For a measurable,
a.e.-nonzero residual `R : Y → ℝ` with `R ≥ 0`, adding the regular block `∑_{i<m} x_i²` lowers the
RLCT by at least `m/2`:

    (m : ℝ≥0∞)/2 + rlctAtOn R y0
      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, y0).

`m`-fold `step_rlct_ge` along the `chartN`/`finPeel` peel (the `≥` half of `step_rlct`; no cusp).
The a.e.-nonzero side condition propagates as in `hHne_sumSq` (the partial-sum core `∑ + R ≥ R`). -/
theorem rlct_smooth_block_ge (R : Y → ℝ) (y0 : Y) (hR : ∀ z, 0 ≤ R z) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0) (m : ℕ) :
    (m : ℝ≥0∞) / 2 + rlctAtOn R y0
      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, y0) := by
  induction m with
  | zero =>
    -- `0/2 + λ R = λ R`, and `(fun p:(Fin 0→ℝ)×Y => 0 + R p.2)` transports to `R` by the singleton chart.
    have hrhs : (↑(0 : ℕ) : ℝ≥0∞) / 2 + rlctAtOn R y0 = rlctAtOn R y0 := by simp
    rw [hrhs]
    set e : Y ≃ₜ ((Fin 0 → ℝ) × Y) := (Homeomorph.uniqueProd (Fin 0 → ℝ) Y).symm with he
    have hfwd : MeasurePreserving (Homeomorph.uniqueProd (Fin 0 → ℝ) Y) (volume) (volume) := by
      have hsnd : MeasurePreserving (Prod.snd : (Fin 0 → ℝ) × Y → Y) (volume) (volume) := by
        rw [Measure.volume_eq_prod]; exact measurePreserving_snd
      rw [show (Homeomorph.uniqueProd (Fin 0 → ℝ) Y : ((Fin 0 → ℝ) × Y) → Y) = Prod.snd from rfl]
      exact hsnd
    have hMP : MeasurePreserving e :=
      MeasurePreserving.symm (Homeomorph.uniqueProd (Fin 0 → ℝ) Y).toMeasurableEquiv hfwd
    have hkey := rlctAtOn_comp_homeomorph e hMP e.measurableEmbedding
      (fun p : (Fin 0 → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) y0
    rw [show ((0 : Fin 0 → ℝ), y0) = e y0 from Prod.ext (Subsingleton.elim _ _) rfl, ← hkey]
    apply le_of_eq
    congr 1
    funext y
    show R y = (∑ i : Fin 0, ((e y).1) i ^ 2) + R ((e y).2)
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    rfl
  | succ k ih =>
    -- peel one coordinate via `chartN`, then `step_rlct_ge` against the `m=k` block core.
    have hMP : MeasurePreserving (chartN k Y).symm :=
      MeasurePreserving.symm (chartN k Y).toMeasurableEquiv (chartN_mp k)
    have hkey := rlctAtOn_comp_homeomorph (chartN k Y).symm hMP
      (chartN k Y).symm.measurableEmbedding
      (fun p : (Fin (k + 1) → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, (0, y0))
    rw [show ((0 : Fin (k + 1) → ℝ), y0) = (chartN k Y).symm (0, (0, y0)) from by
          rw [← qs_chartN_at_zero k y0, Homeomorph.symm_apply_apply], ← hkey]
    -- rewrite the transported core into the peeled `q.1² + (block core)` form.
    have hcomp : (fun q : ℝ × ((Fin k → ℝ) × Y) =>
          (∑ i, ((chartN k Y).symm q).1 i ^ 2) + R ((chartN k Y).symm q).2)
        = (fun q : ℝ × ((Fin k → ℝ) × Y) => q.1 ^ 2 + ((∑ i, q.2.1 i ^ 2) + R q.2.2)) := by
      funext q; obtain ⟨a, f, y⟩ := q
      rw [qs_chartN_symm_app]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]; ring
    rw [hcomp]
    -- `step_rlct_ge` for the `m=k` block core `H`; then IH.
    have hstep := step_rlct_ge (fun p : (Fin k → ℝ) × Y => (∑ i, p.1 i ^ 2) + R p.2) (0, y0)
      (fun p => by have := hR p.2; positivity) (by fun_prop) (qs_hHne_block k R y0 hR hRne)
    refine le_trans ?_ hstep
    -- `(k+1)/2 + λR = 1/2 + (k/2 + λR) ≤ 1/2 + λ(block core)` by IH.
    have hsplit : ((k + 1 : ℕ) : ℝ≥0∞) / 2 + rlctAtOn R y0
        = (1 / 2 : ℝ≥0∞) + ((k : ℝ≥0∞) / 2 + rlctAtOn R y0) := by
      rw [← add_assoc]; congr 1; rw [← ENNReal.add_div]; congr 1; push_cast; ring
    rw [hsplit]
    gcongr

end Iterate

/-! ## The pure quasi-splitting inequality

The constant comparison that replaces the false pointwise decoupling. From a (squared) local
Lipschitz bound on the coupled inactive part `q`, the decoupled slice square `b²` is controlled by a
constant times the coupled energy. Pure inequality (`nlinarith`), no measure theory, no RLCT. -/

/-- **The quasi-splitting constant comparison** (pure inequality, one inactive square). With one
coupled inactive component `a = q (s,t)` and its slice value `b = q (0,t)` satisfying the squared
local Lipschitz bound `(a − b)² ≤ L² · (∑ s²)`, the decoupled slice square is dominated by a
constant multiple of the coupled energy:

    (∑ i, s i ^ 2) + b² ≤ (2 L² + 2) · ((∑ i, s i ^ 2) + a²).

(`b² ≤ 2(a−b)² + 2a² ≤ 2L²·(∑s²) + 2a²`, then `(∑s²) + b² ≤ (2L²+1)(∑s²) + 2a² ≤ (2L²+2)(∑s²+a²)`.)
Single-square form; the producer sums it over the inactive index set and supplies `L` from the
mean-value bound on `q` (`Convex.norm_image_sub_le_of_norm_fderiv_le`). -/
theorem coupled_controls_slice {m : ℕ} (a b L : ℝ) (s : Fin m → ℝ) (hL : 0 ≤ L)
    (hlip : (a - b) ^ 2 ≤ L ^ 2 * (∑ i, s i ^ 2)) :
    (∑ i, s i ^ 2) + b ^ 2 ≤ (2 * L ^ 2 + 2) * ((∑ i, s i ^ 2) + a ^ 2) := by
  set ssq := ∑ i, s i ^ 2 with hssq
  have hssq0 : 0 ≤ ssq := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg _
  -- `b² ≤ 2(a−b)² + 2a²`, so `b² ≤ 2 L² ssq + 2 a²`.
  -- `2(a−b)² + 2a² − b² = (2a − b)² ≥ 0`, and `(a−b)² ≤ L² ssq`.
  have hb2 : b ^ 2 ≤ 2 * L ^ 2 * ssq + 2 * a ^ 2 := by nlinarith [hlip, sq_nonneg (2 * a - b)]
  -- RHS − (ssq + b²) ≥ ssq + 2 L² a² ≥ 0, using `hb2`. Expand the product explicitly.
  have hexp : (2 * L ^ 2 + 2) * (ssq + a ^ 2)
      = 2 * L ^ 2 * ssq + 2 * a ^ 2 + (ssq + 2 * L ^ 2 * a ^ 2) + ssq := by ring
  rw [hexp]
  have h1 : 0 ≤ ssq + 2 * L ^ 2 * a ^ 2 :=
    add_nonneg hssq0 (by positivity)
  linarith [hb2, hssq0, h1]

/-! ## The abstract post-chart quasi-split lower bound

Consumes the post-chart form `F = ∑s² + Q` plus the constant comparison; concludes the `m/2`-shifted
lower bound on `F` at the origin. The chart-transfer back to `f` at `v` is the banked
`rlctAtOn_boundedUnit_localHomeomorph` (applied at the D1 use site). -/

/-- **The abstract quasi-split RLCT lower bound** (post-chart). Let `F : (Fin m → ℝ) × Y → ℝ` be the
chart form `F (s,t) = (∑ i, s i²) + Q (s,t)` with `Q ≥ 0` measurable, and let the **slice residual**
`R (t) = Q (0,t)` (the inactive energy at `s = 0`) satisfy:
  (i) `R ≥ 0`, measurable, a.e.-nonzero near `t0` (`hRne`);
  (ii) the constant comparison `(∑ s²) + R t ≤ C · F (s,t)` for `(s,t)` near `(0,t0)`, `C > 0`.
Then `m/2 + rlctAtOn R t0 ≤ rlctAtOn F (0,t0)`. (`C⁻¹·G ≤ F` ⟹ `rlctAtOn G ≤ rlctAtOn F` by
`rlctAtOn_mono` + constant-scale invariance, with `G = ∑s² + R`; then `rlct_smooth_block_ge`.) -/
theorem rlct_quasiSplit_ge {m : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    (F : (Fin m → ℝ) × Y → ℝ) (Q : (Fin m → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hQmeas : Measurable Q) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ C * F p) :
    (m : ℝ≥0∞) / 2 + rlctAtOn R t0 ≤ rlctAtOn F ((0 : Fin m → ℝ), t0) := by
  sorry

end DLNFibre.DLN.RLCT
