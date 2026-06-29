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
  sorry

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
  sorry

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
