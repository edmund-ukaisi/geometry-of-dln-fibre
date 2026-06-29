import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1IFTProducer` — the selected-square IFT-chart PRODUCER

The network-free real-analysis lemma the D1 (★) `≥`-leg rests on (spec §SEL, the LIGHTER
existing-engine route). It CONSTRUCTS the inputs of the banked engine `rlct_quasiSplit_ge` from a
clean premise — a smooth loss `f = ∑_k g_k²` near a zero `v` together with a selected family of `m`
of the `g_k` whose chart-straightening realises the `m` regular coordinates — rather than positing.

## What it lands (the bedrock)

`rlct_quasiSplit_ge` consumes `F = ∑s² + Q`, `Q ≥ 0`, `R = Q(0,·)`, and the constant comparison
`hcmp : ∑s² + R ≤ C·F`. This module builds those FROM a chart `Ψ` (an `OpenPartialHomeomorph` on the
flat slice `(Fin m → ℝ) × Y`) whose first `m` coordinates pull back the selected `g_k` (the IFT
straightening), plus the residual `q : (Fin n → ℝ)`-valued family of the inactive `g`. The two
genuine analytic facts are:

  * **the post-chart form** `F(s,t) = ∑_{k<m} s_k² + Q(s,t)` with `Q = ‖q(s,t)‖²` (a sum of squares,
    so `Q ≥ 0` GLOBALLY by definition — `F`, `Q` are DEFINED this way, not posited), and on the
    image `F = f ∘ Ψ.symm` (the chart transfer's local identity);
  * **the constant comparison** `hcmp`, via the cleaner **vector triangle** (decorrelated Codex,
    spec §SEL): a single mean-value Lipschitz bound `‖q(s,t) − q(0,t)‖ ≤ L·‖s‖` on a ball gives
    `R = ‖q(0,t)‖² ≤ 2‖q(s,t)‖² + 2L²‖s‖² = 2Q + 2L²‖s‖² ≤ 2Q + 2L²∑s²`, whence
    `∑s² + R ≤ max(1+2L², 2)·(∑s² + Q)`. (NOT a per-square `coupled_controls_slice` sum — the vector
    triangle avoids the `n·∑s²` factor that route incurs.)

The chart `Ψ` itself is the C^r IFT `ContDiffAt.toOpenPartialHomeomorph`; this module takes its raw
data (the source/inverse identities + the bounded-unit Jacobian) and CONSTRUCTS the engine inputs,
landing `m/2 + rlctAtOn R t0 ≤ rlctAt f v` — exactly the D1 `hAtV` shape.

STATUS: built sorry-free, axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

/-! ## Two real-analysis helpers (network-free, no RLCT) -/

/-- For the sup-normed `Fin m → ℝ`, the squared norm is dominated by the sum of squares:
`‖s‖² ≤ ∑ i, s i²`. (The sup `‖s‖ = max_i |s i|` is attained at some `j`, and `s j² ≤ ∑ s²`.) The
`m = 0` case is `0 ≤ 0`. This converts the mean-value `L²‖s‖²` bound into the `L²·∑s²` shape the
engine's `R ≤ 2Q + 2L²·∑s²` comparison uses. -/
theorem sq_norm_le_sum_sq {m : ℕ} (s : Fin m → ℝ) : ‖s‖ ^ 2 ≤ ∑ i, s i ^ 2 := by
  rcases isEmpty_or_nonempty (Fin m) with hempty | hne
  · -- `m = 0`: `‖s‖ = 0`, `∑ = 0`.
    have : s = 0 := Subsingleton.elim _ _
    simp [this]
  · -- pick `j` attaining the sup; then `‖s‖² = s j² ≤ ∑ s²`.
    obtain ⟨j, hj⟩ := Finite.exists_max (fun i => |s i|)
    have hnorm : ‖s‖ = |s j| := by
      apply le_antisymm
      · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
        intro i; rw [Real.norm_eq_abs]; exact hj i
      · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm s j
    rw [hnorm, sq_abs]
    exact Finset.single_le_sum (f := fun i => s i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/-- **The slice comparison from one vector Lipschitz bound** (the §SEL vector triangle). For a
residual vector `q : Fin n → ℝ` at the coupled point and `b : Fin n → ℝ` at the slice (`s = 0`),
with the Lipschitz gap `∑ i, (q i − b i)² ≤ L²·∑ s²`, the decoupled slice energy is dominated by a
constant multiple of the coupled energy:

    (∑ i, s i²) + (∑ i, b i²) ≤ (2·L² + 2)·((∑ i, s i²) + (∑ i, q i²)).

(`∑ b² ≤ 2∑(q−b)² + 2∑q² ≤ 2L²∑s² + 2∑q²`, then `(∑s²)+∑b² ≤ (1+2L²)∑s² + 2∑q² ≤ (2L²+2)(∑s²+∑q²)`.)
The aggregate of `coupled_controls_slice` over the inactive index, from a single vector bound — no
`n·∑s²` factor. -/
theorem slice_le_of_lipschitz {m n : ℕ} (s : Fin m → ℝ) (q b : Fin n → ℝ) (L : ℝ)
    (hlip : ∑ i, (q i - b i) ^ 2 ≤ L ^ 2 * (∑ j, s j ^ 2)) :
    (∑ j, s j ^ 2) + (∑ i, b i ^ 2)
      ≤ (2 * L ^ 2 + 2) * ((∑ j, s j ^ 2) + (∑ i, q i ^ 2)) := by
  set ssq := ∑ j, s j ^ 2 with hssq
  have hssq0 : 0 ≤ ssq := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg _
  -- `∑ b² ≤ 2 ∑(q−b)² + 2 ∑ q²` (per-index `b² ≤ 2(q−b)² + 2q²`, summed).
  have hb2 : ∑ i, b i ^ 2 ≤ 2 * (∑ i, (q i - b i) ^ 2) + 2 * (∑ i, q i ^ 2) := by
    have hsumrhs : 2 * (∑ i, (q i - b i) ^ 2) + 2 * (∑ i, q i ^ 2)
        = ∑ i, (2 * (q i - b i) ^ 2 + 2 * q i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsumrhs]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (2 * q i - b i)]
  -- chain through the Lipschitz bound.
  have hqsq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [hb2, hlip, hssq0, hqsq0, hL2,
    mul_nonneg hL2 hssq0]

/-! ## The constant-comparison producer — `hcmp` from a `C¹` residual vector

The genuinely-new analytic content over the banked `rlct_quasiSplit_ge`: it CONSTRUCTS the `hcmp`
existential from the smoothness of the residual `q`, via the mean-value theorem. The slice
`R = Q(0,·)` and the coupled `Q = ‖q‖²` are sums of squares, so `Q ≥ 0` is automatic; the only work
is the constant comparison, and the §SEL vector triangle gives it from a single Lipschitz bound. -/

/-- **`hcmp` from a `C¹` residual** (the constant-comparison producer). For a `C¹` residual vector
`q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)` (the inactive `g`'s composed with the chart), with
coupled energy `Q p = ‖q p‖²` and slice residual `R t = ‖q (0,t)‖²`, the post-chart loss
`F p = (∑ s²) + Q p` satisfies the constant comparison near `(0,t0)`:

    ∃ C > 0, ∃ U ∈ 𝓝 ((0:Fin m→ℝ), t0), ∀ p ∈ U, (∑ p.1 i²) + R p.2 ≤ C · F p.

The mean-value theorem (`Convex.norm_image_sub_le_of_norm_fderiv_le`) on the unit ball bounds
`‖q (s,t) − q (0,t)‖ ≤ L·‖(s,0)‖ = L·‖s‖` (`L =` sup of `‖fderiv q‖` on the ball); squaring +
`EuclideanSpace.real_norm_sq_eq` + `sq_norm_le_sum_sq` gives `∑ (q(s,t)−q(0,t))² ≤ L²·∑ s²`, fed to
`slice_le_of_lipschitz` (the vector triangle), `C = 2L²+2`. -/
theorem hcmp_of_contDiff {m n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y) :
    ∃ C : ℝ, 0 < C ∧ ∃ U ∈ 𝓝 ((0 : Fin m → ℝ), t0), ∀ p ∈ U,
      (∑ i, p.1 i ^ 2) + (∑ i, q ((0 : Fin m → ℝ), p.2) i ^ 2)
        ≤ C * ((∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) := by
  classical
  -- the compact unit ball around the chart-origin
  set w0 : (Fin m → ℝ) × Y := ((0 : Fin m → ℝ), t0) with hw0
  set B : Set ((Fin m → ℝ) × Y) := Metric.closedBall w0 1 with hB
  have hBconvex : Convex ℝ B := convex_closedBall _ _
  have hBcompact : IsCompact B := isCompact_closedBall _ _
  -- `q` is differentiable; `‖fderiv q‖` is continuous, so bounded on the compact `B`.
  have hqdiff : Differentiable ℝ q := hq.differentiable one_ne_zero
  have hfderivcont : Continuous fun w => ‖fderiv ℝ q w‖ :=
    (hq.continuous_fderiv one_ne_zero).norm
  obtain ⟨L, hLmem, hLmax⟩ := hBcompact.exists_isMaxOn ⟨w0, Metric.mem_closedBall_self zero_le_one⟩
    hfderivcont.continuousOn
  -- `L = ‖fderiv q L_pt‖ ≥ 0` is the uniform bound on `B`.
  set Lval : ℝ := ‖fderiv ℝ q L‖ with hLval
  have hLval0 : 0 ≤ Lval := norm_nonneg _
  have hbound : ∀ w ∈ B, ‖fderiv ℝ q w‖ ≤ Lval := fun w hw => hLmax hw
  -- the open unit ball is the `hcmp` neighbourhood.
  refine ⟨2 * Lval ^ 2 + 2, by positivity, Metric.ball w0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  intro p hp
  have hpB : p ∈ B := Metric.ball_subset_closedBall hp
  -- the slice point `(0, p.2)` is also in `B`: `‖(0,p.2) − w0‖ = ‖p.2 − t0‖ ≤ ‖p − w0‖ ≤ 1`.
  have hsliceB : ((0 : Fin m → ℝ), p.2) ∈ B := by
    rw [hB, Metric.mem_closedBall, dist_eq_norm]
    rw [hB, Metric.mem_closedBall, dist_eq_norm] at hpB
    refine le_trans ?_ hpB
    rw [hw0, Prod.norm_def, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, norm_zero]
    exact max_le_max (by positivity) (le_refl _)
  -- mean-value: `‖q p − q (0,p.2)‖ ≤ Lval · ‖p − (0,p.2)‖ = Lval · ‖p.1‖`.
  have hmvt : ‖q p - q ((0 : Fin m → ℝ), p.2)‖ ≤ Lval * ‖p - ((0 : Fin m → ℝ), p.2)‖ :=
    hBconvex.norm_image_sub_le_of_norm_fderiv_le (fun w _ => hqdiff w) hbound hsliceB hpB
  -- `p − (0,p.2) = (p.1, 0)`, norm `= ‖p.1‖`.
  have hdiffnorm : ‖p - ((0 : Fin m → ℝ), p.2)‖ = ‖p.1‖ := by
    rw [show p - ((0 : Fin m → ℝ), p.2) = (p.1, (0 : Y)) from by
      ext <;> simp [Prod.sub_def]]
    rw [Prod.norm_def]; simp
  rw [hdiffnorm] at hmvt
  -- square + EuclideanSpace: `∑ (q p − q(0,p.2))² ≤ Lval²·∑ p.1²`.
  have hlip : ∑ i, (q p i - q ((0 : Fin m → ℝ), p.2) i) ^ 2 ≤ Lval ^ 2 * (∑ j, p.1 j ^ 2) := by
    have hsq : ∑ i, (q p i - q ((0 : Fin m → ℝ), p.2) i) ^ 2
        = ‖q p - q ((0 : Fin m → ℝ), p.2)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _; rw [PiLp.sub_apply]
    rw [hsq]
    calc ‖q p - q ((0 : Fin m → ℝ), p.2)‖ ^ 2
        ≤ (Lval * ‖p.1‖) ^ 2 := by
          apply sq_le_sq'
          · have h1 := norm_nonneg (q p - q ((0 : Fin m → ℝ), p.2))
            have h2 := mul_nonneg hLval0 (norm_nonneg p.1)
            linarith
          · exact hmvt
      _ = Lval ^ 2 * ‖p.1‖ ^ 2 := by ring
      _ ≤ Lval ^ 2 * (∑ j, p.1 j ^ 2) := by
          apply mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq p.1) (by positivity)
  -- the vector triangle aggregate.
  exact slice_le_of_lipschitz p.1 (q p) (q ((0 : Fin m → ℝ), p.2)) Lval hlip

/-! ## The post-chart quasi-split lower bound from a `C¹` residual

Assembles `hcmp_of_contDiff` (the constant comparison, the new analytic content) with the banked
`rlct_quasiSplit_ge`: the residual `q` being `C¹` is enough to drive the whole engine — `Q = ‖q‖²`
is a sum of squares so `Q ≥ 0`, `F = ∑s² + Q` and `R = Q(0,·)` are definitional, the only side
condition left is the a.e.-nonzero `hRne` (loss-specific, taken as a hypothesis). This is the clean
producer the D1 use sites (both peels) instantiate. -/

/-- **The post-chart quasi-split bound from a `C¹` residual** (the producer). For a `C¹` residual
vector `q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)`, the post-chart loss
`F (s,t) = (∑ s²) + ‖q (s,t)‖²` with slice residual `R t = ‖q (0,t)‖²` satisfies the `m/2`-shifted
RLCT lower bound at the chart-origin, provided `R` is a.e.-nonzero near `t0` (`hRne`):

    (m : ℝ≥0∞)/2 + rlctAtOn R t0 ≤ rlctAtOn F ((0 : Fin m → ℝ), t0).

`hcmp_of_contDiff` supplies the constant comparison; `Q ≥ 0`, `hF`, `hR` are definitional (sums of
squares); measurability of `F`, `R` follows from continuity of `q` (`C¹`). The chart transfer back
to `rlctAt (loss) v` is the SEPARATE banked `rlctAtOn_boundedUnit_localHomeomorph` (use site). -/
theorem rlctAtOn_quasiSplit_ge_of_contDiff_residual {m n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    (q : (Fin m → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 q) (t0 : Y)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin m → ℝ), z) i ^ 2) ≠ 0) :
    (m : ℝ≥0∞) / 2
        + rlctAtOn (fun t : Y => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2) t0
      ≤ rlctAtOn (fun p : (Fin m → ℝ) × Y => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2))
          ((0 : Fin m → ℝ), t0) := by
  -- continuity of `q` ⟹ measurability of the sum-of-squares `F`, `R`.
  have hqcont : Continuous q := hq.continuous
  set F : (Fin m → ℝ) × Y → ℝ := fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2) with hFdef
  set Q : (Fin m → ℝ) × Y → ℝ := fun p => ∑ i, q p i ^ 2 with hQdef
  set R : Y → ℝ := fun t => ∑ i, q ((0 : Fin m → ℝ), t) i ^ 2 with hRdef
  have hqi : ∀ i, Continuous fun p : (Fin m → ℝ) × Y => q p i := fun i => by
    have hproj : Continuous fun w : EuclideanSpace ℝ (Fin n) => w i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    exact hproj.comp hqcont
  have hFmeas : Measurable F := by
    have hcont : Continuous F := by
      apply Continuous.add
      · exact continuous_finset_sum _
          (fun i _ => ((continuous_apply i).comp continuous_fst).pow 2)
      · exact continuous_finset_sum _ (fun i _ => (hqi i).pow 2)
    exact hcont.measurable
  have hRmeas : Measurable R := by
    have hcont : Continuous R := by
      apply continuous_finset_sum _ (fun i _ => ?_)
      exact ((hqi i).comp (Continuous.prodMk continuous_const continuous_id)).pow 2
    exact hcont.measurable
  -- the constant comparison from `hcmp_of_contDiff`.
  obtain ⟨C, hC, hcmp⟩ := hcmp_of_contDiff q hq t0
  -- fire the banked engine.
  exact rlct_quasiSplit_ge F Q R t0 (fun _ => rfl)
    (fun p => Finset.sum_nonneg fun i _ => sq_nonneg _)
    hFmeas (fun _ => rfl) hRmeas hRne C hC hcmp

end DLNFibre.DLN.RLCT
