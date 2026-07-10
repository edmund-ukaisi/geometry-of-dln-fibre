import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJRadialInt` — radial integrability over a ball

**Thread `genm-catclose`, the Cat I good-stratum load-bearing sub-lemma.** The `n`-dim radial
integrability `∫_{ball} ‖x‖^{−a} < ∞ ⟸ a < n`, which recurs at every level of the Gram–Schur
`b`-recursion for the good-stratum weight `∫_{det>0} det(Q_b Q_bᵀ)^{−a/2}` (catint cert).

The mechanism: Mathlib's coarea reduction `integrable_fun_norm_addHaar` turns the radial integral
into the 1-D weighted power `∫_{Ioi 0} y^{n−1}·f(y)`, and `integrableOn_Ioo_rpow_iff` supplies the
near-0 power test `∫_0^R y^s < ∞ ⟺ −1 < s` (here `s = (n−1) − a`, so the test is `a < n`).

S2-FREE: pure Mathlib analysis. Intended axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Radial integrability over a ball.** On `ℝ^n` (`n ≥ 1`), `x ↦ ‖x‖^{−a}` is integrable on any
ball `ball 0 R` iff `a < n` — here the `⟸` (the finiteness we need). Via the coarea reduction
`integrable_fun_norm_addHaar` to the 1-D near-0 power test `integrableOn_Ioo_rpow_iff`. -/
theorem integrableOn_norm_rpow_neg_ball {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : a < n) (R : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ (-a)) (Metric.ball 0 R) := by
  -- The trivial `R ≤ 0` case: the ball is empty.
  by_cases hR : 0 < R
  swap
  · rw [Metric.ball_eq_empty.2 (not_lt.mp hR)]; exact integrableOn_empty
  -- Nontriviality of the space from `n ≥ 1`.
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]; omega
  -- Truncated radial profile `g y = 1_{y<R} · y^{−a}`: ball-indicator of `‖·‖^{−a}` is `g ∘ ‖·‖`.
  set g : ℝ → ℝ := fun y ↦ (Iio R).indicator (fun y ↦ y ^ (-a)) y with hg
  rw [← integrable_indicator_iff measurableSet_ball]
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator
        (fun x ↦ ‖x‖ ^ (-a)) = fun x ↦ g ‖x‖ := by
    funext x
    change (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator (fun x ↦ ‖x‖ ^ (-a)) x
      = (Iio R).indicator (fun y ↦ y ^ (-a)) ‖x‖
    by_cases hx : ‖x‖ < R
    · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hx),
          Set.indicator_of_mem (mem_Iio.mpr hx)]
    · rw [Set.indicator_of_notMem (by rw [mem_ball_zero_iff]; exact hx),
          Set.indicator_of_notMem (by rw [mem_Iio]; exact hx)]
  rw [hind, integrable_fun_norm_addHaar (μ := volume)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  -- Goal: `IntegrableOn (fun y ↦ y^(n-1) * g y) (Ioi 0)`.
  -- Split `Ioi 0 = Ioo 0 R ∪ Ici R`; on `Ioo 0 R` integrand is `y^{(n-1)-a}`, on `Ici R` it is 0.
  have hsplit : Ioi (0 : ℝ) = Ioo 0 R ∪ Ici R := by
    ext y; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]; constructor
    · intro hy; rcases le_or_gt R y with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hy, h⟩
    · rintro (⟨hy, _⟩ | h)
      · exact hy
      · exact lt_of_lt_of_le hR h
  rw [hsplit, integrableOn_union]
  constructor
  · -- On `Ioo 0 R`: `y^(n-1) * g y = y^((n-1:ℝ)-a)`.
    rw [integrableOn_congr_fun (g := fun y ↦ y ^ ((n - 1 : ℕ) - a : ℝ)) ?_ measurableSet_Ioo]
    · refine (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr ?_
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]; norm_num
      rw [this]; linarith
    · intro y hy
      obtain ⟨hy0, hyR⟩ := hy
      rw [hg]
      simp only [Set.indicator_apply, mem_Iio, if_pos hyR]
      rw [← Real.rpow_natCast y (n - 1), ← Real.rpow_add hy0]
      ring_nf
  · -- On `Ici R`: `g y = 0`, so the integrand is 0.
    rw [integrableOn_congr_fun (g := fun _ ↦ (0 : ℝ)) ?_ measurableSet_Ici]
    · exact integrableOn_zero
    · intro y hy
      rw [hg]
      simp only [Set.indicator_apply, mem_Iio]
      rw [if_neg (by simp only [not_lt]; exact hy)]
      ring

/-- **Radial `∫⁻`-finiteness over a ball** — the `ENNReal` shape consumed by the Gram–Schur
`b`-recursion. Immediate from `integrableOn_norm_rpow_neg_ball` via `setLIntegral_lt_top`. -/
theorem lintegral_norm_rpow_neg_ball_lt_top {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : a < n) (R : ℝ) :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        ENNReal.ofReal (‖x‖ ^ (-a))) < ⊤ :=
  (integrableOn_norm_rpow_neg_ball hn ha R).setLIntegral_lt_top

end DLNFibre.DLN.RLCT
