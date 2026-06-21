import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Cover` — the `(2,2,2)` cover assembly (measure half)

The `fm-2` measure half of `(2,2,2)` (#54/#76): assemble the 24-leaf resolution cover into the RLCT
value `rlctAtOn myF222 0 = 3/2`, where `myF222 = ‖A·B‖²` in the explicit `a00=0..b11=7` flat order
(the seam's `dlnLoss ∘ e222.symm`). The cover→`rlctAtOn` spine is `Foundations.S1Cover`; the
per-leaf thresholds are `Case222Value` (#68, both `= 3/2`).

This file holds the `(2,2,2)`-specific + `Skeleton`-dependent pieces: the per-leaf
`monomialThreshold` down-set (the `≥`-direction's per-leaf finiteness input) and — to come — the
concrete 3-deep chart cover and the final `rlctAtOn myF222 0 = 3/2`.
-/

open MeasureTheory Set
open scoped ENNReal
namespace DLNFibre.DLN.RLCT

/-- **Monomial integrand down-set (`0 < c'`).** On the unit box, decreasing the threshold exponent
keeps integrability: `monomialIntegrand d k h c' ≤ monomialIntegrand d k h c''` pointwise (the base
`∏|uⱼ|^{2kⱼ} ∈ [0,1]`, so its `(−c')`-power is `≤` its `(−c'')`-power for `c' ≤ c''`). NOTE the
`0 < c'` hypothesis is load-bearing: at `c' = 0` the base-`0` factor jumps (`0^0 = 1` vs `0^{−c''} =
0`), breaking the domination — the `c' = 0` case is integrable directly (integrand `= ∏|uⱼ|^{hⱼ}`,
bounded), handled separately. -/
theorem monomialIntegrand_downset (d : ℕ) (k h : Fin d → ℕ) (c' c'' : ℝ)
    (hc' : 0 < c') (hle : c' ≤ c'')
    (hint : IntegrableOn (monomialIntegrand d k h c'') (unitBox d) volume) :
    IntegrableOn (monomialIntegrand d k h c') (unitBox d) volume := by
  have hmeas : Measurable (monomialIntegrand d k h c') := by unfold monomialIntegrand; fun_prop
  apply hint.mono' hmeas.aestronglyMeasurable
  have hms : MeasurableSet (unitBox d) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [ae_restrict_iff' hms]
  filter_upwards [] with u hu
  simp only [unitBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left] at hu
  set P := ∏ j, |u j| ^ (h j) with hP
  set b := ∏ j, |u j| ^ (2 * k j) with hb
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hb0 : 0 ≤ b := Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hb1 : b ≤ 1 := by
    rw [hb]; apply Finset.prod_le_one (fun j _ => pow_nonneg (abs_nonneg _) _)
    intro j _; apply pow_le_one₀ (abs_nonneg _); rw [abs_of_nonneg (hu j).1]; exact (hu j).2
  show |monomialIntegrand d k h c' u| ≤ monomialIntegrand d k h c'' u
  unfold monomialIntegrand
  rw [← hP, ← hb, abs_of_nonneg (mul_nonneg hP0 (Real.rpow_nonneg hb0 _))]
  apply mul_le_mul_of_nonneg_left _ hP0
  rcases eq_or_lt_of_le hb0 with hb00 | hbpos
  · rw [← hb00, Real.zero_rpow (by linarith : -c' ≠ 0), Real.zero_rpow (by linarith : -c'' ≠ 0)]
  · exact Real.rpow_le_rpow_of_exponent_ge hbpos hb1 (by linarith)

/-- **Below the monomial threshold ⟹ leaf integral finite** (`0 < c'`). For `c' < monomialThreshold
d k h`, the weighted monomial integrand is integrable on the unit box: extract a strictly-larger
admissible `d'` (`lt_sSup`) and apply the down-set. The `≥`-direction's per-leaf input (each chart
converges below its threshold). -/
theorem monomialIntegrand_integrable_of_lt (d : ℕ) (k h : Fin d → ℕ) (c' : NNReal) (hc' : 0 < c')
    (hlt : (c' : ℝ≥0∞) < monomialThreshold d k h) :
    IntegrableOn (monomialIntegrand d k h (c' : ℝ)) (unitBox d) volume := by
  unfold monomialThreshold at hlt
  obtain ⟨c, hc_mem, hc'c⟩ := lt_sSup_iff.1 hlt
  obtain ⟨d', rfl, hint⟩ := hc_mem
  have hle : (c' : ℝ) ≤ (d' : ℝ) := by exact_mod_cast (by exact_mod_cast hc'c.le : c' ≤ d')
  exact monomialIntegrand_downset d k h (c' : ℝ) (d' : ℝ) (by exact_mod_cast hc') hle hint

/-- **Unit-factor threshold-invariance (the per-leaf fidelity bridge).** A leaf's integrand factors
as `monomialIntegrand d k h c · |unit|^{−c}` (NOT a bare monomial — the residual `unit` with
`unit 0 ≠ 0` is nonconstant). On a set where `|unit| ∈ [a, b]` (`0 < a`), the bounded factor
`|unit|^{−c}` does NOT change integrability — `monomial·|unit|^{−c}` integrable ⟺ `monomial`
integrable — via `Integrable.bdd_mul` both ways (the `S1.3` `rlct_unit_invariant_aux` technique,
fixed-box form). So the leaf's `monomialThreshold` IS its actual RLCT: the load-bearing per-leaf
identification (the `(2,2,2)` analogue of the seam's coordinate identification). NOTE the equality
to a *bare* monomial is FALSE for a nonconstant unit — the invariance is the correct statement. -/
theorem integrableOn_monomial_mul_unit_iff (d : ℕ) (k h : Fin d → ℕ) (unit : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (c : ℝ) (a b : ℝ) (ha : 0 < a) (hmeas : Measurable unit)
    (hunit : ∀ᵐ u ∂(volume.restrict S), a ≤ |unit u| ∧ |unit u| ≤ b) :
    IntegrableOn (fun u => monomialIntegrand d k h c u * |unit u| ^ (-c)) S volume
      ↔ IntegrableOn (monomialIntegrand d k h c) S volume := by
  constructor
  · intro hint
    have key : IntegrableOn
        (fun u => |unit u| ^ c * (monomialIntegrand d k h c u * |unit u| ^ (-c))) S volume := by
      refine Integrable.bdd_mul (c := max (a ^ c) (b ^ c)) hint
        ((by fun_prop : Measurable (fun u => |unit u| ^ c)).aestronglyMeasurable) ?_
      filter_upwards [hunit] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rcases le_or_gt 0 c with hc | hc
      · exact le_max_of_le_right (Real.rpow_le_rpow (abs_nonneg _) hu.2 hc)
      · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos ha hu.1 hc.le)
    refine key.congr ?_
    filter_upwards [hunit] with u hu
    have hupos : (0 : ℝ) < |unit u| := lt_of_lt_of_le ha hu.1
    rw [← mul_assoc, mul_comm (|unit u| ^ c), mul_assoc, ← Real.rpow_add hupos]; simp
  · intro hint
    have key : IntegrableOn (fun u => |unit u| ^ (-c) * monomialIntegrand d k h c u) S volume := by
      refine Integrable.bdd_mul (c := max (a ^ (-c)) (b ^ (-c))) hint
        ((by fun_prop : Measurable (fun u => |unit u| ^ (-c))).aestronglyMeasurable) ?_
      filter_upwards [hunit] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rcases le_or_gt 0 (-c) with hc | hc
      · exact le_max_of_le_right (Real.rpow_le_rpow (abs_nonneg _) hu.2 hc)
      · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos ha hu.1 hc.le)
    refine key.congr ?_
    filter_upwards [] with u; rw [mul_comm]

end DLNFibre.DLN.RLCT
