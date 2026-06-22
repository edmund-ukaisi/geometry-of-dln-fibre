import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Cover
import DLNFibre.DLN.RLCT.Validate.Case222Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMBridge` — the Route-M rlct-cover BRIDGE (crux2, §5(5))

The general per-node mechanism's value step (g138 §5(5)): `rlctAtOn (core) 0 = ⨅ᵢ monomialThreshold`,
over fm3's chart cover. MECHANISM-INDEPENDENT — consumes the chart family `(ι, d, k, h)` + the cover
datum ABSTRACTLY (an `IsRouteMCover` hypothesis), so it is unaffected by how the charts are PRODUCED
(fm3's geometry; the C1 squeeze→monomial correction changes the production, not this consumed assembly).
Generalizes `Case222CoverGE`/`Case222CoverGETail` (the bespoke (2,2,2) `≥`-cover) to an abstract cover.
Cover #21 (`resolution_value_of_atlas`) then closes `⨅ = ofReal(lambdaCore M)`. Core-only.
-/

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **The `c'=0` leaf-integral edge.** `∫⁻_{unitBox} ofReal(monomialIntegrand d k h 0) < ⊤`: at `c'=0`
the integrand is `∏ⱼ |uⱼ|^{hⱼ} ≤ 1` on the compact box `[0,1]^d`, so the integral is `≤ vol(box) < ⊤`. -/
theorem monomialIntegrand_zero_lintegral_lt_top (d : ℕ) (k h : Fin d → ℕ) :
    ∫⁻ y in unitBox d, ENNReal.ofReal (monomialIntegrand d k h 0 y) < ⊤ := by
  have hcpt : IsCompact (unitBox d) := by
    rw [unitBox]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbound : ∀ y ∈ unitBox d, ENNReal.ofReal (monomialIntegrand d k h 0 y) ≤ 1 := by
    intro y hy
    rw [unitBox, Set.mem_univ_pi] at hy
    rw [monomialIntegrand]
    simp only [neg_zero, Real.rpow_zero, mul_one]
    rw [ENNReal.ofReal_le_one]
    apply Finset.prod_le_one (fun j _ => by positivity)
    intro j _
    have hj := hy j; rw [Set.mem_Icc] at hj
    have : |y j| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hj.1], hj.2⟩
    exact pow_le_one₀ (abs_nonneg _) this
  calc ∫⁻ y in unitBox d, ENNReal.ofReal (monomialIntegrand d k h 0 y)
      ≤ ∫⁻ _ in unitBox d, 1 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hcpt.measurableSet] with y hy using hbound y hy
    _ = volume (unitBox d) := by rw [lintegral_one, Measure.restrict_apply_univ]
    _ < ⊤ := hcpt.measure_lt_top

/-- **The abstract Route-M chart cover** (the interface fm3's chart geometry fills, §5(1,2)). The
generalized `Case222CoverGE` input — `crux2`'s bridge consumes it ABSTRACTLY; the C1 squeeze→monomial
correction changes how fm3 PRODUCES it, not this consumed shape. -/
structure IsRouteMCover {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) : Prop where
  /-- `F` is measurable (polynomial core). -/
  Fmeas : Measurable F
  /-- The base nbhd `U` is open and contains the deepest point `0`. -/
  Uopen : IsOpen U
  Umem : (0 : Fin N → ℝ) ∈ U
  /-- (COVER ≥) the `U`-integral is bounded by the SUM over leaves of the per-leaf monomial integrals
  (the cover split + per-chart change-of-variables). -/
  cover_le : ∀ c' : NNReal,
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ)))
        ≤ ∑ i : ι, ∫⁻ y in unitBox (d i),
            ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y)
  /-- (COVER ≤) for `c'` at-or-above some leaf's threshold, the `U`-integral diverges on any open
  `Ω ∋ 0` (the ε-uniform leaf monomial singularity). -/
  cover_ge_div : ∀ c' : NNReal, (∃ i : ι, monomialThreshold (d i) (k i) (h i) ≤ (c' : ℝ≥0∞)) →
      ∀ Ω : Set (Fin N → ℝ), IsOpen Ω → (0 : Fin N → ℝ) ∈ Ω →
        ¬ IntegrableOn (fun x => |F x| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) x) Ω volume

/-- **The Route-M rlct-cover BRIDGE (crux2, §5(5)).** Given the abstract chart cover,
`rlctAtOn F 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`. `le_antisymm`: (≤) any admissible `c'` has
`c' ≤ ⨅` (else `exists_lt_of_ciInf_lt` + `cover_ge_div` contradiction); (≥) for `c' < ⨅`, `cover_le` +
per-leaf integrability (`monomialIntegrand_integrable_of_lt`, `…_zero_…` at `c'=0`) + `ENNReal.sum_lt_top`
give `∫⁻_U < ⊤` (`rlctAtOn_ge_of_integral_lt`). Mechanism-independent. `⨅ = ofReal(lambdaCore M)` is
cover #21's `resolution_value_of_atlas`, NOT here. -/
theorem routeM_rlctAtOn_eq_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    (ι : Type) [Fintype ι] [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hcover : IsRouteMCover F U ι d k h) :
    rlctAtOn F (0 : Fin N → ℝ) = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  set t := ⨅ i : ι, monomialThreshold (d i) (k i) (h i) with ht
  refine le_antisymm ?_ ?_
  · apply rlctAtOn_le_of_adm_le F t
    intro c' hadm
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hgt
    obtain ⟨Ω, hΩopen, h0Ω, hint⟩ := hadm
    exact hcover.cover_ge_div c' ⟨i, hi.le⟩ Ω hΩopen h0Ω hint
  · apply rlctAtOn_ge_of_integral_lt F hcover.Fmeas U hcover.Uopen hcover.Umem t
    intro c' hc'lt
    refine lt_of_le_of_lt (hcover.cover_le c') ?_
    rw [ENNReal.sum_lt_top]
    intro i _
    rcases eq_or_lt_of_le (zero_le c') with hc0 | hc0
    · rw [← hc0]; exact monomialIntegrand_zero_lintegral_lt_top (d i) (k i) (h i)
    · have hlt_i : (c' : ℝ≥0∞) < monomialThreshold (d i) (k i) (h i) :=
        lt_of_lt_of_le hc'lt (iInf_le _ i)
      exact (monomialIntegrand_integrable_of_lt (d i) (k i) (h i) c' hc0 hlt_i).setLIntegral_lt_top

end DLNFibre.DLN.RLCT
