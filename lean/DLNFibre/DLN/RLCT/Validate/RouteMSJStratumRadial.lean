import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceAssembly
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

set_option linter.style.longLine false

/-!
# `RouteMSJStratumRadial` — the single-block per-stratum radial finiteness (Brick A, item 3)

**Thread `genm-arch1build` (aoyagi-full Stage 2), Brick A.** The single-block per-stratum transverse loss,
per arch1probe §Q-B: on a single `(ℓ, s)` stratum the transverse loss is an exact quadratic form
`g(w) = ‖Λ · w‖²` with `Λ` full column rank (the chart-data Morse–Bott normal form). This module CONSTRUCTS
`g`, proves the two `stratum_corner_lt_top` obligations `hom`/`hlb`, and closes the per-stratum radial:

- **`hom` — EXACT** (`g (r • w) = r² · g w`, `Λ` fixed): `mulVec` is linear.
- **`hlb` — a positive unit-sphere floor** `= σ_min(Λ)² > 0`: since `Λ` is full column rank
  (`Λ.mulVec w = 0 → w = 0`), the continuous `g` is `> 0` at every unit vector, and the unit sphere is
  compact, so `g` attains a positive minimum on it (extreme-value theorem — no eigenvalue machinery).

Abstract in `Λ` (the chart data). The `ℓ = 0` biquadratic corner `‖Y·W‖²` is degree-4 with NO sphere
floor — it must route through `twoBlock_radial_le`, NOT this lemma (arch1probe's KILL). Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The single-block per-stratum radial finiteness.** For a valid stratum `(ℓ, s)` at cut `u` with a
nonzero codimension `C = clsCodim ![M₀,M₁,M₂] u ℓ s`, and any FULL-COLUMN-RANK `Λ : Matrix (Fin m) (Fin C)`
(`Λ.mulVec w = 0 → w = 0`), the transverse loss `g(w) = ∑ᵢ (Λ·w)ᵢ²` is degree-2-homogeneous with a
positive unit-sphere floor, so the residual power integral over `[−1,1]^C` at the shifted exponent
`q = c'−ab/2` is finite (`stratum_corner_lt_top`). This is the single-block Morse–Bott normal form
(arch1probe §Q-B); the `ℓ=0` biquadratic corner routes through `twoBlock_radial_le` instead. -/
theorem single_block_stratum_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (u ℓ s : ℕ) (c' : ℝ)
    (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2)
    (hN : 0 < clsCodim ![M 0, M 1, M 2] u ℓ s)
    (hc' : (((M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2 < c') (hcT : c' < carrierThreshold M)
    {m : ℕ} (Λ : Matrix (Fin m) (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s)) ℝ)
    (hΛ : ∀ w : Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) → ℝ, Λ.mulVec w = 0 → w = 0) :
    ∫⁻ z in Set.univ.pi
        (fun _ : Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal
          ((∑ i, (Λ.mulVec z i) ^ 2) ^ (-(c' - (((M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2))) < ⊤ := by
  classical
  haveI : NeZero (clsCodim ![M 0, M 1, M 2] u ℓ s) := ⟨by omega⟩
  set g : (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) → ℝ) → ℝ :=
    fun w => ∑ i, (Λ.mulVec w i) ^ 2 with hg_def
  -- `Λ *ᵥ ·` is continuous (a finite-dimensional linear map)
  have hmv : Continuous (fun w : Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) → ℝ => Λ.mulVec w) := by
    have h := LinearMap.continuous_of_finiteDimensional Λ.mulVecLin
    exact h.congr (fun w => (Matrix.mulVecLin_apply Λ w).symm)
  -- `g` continuous ⟹ measurable
  have hgcont : Continuous g := by
    rw [hg_def]
    exact continuous_finset_sum _ (fun i _ => ((continuous_apply i).comp hmv).pow 2)
  have hgmeas : Measurable g := hgcont.measurable
  -- degree-2 homogeneity (`Λ` fixed): `mulVec` is linear
  have hom : ∀ (r : ℝ) (x : Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) → ℝ),
      g (r • x) = r ^ 2 * g x := by
    intro r x
    simp only [hg_def, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  -- the positive unit-sphere floor, via the extreme-value theorem on the compact sphere
  have hcont : Continuous
      (fun x : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s)) => g (WithLp.ofLp x)) :=
    hgcont.comp (PiLp.continuous_ofLp 2 (fun _ : Fin (clsCodim ![M 0, M 1, M 2] u ℓ s) => ℝ))
  obtain ⟨a, ha, hlb⟩ : ∃ a : ℝ, 0 < a ∧
      ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s))) 1,
        a ≤ g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s)))) := by
    obtain ⟨ω₀, hω₀mem, hmin⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s))) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    refine ⟨g (WithLp.ofLp (ω₀ : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s)))), ?_,
      fun ω => isMinOn_iff.mp hmin
        (ω : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s))) ω.2⟩
    -- `g (ofLp ω₀) > 0`: `ω₀` is a unit vector, so `Λ · ofLp ω₀ ≠ 0`, so the sum of squares is `> 0`
    simp only [hg_def]
    have hv : Λ.mulVec
        (WithLp.ofLp (ω₀ : EuclideanSpace ℝ (Fin (clsCodim ![M 0, M 1, M 2] u ℓ s)))) ≠ 0 := by
      intro hvz
      have hofz := hΛ _ hvz
      rw [WithLp.ofLp_eq_zero] at hofz
      rw [Metric.mem_sphere, dist_zero_right, hofz, norm_zero] at hω₀mem
      exact one_ne_zero hω₀mem.symm
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩
  simpa only [hg_def] using
    stratum_corner_lt_top M u ℓ s c' hu hs hℓs hbℓ hN hc' hcT g hgmeas hom a ha hlb

end DLNFibre.DLN.RLCT
