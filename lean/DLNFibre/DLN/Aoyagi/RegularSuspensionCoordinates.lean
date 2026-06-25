import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import DLNFibre.DLN.Aoyagi.ChartTopology
import DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
import DLNFibre.DLN.Aoyagi.FinalFormula
import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge

/-!
# Scalar coordinate indices for Aoyagi's p. 13 blocks

This file scalarizes the three regular block families appearing after
Aoyagi's product reduction:

* `Ctop - 1`,
* `F2`,
* `F3`.

It also scalarizes the residual `D` block while keeping those coordinates
separate from the regular-coordinate index and regular-variable shift.  It
proves finite coordinate bookkeeping and componentwise continuity projections,
plus the algebraic bridge from tagged scalar-coordinate values to the relevant
matrix-entry ideals.  It does not construct a regular-suspension chart, prove
analytic ideal transport, prove chart coverage, prove Jacobian compatibility,
produce normal crossings, or extract pole order/RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Matrix

set_option linter.style.longLine false

universe uι uμ uν

/-- Finite algebraic square-sum attached to a scalar coordinate family.

This is the square-sum convention for a finite generator family.  It is not an
analytic norm, chart statement, or RLCT statement. -/
def aoyagiCoordinateSquareSum
    {η R : Type*} [Fintype η] [CommSemiring R] (f : η → R) : R :=
  ∑ c, f c ^ 2

/-- The square-sum over a disjoint sum of coordinate indices is the sum of the
two square-sums. -/
@[simp]
theorem aoyagiCoordinateSquareSum_sumElim
    {η κ R : Type*} [Fintype η] [Fintype κ] [CommSemiring R]
    (f : η → R) (g : κ → R) :
    aoyagiCoordinateSquareSum (Sum.elim f g) =
      aoyagiCoordinateSquareSum f + aoyagiCoordinateSquareSum g := by
  simp [aoyagiCoordinateSquareSum, Fintype.sum_sum_type]

/-- Reindexing a finite coordinate family does not change its square-sum. -/
theorem aoyagiCoordinateSquareSum_comp_equiv
    {η κ R : Type*} [Fintype η] [Fintype κ] [CommSemiring R]
    (e : η ≃ κ) (f : κ → R) :
    aoyagiCoordinateSquareSum (fun a : η => f (e a)) =
      aoyagiCoordinateSquareSum f := by
  simpa [aoyagiCoordinateSquareSum] using e.sum_comp (fun b : κ => f b ^ 2)

/-- A finite coordinate square-sum is nonnegative over an ordered scalar
ring. -/
theorem aoyagiCoordinateSquareSum_nonneg
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : η → R) :
    0 ≤ aoyagiCoordinateSquareSum f := by
  exact Finset.sum_nonneg (fun c _ => sq_nonneg (f c))

/-- A Euclidean coordinate vector in a ball of radius at most `1` has finite
coordinate square-sum at most `1`. -/
theorem aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one
    {η : Type*} [Fintype η] {Rmax : ℝ}
    {u : EuclideanSpace ℝ η}
    (hu : u ∈ Metric.ball (0 : EuclideanSpace ℝ η) Rmax)
    (hRmax_le_one : Rmax ≤ 1) :
    aoyagiCoordinateSquareSum (fun i : η => u i) ≤ 1 := by
  have hnorm_lt : ‖u‖ < Rmax := by
    simpa [Metric.mem_ball, dist_zero_right] using hu
  have hnorm_le_one : ‖u‖ ≤ 1 :=
    (le_of_lt hnorm_lt).trans hRmax_le_one
  have hnorm_sq_le_one : ‖u‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [norm_nonneg u]
  simpa [aoyagiCoordinateSquareSum, EuclideanSpace.real_norm_sq_eq] using
    hnorm_sq_le_one

/-- For a real matrix, the trace form `Tr(MᵀM)` is the entrywise finite
coordinate square-sum. -/
theorem matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum
    {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    ((Mᵀ * M).trace : ℝ) =
      aoyagiCoordinateSquareSum (fun ij : m × n => M ij.1 ij.2) := by
  classical
  calc
    ((Mᵀ * M).trace : ℝ) =
        ∑ j : n, ∑ i : m, M i j * M i j := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = ∑ i : m, ∑ j : n, M i j * M i j := by
      rw [Finset.sum_comm]
    _ = ∑ ij : m × n, M ij.1 ij.2 ^ 2 := by
      simp [Fintype.sum_prod_type, pow_two]
    _ = aoyagiCoordinateSquareSum (fun ij : m × n => M ij.1 ij.2) := by
      rw [aoyagiCoordinateSquareSum]

/-- Pointwise square estimate used to compare corrected and uncorrected
finite square-sums. -/
theorem aoyagi_sq_sub_le_two_mul_sq_add_two_mul_sq
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- Pointwise square estimate for a sum. -/
theorem aoyagi_sq_add_le_two_mul_sq_add_two_mul_sq
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (a b : R) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Finite square-sum estimate for coordinatewise subtraction. -/
theorem aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f g : η → R) :
    aoyagiCoordinateSquareSum (fun c => f c - g c) ≤
      2 * aoyagiCoordinateSquareSum f + 2 * aoyagiCoordinateSquareSum g := by
  classical
  unfold aoyagiCoordinateSquareSum
  calc
    ∑ c, (f c - g c) ^ 2 ≤
        ∑ c, (2 * f c ^ 2 + 2 * g c ^ 2) := by
      exact Finset.sum_le_sum
        (fun c _ => aoyagi_sq_sub_le_two_mul_sq_add_two_mul_sq (f c) (g c))
    _ = (∑ c, 2 * f c ^ 2) + ∑ c, 2 * g c ^ 2 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (∑ c, f c ^ 2) + 2 * ∑ c, g c ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Finite square-sum estimate for coordinatewise addition. -/
theorem aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
    {η R : Type*} [Fintype η] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (f g : η → R) :
    aoyagiCoordinateSquareSum (fun c => f c + g c) ≤
      2 * aoyagiCoordinateSquareSum f + 2 * aoyagiCoordinateSquareSum g := by
  classical
  unfold aoyagiCoordinateSquareSum
  calc
    ∑ c, (f c + g c) ^ 2 ≤
        ∑ c, (2 * f c ^ 2 + 2 * g c ^ 2) := by
      exact Finset.sum_le_sum
        (fun c _ => aoyagi_sq_add_le_two_mul_sq_add_two_mul_sq (f c) (g c))
    _ = (∑ c, 2 * f c ^ 2) + ∑ c, 2 * g c ^ 2 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (∑ c, f c ^ 2) + 2 * ∑ c, g c ^ 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Frobenius-style finite matrix-product estimate for coordinate
square-sums. -/
theorem matrixCoordinateSquareSum_mul_le_mul
    {ι μ ν R : Type*} [Fintype ι] [Fintype μ] [Fintype ν]
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (A : Matrix μ ι R) (B : Matrix ι ν R) :
    aoyagiCoordinateSquareSum (fun ij : μ × ν => (A * B) ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (fun ij : μ × ι => A ij.1 ij.2) *
        aoyagiCoordinateSquareSum (fun ij : ι × ν => B ij.1 ij.2) := by
  classical
  unfold aoyagiCoordinateSquareSum
  calc
    ∑ ij : μ × ν, (A * B) ij.1 ij.2 ^ 2 ≤
        ∑ ij : μ × ν,
          (∑ k : ι, A ij.1 k ^ 2) * ∑ k : ι, B k ij.2 ^ 2 := by
      exact Finset.sum_le_sum (fun ij _ => by
        simpa [Matrix.mul_apply] using
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
            (fun k => A ij.1 k) (fun k => B k ij.2)))
    _ =
        (∑ ij : μ × ι, A ij.1 ij.2 ^ 2) *
          ∑ ij : ι × ν, B ij.1 ij.2 ^ 2 := by
      simp only [Fintype.sum_prod_type]
      calc
        ∑ i : μ, ∑ j : ν,
            (∑ k : ι, A i k ^ 2) * ∑ k : ι, B k j ^ 2 =
            ∑ i : μ, (∑ k : ι, A i k ^ 2) *
              ∑ j : ν, ∑ k : ι, B k j ^ 2 := by
          simp [Finset.mul_sum]
        _ =
            (∑ i : μ, ∑ k : ι, A i k ^ 2) *
              ∑ j : ν, ∑ k : ι, B k j ^ 2 := by
          rw [Finset.sum_mul]
        _ =
            (∑ i : μ, ∑ k : ι, A i k ^ 2) *
              ∑ k : ι, ∑ j : ν, B k j ^ 2 := by
          have hcomm :
              (∑ j : ν, ∑ k : ι, B k j ^ 2) =
                ∑ k : ι, ∑ j : ν, B k j ^ 2 := by
            rw [Finset.sum_comm]
          rw [hcomm]

/-- Two-sided multiplication by finite matrices is bounded for coordinate
square-sums. -/
theorem matrixCoordinateSquareSum_mul_mul_le_mul
    {ι μ ν κ R : Type*} [Fintype ι] [Fintype μ] [Fintype ν] [Fintype κ]
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (L : Matrix μ ι R) (M : Matrix ι ν R) (Rmat : Matrix ν κ R) :
    aoyagiCoordinateSquareSum
        (fun ij : μ × κ => (L * M * Rmat) ij.1 ij.2) ≤
      (aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
          aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2)) *
        aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2) := by
  classical
  have hright :=
    matrixCoordinateSquareSum_mul_le_mul (A := L * M) (B := Rmat)
  have hleft :=
    matrixCoordinateSquareSum_mul_le_mul (A := L) (B := M)
  let SL := aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2)
  let SM := aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2)
  let SR := aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2)
  let SLM := aoyagiCoordinateSquareSum (fun ij : μ × ν => (L * M) ij.1 ij.2)
  let SLMR :=
    aoyagiCoordinateSquareSum
      (fun ij : μ × κ => (L * M * Rmat) ij.1 ij.2)
  have hright' : SLMR ≤ SLM * SR := by
    simpa [SLMR, SLM, SR, Matrix.mul_assoc] using hright
  have hleft' : SLM ≤ SL * SM := by
    simpa [SLM, SL, SM] using hleft
  have hSR : 0 ≤ SR := by
    exact aoyagiCoordinateSquareSum_nonneg
      (fun ij : ν × κ => Rmat ij.1 ij.2)
  have hSM : 0 ≤ SM := by
    exact aoyagiCoordinateSquareSum_nonneg
      (fun ij : ι × ν => M ij.1 ij.2)
  have hbounded : SLM * SR ≤ (SL * SR) * SM := by
    calc
      SLM * SR ≤ (SL * SM) * SR := mul_le_mul_of_nonneg_right hleft' hSR
      _ = (SL * SR) * SM := by ring
  calc
    SLMR ≤ SLM * SR := hright'
    _ ≤ (SL * SR) * SM := hbounded

/-- If the product of the left and right multiplier square-sums is bounded by
`K`, then a small enough constant times the transformed square-sum is bounded
by the original square-sum. -/
theorem const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
    {ι μ ν κ R : Type*} [Fintype ι] [Fintype μ] [Fintype ν] [Fintype κ]
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {L : Matrix μ ι R} {M : Matrix ι ν R} {Rmat : Matrix ν κ R}
    {T : Matrix μ κ R} {c K : R}
    (hc_nonneg : 0 ≤ c)
    (hcK : c * K ≤ 1)
    (hbound :
      aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
          aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2) ≤ K)
    (hT : L * M * Rmat = T) :
    c * aoyagiCoordinateSquareSum (fun ij : μ × κ => T ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2) := by
  classical
  let SL := aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2)
  let SM := aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2)
  let SR := aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2)
  let ST := aoyagiCoordinateSquareSum (fun ij : μ × κ => T ij.1 ij.2)
  have hSM : 0 ≤ SM := by
    exact aoyagiCoordinateSquareSum_nonneg
      (fun ij : ι × ν => M ij.1 ij.2)
  have hmul :
      ST ≤ (SL * SR) * SM := by
    simpa [ST, SL, SM, SR, hT] using
      matrixCoordinateSquareSum_mul_mul_le_mul L M Rmat
  have hbound' : (SL * SR) * SM ≤ K * SM :=
    mul_le_mul_of_nonneg_right hbound hSM
  calc
    c * ST ≤ c * (K * SM) := by
      exact mul_le_mul_of_nonneg_left (hmul.trans hbound') hc_nonneg
    _ = (c * K) * SM := by ring
    _ ≤ 1 * SM := by
      exact mul_le_mul_of_nonneg_right hcK hSM
    _ = SM := one_mul SM

/-- Fixed left and right multiplication compare finite coordinate square-sums
up to a positive constant. -/
theorem exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq
    {ι μ ν κ : Type*} [Fintype ι] [Fintype μ] [Fintype ν] [Fintype κ]
    {L : Matrix μ ι ℝ} {M : Matrix ι ν ℝ} {Rmat : Matrix ν κ ℝ}
    {T : Matrix μ κ ℝ}
    (hT : L * M * Rmat = T) :
    ∃ c : ℝ, 0 < c ∧
      c * aoyagiCoordinateSquareSum (fun ij : μ × κ => T ij.1 ij.2) ≤
        aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2) := by
  classical
  let Kmul : ℝ :=
    max 1
      (aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
        aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2))
  let c : ℝ := Kmul⁻¹
  have hKmul_pos : 0 < Kmul := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) _)
  have hc_pos : 0 < c := inv_pos.mpr hKmul_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hcK : c * Kmul ≤ 1 := by
    dsimp [c]
    rw [inv_mul_cancel₀ (ne_of_gt hKmul_pos)]
  have hbound :
      aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
          aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2) ≤
        Kmul := by
    exact le_max_right (1 : ℝ) _
  exact
    ⟨c, hc_pos,
      const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
        (L := L) (M := M) (Rmat := Rmat) (T := T)
        hc_nonneg hcK hbound hT⟩

/-- Uniform version of
`exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq`: the comparison
constant depends only on the fixed left and right multipliers. -/
theorem exists_pos_const_forall_matrixCoordinateSquareSum_le_mul
    {ι μ ν κ : Type*} [Fintype ι] [Fintype μ] [Fintype ν] [Fintype κ]
    (L : Matrix μ ι ℝ) (Rmat : Matrix ν κ ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ M : Matrix ι ν ℝ,
        c * aoyagiCoordinateSquareSum
          (fun ij : μ × κ => (L * M * Rmat) ij.1 ij.2) ≤
        aoyagiCoordinateSquareSum (fun ij : ι × ν => M ij.1 ij.2) := by
  classical
  let Kmul : ℝ :=
    max 1
      (aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
        aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2))
  let c : ℝ := Kmul⁻¹
  have hKmul_pos : 0 < Kmul := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) _)
  have hc_pos : 0 < c := inv_pos.mpr hKmul_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hcK : c * Kmul ≤ 1 := by
    dsimp [c]
    rw [inv_mul_cancel₀ (ne_of_gt hKmul_pos)]
  have hbound :
      aoyagiCoordinateSquareSum (fun ij : μ × ι => L ij.1 ij.2) *
          aoyagiCoordinateSquareSum (fun ij : ν × κ => Rmat ij.1 ij.2) ≤
        Kmul := by
    exact le_max_right (1 : ℝ) _
  refine ⟨c, hc_pos, ?_⟩
  intro M
  exact
    const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
      (L := L) (M := M) (Rmat := Rmat) (T := L * M * Rmat)
      hc_nonneg hcK hbound rfl

/-- Changing finite bases in the domain and codomain compares the coordinate
square-sum of a linear map up to a positive constant.

The constant depends only on the two fixed basis-change matrices. -/
theorem exists_pos_const_linearMap_toMatrix_squareSum_le_of_basis_change
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq ι']
    (bE : Module.Basis ι ℝ E) (bE' : Module.Basis ι' ℝ E)
    (bF : Module.Basis κ ℝ F) (bF' : Module.Basis κ' ℝ F)
    (f : E →ₗ[ℝ] F) :
    ∃ c : ℝ, 0 < c ∧
      c * aoyagiCoordinateSquareSum
        (fun ij : κ × ι => (LinearMap.toMatrix bE bF f) ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum
        (fun ij : κ' × ι' => (LinearMap.toMatrix bE' bF' f) ij.1 ij.2) := by
  classical
  let L : Matrix κ κ' ℝ :=
    LinearMap.toMatrix bF' bF (LinearMap.id : F →ₗ[ℝ] F)
  let M : Matrix κ' ι' ℝ :=
    LinearMap.toMatrix bE' bF' f
  let Rmat : Matrix ι' ι ℝ :=
    LinearMap.toMatrix bE bE' (LinearMap.id : E →ₗ[ℝ] E)
  let T : Matrix κ ι ℝ :=
    LinearMap.toMatrix bE bF f
  have hright :
      LinearMap.toMatrix bE bF' f = M * Rmat := by
    simp [M, Rmat]
  have hleft :
      LinearMap.toMatrix bE bF f = L * LinearMap.toMatrix bE bF' f := by
    simp [L]
  have hT : L * M * Rmat = T := by
    calc
      L * M * Rmat = L * (M * Rmat) := by rw [Matrix.mul_assoc]
      _ = L * LinearMap.toMatrix bE bF' f := by rw [← hright]
      _ = LinearMap.toMatrix bE bF f := by rw [← hleft]
      _ = T := rfl
  simpa [L, M, Rmat, T] using
    exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq
      (L := L) (M := M) (Rmat := Rmat) (T := T) hT

/-- Uniform basis-change comparison for coordinate square-sums of linear maps:
the comparison constant depends only on the two fixed pairs of bases, not on
the map. -/
theorem exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq ι']
    (bE : Module.Basis ι ℝ E) (bE' : Module.Basis ι' ℝ E)
    (bF : Module.Basis κ ℝ F) (bF' : Module.Basis κ' ℝ F) :
    ∃ c : ℝ, 0 < c ∧
      ∀ f : E →ₗ[ℝ] F,
        c * aoyagiCoordinateSquareSum
          (fun ij : κ × ι => (LinearMap.toMatrix bE bF f) ij.1 ij.2) ≤
        aoyagiCoordinateSquareSum
          (fun ij : κ' × ι' => (LinearMap.toMatrix bE' bF' f) ij.1 ij.2) := by
  classical
  let L : Matrix κ κ' ℝ :=
    LinearMap.toMatrix bF' bF (LinearMap.id : F →ₗ[ℝ] F)
  let Rmat : Matrix ι' ι ℝ :=
    LinearMap.toMatrix bE bE' (LinearMap.id : E →ₗ[ℝ] E)
  rcases exists_pos_const_forall_matrixCoordinateSquareSum_le_mul L Rmat with
    ⟨c, hc_pos, hc⟩
  refine ⟨c, hc_pos, ?_⟩
  intro f
  let M : Matrix κ' ι' ℝ :=
    LinearMap.toMatrix bE' bF' f
  have hright :
      LinearMap.toMatrix bE bF' f = M * Rmat := by
    simp [M, Rmat]
  have hleft :
      LinearMap.toMatrix bE bF f = L * LinearMap.toMatrix bE bF' f := by
    simp [L]
  have hT :
      L * M * Rmat = LinearMap.toMatrix bE bF f := by
    calc
      L * M * Rmat = L * (M * Rmat) := by rw [Matrix.mul_assoc]
      _ = L * LinearMap.toMatrix bE bF' f := by rw [← hright]
      _ = LinearMap.toMatrix bE bF f := by rw [← hleft]
  simpa [M, L, Rmat, hT] using hc M

/-- A finite real coordinate square-sum is continuous at a point when the
coordinate family is continuous there. -/
theorem aoyagiCoordinateSquareSum_continuousAt
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (hf : ContinuousAt f x₀) :
    ContinuousAt (fun x : α => aoyagiCoordinateSquareSum (f x)) x₀ := by
  classical
  unfold aoyagiCoordinateSquareSum
  change ContinuousAt (fun x : α => ∑ c : η, (f x c) ^ 2) x₀
  refine Finset.induction_on (s := (Finset.univ : Finset η)) ?_ ?_
  · simpa using (continuousAt_const : ContinuousAt (fun _ : α => (0 : ℝ)) x₀)
  · intro c s hcs ih
    have hterm : ContinuousAt (fun x : α => (f x c) ^ 2) x₀ :=
      (((continuous_apply c).continuousAt.comp hf).pow 2)
    simpa [Finset.sum_insert, hcs] using hterm.add ih

/-- A finite real coordinate square-sum is measurable when the coordinate
family is measurable. -/
theorem measurable_aoyagiCoordinateSquareSum
    {η α : Type*} [Fintype η] [MeasurableSpace α]
    {f : α → η → ℝ} (hf : Measurable f) :
    Measurable (fun x : α => aoyagiCoordinateSquareSum (f x)) := by
  classical
  unfold aoyagiCoordinateSquareSum
  simpa [pow_two] using
    Finset.measurable_sum Finset.univ fun c _ =>
      ((measurable_pi_apply c).comp hf).mul ((measurable_pi_apply c).comp hf)

/-- A continuous real-valued function is locally bounded above by its value
plus one. -/
theorem continuousAt_eventually_le_self_add_one
    {α : Type*} [TopologicalSpace α] {f : α → ℝ} {x₀ : α}
    (hf : ContinuousAt f x₀) :
    ∀ᶠ x in nhds x₀, f x ≤ f x₀ + 1 := by
  have htarget : ∀ᶠ y in nhds (f x₀), y ≤ f x₀ + 1 := by
    exact eventually_le_nhds (show f x₀ < f x₀ + 1 by linarith)
  exact hf.eventually htarget

/-- A continuous real-valued function admits a positive local upper bound. -/
theorem continuousAt_exists_pos_eventually_le
    {α : Type*} [TopologicalSpace α] {f : α → ℝ} {x₀ : α}
    (hf : ContinuousAt f x₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x in nhds x₀, f x ≤ K := by
  refine ⟨max (f x₀ + 1) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · exact
      (continuousAt_eventually_le_self_add_one hf).mono
        (fun _ hx ↦ hx.trans (le_max_left _ _))

/-- A product-neighborhood of `(x₀, 0)` contains a neighborhood in the first
factor times a small Euclidean ball in the second factor. -/
theorem exists_pos_ball_eventually_forall_mem_of_mem_nhds_prod_zero
    {α η : Type*} [TopologicalSpace α] [Fintype η]
    {s : Set (α × EuclideanSpace ℝ η)} {x₀ : α}
    (hs : s ∈ nhds (x₀, (0 : EuclideanSpace ℝ η))) :
    ∃ R : ℝ, 0 < R ∧
      ∀ᶠ x in nhds x₀,
        ∀ u : EuclideanSpace ℝ η,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ η) R → (x, u) ∈ s := by
  rcases mem_nhds_prod_iff.mp hs with ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhds_iff.1 hV with ⟨R, hR, hRmem⟩
  exact ⟨R, hR,
    Filter.eventually_of_mem hU (fun x hx u hu ↦ hUV ⟨hx, hRmem hu⟩)⟩

/-- A finite real coordinate square-sum admits a positive local upper bound
when its coordinate family is continuous. -/
theorem aoyagiCoordinateSquareSum_exists_pos_eventually_le_of_continuousAt
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (hf : ContinuousAt f x₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (f x) ≤ K :=
  continuousAt_exists_pos_eventually_le
    (aoyagiCoordinateSquareSum_continuousAt hf)

/-- Centered continuity lets one shrink to a neighborhood where the finite real
coordinate square-sum is at most `1`. -/
theorem aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (h0 : f x₀ = 0)
    (hf : ContinuousAt f x₀) :
    ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (f x) ≤ 1 := by
  have hs :
      ContinuousAt (fun x : α => aoyagiCoordinateSquareSum (f x)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hf
  have hcenter :
      aoyagiCoordinateSquareSum (f x₀) = (0 : ℝ) := by
    simp [aoyagiCoordinateSquareSum, h0]
  have hsmall :
      ∀ᶠ y in nhds (aoyagiCoordinateSquareSum (f x₀)), y ≤ (1 : ℝ) := by
    simpa [hcenter] using (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  exact hs.eventually hsmall

/-- Centered continuity of two finite real coordinate families gives a
neighborhood where their square-sums have total at most `1`. -/
theorem aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
    {η κ α : Type*} [Fintype η] [Fintype κ] [TopologicalSpace α]
    {f : α → η → ℝ} {g : α → κ → ℝ} {x₀ : α}
    (hf0 : f x₀ = 0)
    (hg0 : g x₀ = 0)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum (f x) + aoyagiCoordinateSquareSum (g x) ≤ 1 := by
  let F : α → (η ⊕ κ) → ℝ := fun x => Sum.elim (f x) (g x)
  have hF0 : F x₀ = 0 := by
    funext c
    cases c <;> simp [F, hf0, hg0]
  have hF : ContinuousAt F x₀ := by
    refine continuousAt_pi.2 ?_
    intro c
    cases c with
    | inl c =>
        exact ((continuous_apply c).continuousAt.comp hf)
    | inr c =>
        exact ((continuous_apply c).continuousAt.comp hg)
  have hsmall :
      ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (F x) ≤ 1 :=
    aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero hF0 hF
  filter_upwards [hsmall] with x hx
  simpa [F, aoyagiCoordinateSquareSum_sumElim] using hx

/-- Scalar centered-continuity data for each coordinate is enough to shrink to
a neighborhood where the finite real square-sum is at most `1`. -/
theorem aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt
    {η α : Type*} [Fintype η] [TopologicalSpace α]
    {f : α → η → ℝ} {x₀ : α}
    (hf : ∀ c, f x₀ c = 0 ∧ ContinuousAt (fun x : α => f x c) x₀) :
    ∀ᶠ x in nhds x₀, aoyagiCoordinateSquareSum (f x) ≤ 1 := by
  have h0 : f x₀ = 0 := by
    funext c
    exact (hf c).1
  have hcont : ContinuousAt f x₀ :=
    continuousAt_pi' (fun c => (hf c).2)
  exact aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero h0 hcont

/-- Scalar centered-continuity data for two finite real coordinate families is
enough to shrink to a neighborhood where their square-sums total at most `1`. -/
theorem aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
    {η κ α : Type*} [Fintype η] [Fintype κ] [TopologicalSpace α]
    {f : α → η → ℝ} {g : α → κ → ℝ} {x₀ : α}
    (hf : ∀ c, f x₀ c = 0 ∧ ContinuousAt (fun x : α => f x c) x₀)
    (hg : ∀ c, g x₀ c = 0 ∧ ContinuousAt (fun x : α => g x c) x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum (f x) + aoyagiCoordinateSquareSum (g x) ≤ 1 := by
  have hf0 : f x₀ = 0 := by
    funext c
    exact (hf c).1
  have hg0 : g x₀ = 0 := by
    funext c
    exact (hg c).1
  have hfcont : ContinuousAt f x₀ :=
    continuousAt_pi' (fun c => (hf c).2)
  have hgcont : ContinuousAt g x₀ :=
    continuousAt_pi' (fun c => (hg c).2)
  exact aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
    hf0 hg0 hfcont hgcont

/-- Scalar coordinates for the three regular block families
`Ctop - 1`, `F2`, and `F3`.

The type parameters are:
* `ι`: the rank-`r` through-coordinate index;
* `μ`: the row/left-endpoint residual-coordinate index;
* `ν`: the column/right-endpoint residual-coordinate index. -/
abbrev AoyagiRegularBlockCoordinateIndex
    (ι : Type uι) (μ : Type uμ) (ν : Type uν) :
    Type (max uι uμ uν) :=
  (ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι))

namespace AoyagiRegularBlockCoordinateIndex

variable {ι μ ν R α : Type*}

/-- The number of scalar regular coordinates is the sum of the three block
entry counts. -/
@[simp]
theorem card [Fintype ι] [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiRegularBlockCoordinateIndex ι μ ν) =
      Fintype.card ι * Fintype.card ι +
        Fintype.card ι * Fintype.card ν +
          Fintype.card μ * Fintype.card ι := by
  simp [AoyagiRegularBlockCoordinateIndex, add_assoc]

/-- The scalar value attached to a regular block coordinate. -/
def value
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    AoyagiRegularBlockCoordinateIndex ι μ ν → R
  | Sum.inl ij => X ij.1 ij.2
  | Sum.inr (Sum.inl ij) => F2 ij.1 ij.2
  | Sum.inr (Sum.inr ij) => F3 ij.1 ij.2

@[simp]
theorem value_ctop
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i j : ι) :
    value X F2 F3
        (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j)) = X i j :=
  rfl

@[simp]
theorem value_f2
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i : ι) (j : ν) :
    value X F2 F3
        (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j))) = F2 i j :=
  rfl

@[simp]
theorem value_f3
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (i : μ) (j : ι) :
    value X F2 F3
        (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j))) = F3 i j :=
  rfl

/-- Repackage the first regular scalar-coordinate block as the matrix
`Ctop - 1`. -/
def ctopMinusIdentityMatrix
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) : Matrix ι ι R :=
  fun i j ↦ coord (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j))

/-- Repackage the first regular scalar-coordinate block as `Ctop = 1 + X`,
where `X` is the stored `Ctop - 1` coordinate block. -/
def ctopMatrix [DecidableEq ι] [Add R] [Zero R] [One R]
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) : Matrix ι ι R :=
  1 + ctopMinusIdentityMatrix coord

/-- Repackage the second regular scalar-coordinate block as `F2`. -/
def f2Matrix
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) : Matrix ι ν R :=
  fun i j ↦ coord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j)))

/-- Repackage the third regular scalar-coordinate block as `F3`. -/
def f3Matrix
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) : Matrix μ ι R :=
  fun i j ↦ coord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j)))

@[simp]
theorem ctopMinusIdentityMatrix_apply
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) (i j : ι) :
    ctopMinusIdentityMatrix coord i j =
      coord (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j)) :=
  rfl

@[simp]
theorem ctopMatrix_sub_one [DecidableEq ι] [Ring R]
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) :
    ctopMatrix coord - 1 = ctopMinusIdentityMatrix coord := by
  ext i j
  simp [ctopMatrix]

@[simp]
theorem f2Matrix_apply
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) (i : ι) (j : ν) :
    f2Matrix coord i j =
      coord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j))) :=
  rfl

@[simp]
theorem f3Matrix_apply
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) (i : μ) (j : ι) :
    f3Matrix coord i j =
      coord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j))) :=
  rfl

/-- The three coordinate-block matrices recover the original scalar regular
coordinate family. -/
theorem value_coordinateMatrices
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) :
    value (ctopMinusIdentityMatrix coord) (f2Matrix coord) (f3Matrix coord) =
      coord := by
  funext c
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      rfl
  | inr rest =>
      cases rest with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          rfl
      | inr ij =>
          rcases ij with ⟨i, j⟩
          rfl

/-- Equivalently, every scalar regular-coordinate family is the readout of
some regular block triple. -/
theorem exists_value_eq
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) :
    ∃ (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R),
      value X F2 F3 = coord := by
  exact ⟨ctopMinusIdentityMatrix coord, f2Matrix coord, f3Matrix coord,
    value_coordinateMatrices coord⟩

/-- A Euclidean regular-coordinate vector can be read as regular block
matrices by applying the coordinate projections to its scalar entries. -/
theorem value_euclideanCoordinateMatrices
    (u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) :
    value (ctopMinusIdentityMatrix (fun c ↦ u c))
        (f2Matrix (fun c ↦ u c)) (f3Matrix (fun c ↦ u c)) =
      fun c ↦ u c := by
  simpa using value_coordinateMatrices (R := ℝ) (ι := ι) (μ := μ) (ν := ν)
    (fun c : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ u c)

/-- Using `Ctop = 1 + X`, where `X` is the first coordinate block, gives the
same Euclidean regular-coordinate readout through `Ctop - 1`. -/
theorem value_euclideanCtopMatrixCoordinateMatrices [DecidableEq ι]
    (u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) :
    value (ctopMatrix (fun c ↦ u c) - 1)
        (f2Matrix (fun c ↦ u c)) (f3Matrix (fun c ↦ u c)) =
      fun c ↦ u c := by
  simpa using value_euclideanCoordinateMatrices (ι := ι) (μ := μ) (ν := ν) u

/-- The `Ctop = 1 + X` block is a continuous function of Euclidean regular
coordinates. -/
theorem continuous_ctopMatrix_euclidean
    [DecidableEq ι] :
    Continuous
      (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
        ctopMatrix (fun c ↦ u c)) := by
  classical
  refine continuous_matrix fun i j ↦ ?_
  have hcoord :
      Continuous
        (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
          u (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j))) :=
    PiLp.continuous_apply
      (p := 2)
      (β := fun _ : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ ℝ)
      (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j))
  simpa [ctopMatrix, ctopMinusIdentityMatrix] using
    (continuous_const.add hcoord)

/-- The `F2` block is a continuous function of Euclidean regular
coordinates. -/
theorem continuous_f2Matrix_euclidean :
    Continuous
      (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
        f2Matrix (fun c ↦ u c)) := by
  refine continuous_matrix fun i j ↦ ?_
  have hcoord :
      Continuous
        (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
          u (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j)))) :=
    PiLp.continuous_apply
      (p := 2)
      (β := fun _ : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ ℝ)
      (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j)))
  simpa [f2Matrix] using hcoord

/-- The `F3` block is a continuous function of Euclidean regular
coordinates. -/
theorem continuous_f3Matrix_euclidean :
    Continuous
      (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
        f3Matrix (fun c ↦ u c)) := by
  refine continuous_matrix fun i j ↦ ?_
  have hcoord :
      Continuous
        (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
          u (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j)))) :=
    PiLp.continuous_apply
      (p := 2)
      (β := fun _ : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ ℝ)
      (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j)))
  simpa [f3Matrix] using hcoord

/-- The determinant of the `Ctop` block is continuous as a function of
Euclidean regular coordinates. -/
theorem continuous_det_ctopMatrix_euclidean
    [Fintype ι] [DecidableEq ι] :
    Continuous
      (fun u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν) ↦
        (ctopMatrix (fun c ↦ u c)).det) :=
  continuous_ctopMatrix_euclidean.matrix_det

@[simp]
theorem ctopMatrix_zero [DecidableEq ι] :
    ctopMatrix
        (fun _ : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ (0 : ℝ)) =
      (1 : Matrix ι ι ℝ) := by
  ext i j
  simp [ctopMatrix, ctopMinusIdentityMatrix]

@[simp]
theorem ctopMatrix_euclidean_zero [DecidableEq ι] :
    ctopMatrix
        (fun c ↦ (0 : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) c) =
      (1 : Matrix ι ι ℝ) := by
  simp

@[simp]
theorem det_ctopMatrix_zero [Fintype ι] [DecidableEq ι] :
    (ctopMatrix
        (fun _ : AoyagiRegularBlockCoordinateIndex ι μ ν ↦ (0 : ℝ))).det =
      (1 : ℝ) := by
  simp

@[simp]
theorem det_ctopMatrix_euclidean_zero [Fintype ι] [DecidableEq ι] :
    (ctopMatrix
        (fun c ↦ (0 : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) c)).det =
      (1 : ℝ) := by
  simp

/-- At the centered Euclidean regular coordinate, the `Ctop` determinant is a
unit. -/
theorem isUnit_det_ctopMatrix_euclidean_zero [Fintype ι] [DecidableEq ι] :
    IsUnit
      (ctopMatrix
        (fun c ↦ (0 : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) c)).det := by
  rw [det_ctopMatrix_euclidean_zero]
  exact isUnit_iff_ne_zero.2 one_ne_zero

/-- Near the centered Euclidean regular coordinate, the `Ctop` determinant
stays a unit. -/
theorem eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero
    [Fintype ι] [DecidableEq ι] :
    ∀ᶠ u in nhds (0 : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)),
      IsUnit (ctopMatrix (fun c ↦ u c)).det := by
  have hunit :
      IsUnit
        (ctopMatrix
          (fun c ↦
            (0 : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν)) c)).det :=
    isUnit_det_ctopMatrix_euclidean_zero
  exact continuous_det_ctopMatrix_euclidean.continuousAt.eventually
    (isOpen_setOf_isUnit.mem_nhds hunit)

/-- The unit determinant condition holds throughout some positive Euclidean
ball around the centered regular coordinate. -/
theorem exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean
    [Fintype ι] [Fintype μ] [Fintype ν] [DecidableEq ι] :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν),
        u ∈ Metric.ball 0 R → IsUnit (ctopMatrix (fun c ↦ u c)).det := by
  rcases Metric.mem_nhds_iff.1
      (eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero
        (ι := ι) (μ := μ) (ν := ν)) with
    ⟨R, hR, hRmem⟩
  exact ⟨R, hR, fun u hu ↦ hRmem hu⟩

/-- The unit determinant ball can be chosen below any prescribed positive
radius. -/
theorem exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
    [Fintype ι] [Fintype μ] [Fintype ν] [DecidableEq ι]
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∀ u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν),
        u ∈ Metric.ball 0 R → IsUnit (ctopMatrix (fun c ↦ u c)).det := by
  rcases exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean
      (ι := ι) (μ := μ) (ν := ν) with
    ⟨R₀, hR₀, hR₀unit⟩
  let R := min R₀ Rmax
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hR₀ hRmax
  have hR_le_R₀ : R ≤ R₀ := by
    dsimp [R]
    exact min_le_left _ _
  have hR_le_Rmax : R ≤ Rmax := by
    dsimp [R]
    exact min_le_right _ _
  refine ⟨R, hR, hR_le_Rmax, fun u hu ↦ ?_⟩
  exact hR₀unit u (Metric.ball_subset_ball hR_le_R₀ hu)

/-- The ideal generated by the scalar regular coordinates. -/
def entryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    Ideal R :=
  Ideal.span (Set.range (value X F2 F3))

/-- The scalar regular-coordinate ideal is exactly the regular block-entry
ideal. -/
theorem entryIdeal_eq_regularBlockEntryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    entryIdeal X F2 F3 = regularBlockEntryIdeal X F2 F3 := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    cases c with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        exact
          ((show matrixEntryIdeal X ≤ regularBlockEntryIdeal X F2 F3 from
            le_sup_left.trans le_sup_left) (matrixEntry_mem X i j))
    | inr rest =>
        cases rest with
        | inl ij =>
            rcases ij with ⟨i, j⟩
            exact
              ((show matrixEntryIdeal F2 ≤ regularBlockEntryIdeal X F2 F3 from
                le_sup_right.trans le_sup_left) (matrixEntry_mem F2 i j))
        | inr ij =>
            rcases ij with ⟨i, j⟩
            exact
              ((show matrixEntryIdeal F3 ≤ regularBlockEntryIdeal X F2 F3 from
                le_sup_right) (matrixEntry_mem F3 i j))
  · unfold regularBlockEntryIdeal
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [matrixEntryIdeal, Ideal.span_le]
        rintro _ ⟨⟨i, j⟩, rfl⟩
        exact
          Ideal.subset_span
            ⟨Sum.inl (β := (ι × ν) ⊕ (μ × ι)) (i, j), rfl⟩
      · rw [matrixEntryIdeal, Ideal.span_le]
        rintro _ ⟨⟨i, j⟩, rfl⟩
        exact
          Ideal.subset_span
            ⟨Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) (i, j)), rfl⟩
    · rw [matrixEntryIdeal, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact
        Ideal.subset_span
          ⟨Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) (i, j)), rfl⟩

/-- A blockwise centered-continuity package projects to every scalar regular
coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (X : α → Matrix ι ι R)
    (F2 : α → Matrix ι ν R)
    (F3 : α → Matrix μ ι R)
    (hX0 : X x₀ = 0) (hF20 : F2 x₀ = 0) (hF30 : F3 x₀ = 0)
    (hX : ContinuousAt X x₀)
    (hF2 : ContinuousAt F2 x₀)
    (hF3 : ContinuousAt F3 x₀) :
    ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
      value (X x₀) (F2 x₀) (F3 x₀) c = 0 ∧
        ContinuousAt
          (fun x : α => value (X x) (F2 x) (F3 x) c) x₀ := by
  intro c
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      constructor
      · simp [value, hX0]
      · exact
          ((continuous_apply j).continuousAt.comp
            ((continuous_apply i).continuousAt.comp hX))
  | inr rest =>
      cases rest with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          constructor
          · simp [value, hF20]
          · exact
              ((continuous_apply j).continuousAt.comp
                ((continuous_apply i).continuousAt.comp hF2))
      | inr ij =>
          rcases ij with ⟨i, j⟩
          constructor
          · simp [value, hF30]
          · exact
              ((continuous_apply j).continuousAt.comp
                ((continuous_apply i).continuousAt.comp hF3))

/-- The regular-coordinate square-sum splits into the three displayed p. 13
regular block square-sums. -/
theorem coordinateSquareSum_eq_ctop_add_f2_add_f3
    [CommSemiring R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (value X F2 F3) =
      aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2) +
        (aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)) := by
  simp [aoyagiCoordinateSquareSum, value, Fintype.sum_sum_type]

/-- The `F2` square-sum is bounded by the full regular-coordinate square-sum. -/
theorem f2SquareSum_le_regularSquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (value X F2 F3) := by
  let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsplit : aoyagiCoordinateSquareSum (value X F2 F3) = SX + (SF2 + SF3) := by
    simpa [SX, SF2, SF3] using coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
  have hSX : 0 ≤ SX := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
  have hSF3 : 0 ≤ SF3 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : μ × ι => F3 ij.1 ij.2)
  rw [hsplit]
  nlinarith

/-- The `F3` square-sum is bounded by the full regular-coordinate square-sum. -/
theorem f3SquareSum_le_regularSquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum (value X F2 F3) := by
  let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsplit : aoyagiCoordinateSquareSum (value X F2 F3) = SX + (SF2 + SF3) := by
    simpa [SX, SF2, SF3] using coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
  have hSX : 0 ≤ SX := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
  have hSF2 : 0 ≤ SF2 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ν => F2 ij.1 ij.2)
  rw [hsplit]
  nlinarith

/-- The `F2` plus `F3` square-sums are bounded by the full regular-coordinate
square-sum for an arbitrary scalar regular-coordinate family. -/
theorem f2_f3_squareSum_add_le_coordinateSquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (coord : AoyagiRegularBlockCoordinateIndex ι μ ν → R) :
    aoyagiCoordinateSquareSum
        (fun ij : ι × ν =>
          coord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
      aoyagiCoordinateSquareSum
        (fun ij : μ × ι =>
          coord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
        aoyagiCoordinateSquareSum coord := by
  let SX :=
    aoyagiCoordinateSquareSum
      (fun ij : ι × ι =>
        coord (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) ij))
  let SF2 :=
    aoyagiCoordinateSquareSum
      (fun ij : ι × ν =>
        coord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij)))
  let SF3 :=
    aoyagiCoordinateSquareSum
      (fun ij : μ × ι =>
        coord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij)))
  have hsplit : aoyagiCoordinateSquareSum coord = SX + (SF2 + SF3) := by
    simp [aoyagiCoordinateSquareSum, SX, SF2, SF3, Fintype.sum_sum_type]
  have hSX : 0 ≤ SX := by
    exact aoyagiCoordinateSquareSum_nonneg
      (fun ij : ι × ι =>
        coord (Sum.inl (β := (ι × ν) ⊕ (μ × ι)) ij))
  rw [hsplit]
  nlinarith

/-- Centered continuity of all scalar regular coordinates gives a neighborhood
where the `F2` and `F3` square-sums have total at most `1`. -/
theorem f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
    [Fintype ι] [Fintype μ] [Fintype ν] [TopologicalSpace α]
    {coord : α → AoyagiRegularBlockCoordinateIndex ι μ ν → ℝ} {x₀ : α}
    (hcoord :
      ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
        coord x₀ c = 0 ∧ ContinuousAt (fun x : α => coord x c) x₀) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            coord x (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            coord x (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  exact
    aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
      (fun ij : ι × ν =>
        hcoord (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij)))
      (fun ij : μ × ι =>
        hcoord (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij)))

/-- The abstract scalar regular-coordinate count matches Aoyagi's p. 13 count
once the three index-cardinalities are identified with `r`, `H(L+1)-r`, and
`H(1)-r`.

This is only finite cardinal arithmetic.  The endpoint cardinality
identifications are separate source/geometric obligations. -/
theorem card_eq_aoyagiTheorem2RegularVariableCount
    [Fintype ι] [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hι : Fintype.card ι = r)
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r) :
    Fintype.card (AoyagiRegularBlockCoordinateIndex ι μ ν) =
      aoyagiTheorem2RegularVariableCount L H r := by
  rw [card, hι, hμ, hν]
  simp [aoyagiTheorem2RegularVariableCount, add_assoc]

end AoyagiRegularBlockCoordinateIndex

/-- Scalar coordinates for the residual `D` block in Aoyagi's p. 13
product-difference split. -/
abbrev AoyagiResidualBlockCoordinateIndex (μ : Type uμ) (ν : Type uν) :
    Type (max uμ uν) :=
  μ × ν

namespace AoyagiResidualBlockCoordinateIndex

variable {μ ν R α : Type*}

/-- The number of scalar residual coordinates is the entry count of the
residual block. -/
@[simp]
theorem card [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiResidualBlockCoordinateIndex μ ν) =
      Fintype.card μ * Fintype.card ν := by
  simp [AoyagiResidualBlockCoordinateIndex]

/-- The scalar value attached to a residual block coordinate. -/
def value (D : Matrix μ ν R) :
    AoyagiResidualBlockCoordinateIndex μ ν → R
  | ij => D ij.1 ij.2

@[simp]
theorem value_apply (D : Matrix μ ν R) (i : μ) (j : ν) :
    value D (i, j) = D i j :=
  rfl

/-- Repackage a scalar residual-coordinate family as a residual matrix. -/
def matrix (coord : AoyagiResidualBlockCoordinateIndex μ ν → R) :
    Matrix μ ν R :=
  fun i j ↦ coord (i, j)

@[simp]
theorem matrix_apply
    (coord : AoyagiResidualBlockCoordinateIndex μ ν → R) (i : μ) (j : ν) :
    matrix coord i j = coord (i, j) :=
  rfl

/-- The residual matrix reconstructed from scalar residual coordinates reads
back as the original scalar coordinate family. -/
theorem value_matrix
    (coord : AoyagiResidualBlockCoordinateIndex μ ν → R) :
    value (matrix coord) = coord := by
  funext c
  rcases c with ⟨i, j⟩
  rfl

/-- Equivalently, every scalar residual-coordinate family is the readout of
some residual matrix. -/
theorem exists_value_eq
    (coord : AoyagiResidualBlockCoordinateIndex μ ν → R) :
    ∃ D : Matrix μ ν R, value D = coord :=
  ⟨matrix coord, value_matrix coord⟩

/-- The ideal generated by the scalar residual coordinates. -/
def entryIdeal [CommRing R] (D : Matrix μ ν R) : Ideal R :=
  Ideal.span (Set.range (value D))

/-- The scalar residual-coordinate ideal is exactly the residual matrix-entry
ideal. -/
theorem entryIdeal_eq_matrixEntryIdeal [CommRing R] (D : Matrix μ ν R) :
    entryIdeal D = matrixEntryIdeal D := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    rcases c with ⟨i, j⟩
    exact matrixEntry_mem D i j
  · rw [matrixEntryIdeal, Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Ideal.subset_span ⟨(i, j), rfl⟩

/-- A centered-continuous residual block projects to every scalar residual
coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (D : α → Matrix μ ν R)
    (hD0 : D x₀ = 0)
    (hD : ContinuousAt D x₀) :
    ∀ c : AoyagiResidualBlockCoordinateIndex μ ν,
      value (D x₀) c = 0 ∧
        ContinuousAt (fun x : α => value (D x) c) x₀ := by
  intro c
  rcases c with ⟨i, j⟩
  constructor
  · simp [value, hD0]
  · exact
      ((continuous_apply j).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hD))

/-- The endpoint residual block entry count is the product of the two endpoint
residual dimensions. -/
theorem card_eq_endpointResidualEntryCount
    [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r) :
    Fintype.card (AoyagiResidualBlockCoordinateIndex μ ν) =
      (H 1 - r) * (H (L + 1) - r) := by
  rw [card, hμ, hν]

end AoyagiResidualBlockCoordinateIndex

/-- Scalar coordinates for the cleaned p. 13 product-difference ideal family:
the three regular blocks together with the residual `D` block. -/
abbrev AoyagiProductDifferenceCoordinateIndex
    (ι : Type uι) (μ : Type uμ) (ν : Type uν) :
    Type (max uι uμ uν) :=
  AoyagiRegularBlockCoordinateIndex ι μ ν ⊕
    AoyagiResidualBlockCoordinateIndex μ ν

namespace AoyagiProductDifferenceCoordinateIndex

variable {ι μ ν R α : Type*}

@[simp]
theorem card [Fintype ι] [Fintype μ] [Fintype ν] :
    Fintype.card (AoyagiProductDifferenceCoordinateIndex ι μ ν) =
      Fintype.card ι * Fintype.card ι +
        Fintype.card ι * Fintype.card ν +
          Fintype.card μ * Fintype.card ι +
            Fintype.card μ * Fintype.card ν := by
  simp [AoyagiProductDifferenceCoordinateIndex, AoyagiRegularBlockCoordinateIndex,
    AoyagiResidualBlockCoordinateIndex, add_assoc]

/-- The scalar value attached to a full product-difference coordinate. -/
def value
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    AoyagiProductDifferenceCoordinateIndex ι μ ν → R
  | Sum.inl c => AoyagiRegularBlockCoordinateIndex.value X F2 F3 c
  | Sum.inr c => AoyagiResidualBlockCoordinateIndex.value D c

/-- The scalar value attached to the literal signed/corrected p. 13
product-difference block
`fromBlocks X (-F2) (-F3) (D - F3 * F2)`. -/
def literalValue [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    AoyagiProductDifferenceCoordinateIndex ι μ ν → R
  | Sum.inl c => AoyagiRegularBlockCoordinateIndex.value X (-F2) (-F3) c
  | Sum.inr c => AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2) c

@[simp]
theorem value_regular
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiRegularBlockCoordinateIndex ι μ ν) :
    value X F2 F3 D (Sum.inl c) =
      AoyagiRegularBlockCoordinateIndex.value X F2 F3 c :=
  rfl

@[simp]
theorem value_residual
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    value X F2 F3 D (Sum.inr c) =
      AoyagiResidualBlockCoordinateIndex.value D c :=
  rfl

/-- If the regular blocks are reconstructed from a Euclidean coordinate vector,
the full cleaned product-difference readout has regular part `u` and residual
part `value D`. -/
theorem value_euclideanCtopMatrixCoordinateMatrices_residual [DecidableEq ι]
    (u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν))
    (D : Matrix μ ν ℝ) :
    value
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c) - 1)
        (AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c ↦ u c))
        (AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c ↦ u c)) D =
      Sum.elim (fun c ↦ u c) (AoyagiResidualBlockCoordinateIndex.value D) := by
  funext c
  cases c with
  | inl c =>
      simpa [value] using
        congrFun
          (AoyagiRegularBlockCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices
            (ι := ι) (μ := μ) (ν := ν) u) c
  | inr c =>
      rfl

@[simp]
theorem literalValue_regular [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiRegularBlockCoordinateIndex ι μ ν) :
    literalValue X F2 F3 D (Sum.inl c) =
      AoyagiRegularBlockCoordinateIndex.value X (-F2) (-F3) c :=
  rfl

@[simp]
theorem literalValue_residual [CommRing R] [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (c : AoyagiResidualBlockCoordinateIndex μ ν) :
    literalValue X F2 F3 D (Sum.inr c) =
      AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2) c :=
  rfl

/-- The ideal generated by the scalar product-difference coordinates. -/
def entryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) : Ideal R :=
  Ideal.span (Set.range (value X F2 F3 D))

/-- The scalar product-difference coordinate ideal is exactly the four-block
entry ideal from Aoyagi's p. 13 product-difference split. -/
theorem entryIdeal_eq_fourMatrixEntryIdeal [CommRing R]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    entryIdeal X F2 F3 D = fourMatrixEntryIdeal X F2 F3 D := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    cases c with
    | inl c =>
        have hreg :
            AoyagiRegularBlockCoordinateIndex.value X F2 F3 c ∈
              regularBlockEntryIdeal X F2 F3 := by
          rw [← AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]
          exact Ideal.subset_span ⟨c, rfl⟩
        exact
          (show regularBlockEntryIdeal X F2 F3 ≤ fourMatrixEntryIdeal X F2 F3 D from
            le_sup_left) hreg
    | inr c =>
        have hres :
            AoyagiResidualBlockCoordinateIndex.value D c ∈ matrixEntryIdeal D := by
          rw [← AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal]
          exact Ideal.subset_span ⟨c, rfl⟩
        exact
          (show matrixEntryIdeal D ≤ fourMatrixEntryIdeal X F2 F3 D from
            le_sup_right) hres
  · unfold fourMatrixEntryIdeal
    refine sup_le ?_ ?_
    · rw [← AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]
      rw [AoyagiRegularBlockCoordinateIndex.entryIdeal, entryIdeal, Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      exact Ideal.subset_span ⟨Sum.inl c, rfl⟩
    · rw [← AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal]
      rw [AoyagiResidualBlockCoordinateIndex.entryIdeal, entryIdeal, Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      exact Ideal.subset_span ⟨Sum.inr c, rfl⟩

/-- The literal signed p. 13 product-difference block generates the scalar
product-difference coordinate ideal. -/
theorem matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal [CommRing R]
    [Fintype ι]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2)) =
      entryIdeal X F2 F3 D := by
  calc
    matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2)) =
        fourMatrixEntryIdeal X F2 F3 D :=
      matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal
        X F2 F3 D
    _ = entryIdeal X F2 F3 D :=
      (entryIdeal_eq_fourMatrixEntryIdeal X F2 F3 D).symm

/-- Centered continuity of the regular and residual blocks combines into
centered continuity for every product-difference scalar coordinate. -/
theorem value_centered_continuousAt
    [Zero R] [TopologicalSpace α] [TopologicalSpace R]
    {x₀ : α}
    (X : α → Matrix ι ι R)
    (F2 : α → Matrix ι ν R)
    (F3 : α → Matrix μ ι R)
    (D : α → Matrix μ ν R)
    (hX0 : X x₀ = 0) (hF20 : F2 x₀ = 0) (hF30 : F3 x₀ = 0)
    (hD0 : D x₀ = 0)
    (hX : ContinuousAt X x₀)
    (hF2 : ContinuousAt F2 x₀)
    (hF3 : ContinuousAt F3 x₀)
    (hD : ContinuousAt D x₀) :
    ∀ c : AoyagiProductDifferenceCoordinateIndex ι μ ν,
      value (X x₀) (F2 x₀) (F3 x₀) (D x₀) c = 0 ∧
        ContinuousAt
          (fun x : α => value (X x) (F2 x) (F3 x) (D x) c) x₀ := by
  intro c
  cases c with
  | inl c =>
      exact
        AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
          X F2 F3 hX0 hF20 hF30 hX hF2 hF3 c
  | inr c =>
      exact
        AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
          D hD0 hD c

/-- The cleaned product-difference coordinate square-sum splits into the
regular-coordinate square-sum plus the residual-coordinate square-sum. -/
theorem coordinateSquareSum_eq_regular_add_residual
    [CommSemiring R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) =
      aoyagiCoordinateSquareSum (AoyagiRegularBlockCoordinateIndex.value X F2 F3) +
        aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) := by
  simp [aoyagiCoordinateSquareSum, value, Fintype.sum_sum_type]

/-- The literal signed/corrected p. 13 product-difference square-sum splits
as the regular block square-sum plus the corrected residual square-sum.

This only expands the finite scalar family
`X, -F2, -F3, D - F3 * F2`; it does not compare this loss with the cleaned
family `X, F2, F3, D`. -/
theorem literalCoordinateSquareSum_eq_regular_add_correctedResidual
    [CommRing R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) =
      aoyagiCoordinateSquareSum (AoyagiRegularBlockCoordinateIndex.value X F2 F3) +
        aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) := by
  simp [aoyagiCoordinateSquareSum, literalValue, AoyagiRegularBlockCoordinateIndex.value,
    AoyagiResidualBlockCoordinateIndex.value, Fintype.sum_sum_type]

/-- The literal p. 13 product-difference square-sum is the entry square-sum of
the displayed signed/corrected block matrix. -/
theorem literalCoordinateSquareSum_eq_fromBlocks_neg_neg_sub_mul
    [CommRing R] [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) =
      aoyagiCoordinateSquareSum
        (fun ij : (ι ⊕ μ) × (ι ⊕ ν) =>
          (fromBlocks X (-F2) (-F3) (D - F3 * F2)) ij.1 ij.2) := by
  simp [aoyagiCoordinateSquareSum, literalValue, AoyagiRegularBlockCoordinateIndex.value,
    AoyagiResidualBlockCoordinateIndex.value, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Finset.sum_add_distrib]
  abel

/-- Quantitative p. 13 triangular-multiplier comparison.

If triangular endpoint multipliers transform `T` to the p. 13 block-diagonal
form and the product of their coordinate square-sums is bounded by `K`, then a
constant `c` with `c*K <= 1` times the literal p. 13 square-sum is bounded by
the untransformed product-difference square-sum. -/
theorem const_mul_literalCoordinateSquareSum_le_productDifferenceSquareSum_of_triangularBlockProduct
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (Ctop : Matrix ι ι R) (D : Matrix μ ν R)
    (T : Matrix (ι ⊕ μ) (ι ⊕ ν) R)
    {c K : R}
    (hc_nonneg : 0 ≤ c) (hcK : c * K ≤ 1)
    (hbound :
      aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ μ) × (ι ⊕ μ) =>
              (fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R))
                ij.1 ij.2) *
          aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ ν) × (ι ⊕ ν) =>
              (fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R))
                ij.1 ij.2) ≤ K)
    (htri :
      fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R) * T *
        fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R) =
          fromBlocks Ctop 0 0 D) :
    c * aoyagiCoordinateSquareSum (literalValue (Ctop - 1) F2 F3 D) ≤
      aoyagiCoordinateSquareSum
        (fun ij : (ι ⊕ μ) × (ι ⊕ ν) =>
          (T - fromBlocks (1 : Matrix ι ι R) 0
            (0 : Matrix μ ι R) (0 : Matrix μ ν R)) ij.1 ij.2) := by
  classical
  let L : Matrix (ι ⊕ μ) (ι ⊕ μ) R :=
    fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R)
  let Rmat : Matrix (ι ⊕ ν) (ι ⊕ ν) R :=
    fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R)
  let T0 : Matrix (ι ⊕ μ) (ι ⊕ ν) R :=
    fromBlocks (1 : Matrix ι ι R) 0 (0 : Matrix μ ι R) (0 : Matrix μ ν R)
  let Tlit : Matrix (ι ⊕ μ) (ι ⊕ ν) R :=
    fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2)
  have hdiff : L * (T - T0) * Rmat = Tlit := by
    simpa [L, Rmat, T0, Tlit] using
      triangularBlockProductDifference_fromBlocks_indexed F2 F3 Ctop D T htri
  have hlit :
      aoyagiCoordinateSquareSum (literalValue (Ctop - 1) F2 F3 D) =
        aoyagiCoordinateSquareSum
          (fun ij : (ι ⊕ μ) × (ι ⊕ ν) => Tlit ij.1 ij.2) := by
    simpa [Tlit] using
      literalCoordinateSquareSum_eq_fromBlocks_neg_neg_sub_mul
        (Ctop - 1) F2 F3 D
  have hraw :
      c * aoyagiCoordinateSquareSum
          (fun ij : (ι ⊕ μ) × (ι ⊕ ν) => Tlit ij.1 ij.2) ≤
        aoyagiCoordinateSquareSum
          (fun ij : (ι ⊕ μ) × (ι ⊕ ν) => (T - T0) ij.1 ij.2) := by
    refine
      const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
        (L := L) (M := T - T0) (Rmat := Rmat) (T := Tlit)
        (c := c) (K := K) hc_nonneg hcK ?_ hdiff
    simpa [L, Rmat] using hbound
  simpa [hlit, T0] using hraw

/-- The corrected residual square-sum is bounded by twice the cleaned residual
square-sum plus twice the product-correction square-sum.

This is a finite ordered-ring estimate only. -/
theorem correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) ≤
      2 * aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) +
        2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) := by
  simpa [AoyagiResidualBlockCoordinateIndex.value] using
    (aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
      (AoyagiResidualBlockCoordinateIndex.value D)
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)))

/-- The cleaned residual square-sum is bounded by twice the corrected residual
square-sum plus twice the product-correction square-sum.

This is the reverse finite estimate needed for two-sided comparison. -/
theorem residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) (D : Matrix μ ν R) :
    aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value D) ≤
      2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2)) +
        2 * aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) := by
  simpa [AoyagiResidualBlockCoordinateIndex.value] using
    (aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)))

/-- Frobenius-style finite matrix-product estimate for the p. 13 product
correction. -/
theorem productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R) :
    aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
      aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) *
        aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) := by
  classical
  unfold aoyagiCoordinateSquareSum AoyagiResidualBlockCoordinateIndex.value
  calc
    ∑ ij : μ × ν, (F3 * F2) ij.1 ij.2 ^ 2 ≤
        ∑ ij : μ × ν,
          (∑ k : ι, F3 ij.1 k ^ 2) * ∑ k : ι, F2 k ij.2 ^ 2 := by
      exact Finset.sum_le_sum (fun ij _ => by
        simpa [Matrix.mul_apply] using
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
            (fun k => F3 ij.1 k) (fun k => F2 k ij.2)))
    _ =
        (∑ ij : μ × ι, F3 ij.1 ij.2 ^ 2) *
          ∑ ij : ι × ν, F2 ij.1 ij.2 ^ 2 := by
      simp only [Fintype.sum_prod_type]
      calc
        ∑ i : μ, ∑ j : ν,
            (∑ k : ι, F3 i k ^ 2) * ∑ k : ι, F2 k j ^ 2 =
            ∑ i : μ, (∑ k : ι, F3 i k ^ 2) *
              ∑ j : ν, ∑ k : ι, F2 k j ^ 2 := by
          simp [Finset.mul_sum]
        _ =
            (∑ i : μ, ∑ k : ι, F3 i k ^ 2) *
              ∑ j : ν, ∑ k : ι, F2 k j ^ 2 := by
          rw [Finset.sum_mul]
        _ =
            (∑ i : μ, ∑ k : ι, F3 i k ^ 2) *
              ∑ k : ι, ∑ j : ν, F2 k j ^ 2 := by
          have hcomm :
              (∑ j : ν, ∑ k : ι, F2 k j ^ 2) =
                ∑ k : ι, ∑ j : ν, F2 k j ^ 2 := by
            rw [Finset.sum_comm]
          rw [hcomm]

/-- If the `F2` and `F3` square-sums are small, then the product correction is
controlled by one quarter of the regular-coordinate square-sum. -/
theorem four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    4 * aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
      aoyagiCoordinateSquareSum
        (AoyagiRegularBlockCoordinateIndex.value X F2 F3) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let SF2 := aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2)
  let SF3 := aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hP : P ≤ SF3 * SF2 := by
    simpa [P, SF2, SF3] using
      productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum F2 F3
  have hSF20 : 0 ≤ SF2 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ν => F2 ij.1 ij.2)
  have hSF30 : 0 ≤ SF3 := by
    exact aoyagiCoordinateSquareSum_nonneg (fun ij : μ × ι => F3 ij.1 ij.2)
  have hsum_small : SF2 + SF3 ≤ 1 := by
    simpa [SF2, SF3] using hsmall
  have hfour_prod : 4 * (SF3 * SF2) ≤ SF2 + SF3 := by
    have hfour_le_sq : 4 * SF3 * SF2 ≤ (SF2 + SF3) ^ 2 := by
      nlinarith [sq_nonneg (SF2 - SF3)]
    have hsumsq_le : (SF2 + SF3) ^ 2 ≤ SF2 + SF3 := by
      nlinarith
    nlinarith
  have hsum_le_A : SF2 + SF3 ≤ A := by
    let SX := aoyagiCoordinateSquareSum (fun ij : ι × ι => X ij.1 ij.2)
    have hsplit : A = SX + (SF2 + SF3) := by
      simpa [A, SX, SF2, SF3] using
        AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3 X F2 F3
    have hSX : 0 ≤ SX := by
      exact aoyagiCoordinateSquareSum_nonneg (fun ij : ι × ι => X ij.1 ij.2)
    rw [hsplit]
    nlinarith
  nlinarith

/-- Conditional finite comparison: if the product correction `F3 * F2` is
controlled by the regular square-sum, then the literal p. 13 square-sum is at
most three times the cleaned square-sum.

This theorem does not prove the required local small-neighborhood control of
`F3 * F2`; it only records the finite algebra once that control is supplied. -/
theorem literalCoordinateSquareSum_le_three_mul_coordinateSquareSum_of_product_le_regular
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hproduct :
      aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
        aoyagiCoordinateSquareSum
          (AoyagiRegularBlockCoordinateIndex.value X F2 F3)) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) ≤
      3 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hE : E ≤ 2 * B + 2 * P := by
    simpa [E, B, P] using
      correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product F2 F3 D
  have hP : P ≤ A := by
    simpa [A, P] using hproduct
  have hB0 : 0 ≤ B := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value D)
  calc
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) = A + E := by
      simpa [A, E] using
        literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D
    _ ≤ A + (2 * B + 2 * P) := by
      linarith
    _ ≤ A + (2 * B + 2 * A) := by
      linarith
    _ ≤ 3 * (A + B) := by
      nlinarith
    _ = 3 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
      rw [coordinateSquareSum_eq_regular_add_residual X F2 F3 D]

/-- Conditional finite comparison in the reverse direction: under the same
product-control hypothesis, the cleaned square-sum is at most three times the
literal p. 13 square-sum. -/
theorem coordinateSquareSum_le_three_mul_literalCoordinateSquareSum_of_product_le_regular
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hproduct :
      aoyagiCoordinateSquareSum
          (AoyagiResidualBlockCoordinateIndex.value (F3 * F2)) ≤
        aoyagiCoordinateSquareSum
          (AoyagiRegularBlockCoordinateIndex.value X F2 F3)) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) ≤
      3 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hB : B ≤ 2 * E + 2 * P := by
    simpa [B, E, P] using
      residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product F2 F3 D
  have hP : P ≤ A := by
    simpa [A, P] using hproduct
  have hE0 : 0 ≤ E := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  calc
    aoyagiCoordinateSquareSum (value X F2 F3 D) = A + B := by
      simpa [A, B] using
        coordinateSquareSum_eq_regular_add_residual X F2 F3 D
    _ ≤ A + (2 * E + 2 * P) := by
      linarith
    _ ≤ A + (2 * E + 2 * A) := by
      linarith
    _ ≤ 3 * (A + E) := by
      nlinarith
    _ = 3 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
      rw [literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D]

/-- Small-neighborhood finite comparison: if the sum of the `F2` and `F3`
regular square-sums is at most `1`, then the literal p. 13 square-sum is
bounded by twice the cleaned square-sum. -/
theorem literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) ≤
      2 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hE : E ≤ 2 * B + 2 * P := by
    simpa [E, B, P] using
      correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product F2 F3 D
  have hP4 : 4 * P ≤ A := by
    simpa [P, A] using
      four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
        X F2 F3 hsmall
  have hP0 : 0 ≤ P := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hA0 : 0 ≤ A := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  calc
    aoyagiCoordinateSquareSum (literalValue X F2 F3 D) = A + E := by
      simpa [A, E] using
        literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D
    _ ≤ A + (2 * B + 2 * P) := by
      linarith
    _ ≤ 2 * (A + B) := by
      nlinarith
    _ = 2 * aoyagiCoordinateSquareSum (value X F2 F3 D) := by
      rw [coordinateSquareSum_eq_regular_add_residual X F2 F3 D]

/-- Reverse small-neighborhood finite comparison: if the sum of the `F2` and
`F3` regular square-sums is at most `1`, then the cleaned square-sum is bounded
by twice the literal p. 13 square-sum. -/
theorem coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype ι] [Fintype μ] [Fintype ν]
    (X : Matrix ι ι R) (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (D : Matrix μ ν R)
    (hsmall :
      aoyagiCoordinateSquareSum (fun ij : ι × ν => F2 ij.1 ij.2) +
          aoyagiCoordinateSquareSum (fun ij : μ × ι => F3 ij.1 ij.2) ≤
        1) :
    aoyagiCoordinateSquareSum (value X F2 F3 D) ≤
      2 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
  let A :=
    aoyagiCoordinateSquareSum
      (AoyagiRegularBlockCoordinateIndex.value X F2 F3)
  let B :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value D)
  let P :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  let E :=
    aoyagiCoordinateSquareSum
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  have hB : B ≤ 2 * E + 2 * P := by
    simpa [B, E, P] using
      residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product F2 F3 D
  have hP4 : 4 * P ≤ A := by
    simpa [P, A] using
      four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
        X F2 F3 hsmall
  have hP0 : 0 ≤ P := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (F3 * F2))
  have hE0 : 0 ≤ E := by
    exact aoyagiCoordinateSquareSum_nonneg
      (AoyagiResidualBlockCoordinateIndex.value (D - F3 * F2))
  calc
    aoyagiCoordinateSquareSum (value X F2 F3 D) = A + B := by
      simpa [A, B] using
        coordinateSquareSum_eq_regular_add_residual X F2 F3 D
    _ ≤ A + (2 * E + 2 * P) := by
      linarith
    _ ≤ 2 * (A + E) := by
      nlinarith
    _ = 2 * aoyagiCoordinateSquareSum (literalValue X F2 F3 D) := by
      rw [literalCoordinateSquareSum_eq_regular_add_correctedResidual X F2 F3 D]

/-- The cleaned p. 13 product-difference scalar-coordinate count is the
endpoint product entry count. -/
theorem card_eq_endpointProductEntryCount
    [Fintype ι] [Fintype μ] [Fintype ν]
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hι : Fintype.card ι = r)
    (hμ : Fintype.card μ = H 1 - r)
    (hν : Fintype.card ν = H (L + 1) - r)
    (hsource : r ≤ H 1) (htarget : r ≤ H (L + 1)) :
    Fintype.card (AoyagiProductDifferenceCoordinateIndex ι μ ν) =
      H 1 * H (L + 1) := by
  rw [card, hι, hμ, hν]
  have hsource_decomp : H 1 = r + (H 1 - r) := by omega
  have htarget_decomp : H (L + 1) = r + (H (L + 1) - r) := by omega
  calc
    r * r + r * (H (L + 1) - r) + (H 1 - r) * r +
        (H 1 - r) * (H (L + 1) - r) =
        (r + (H 1 - r)) * (r + (H (L + 1) - r)) := by
      ring
    _ = H 1 * H (L + 1) := by
      rw [← hsource_decomp, ← htarget_decomp]

end AoyagiProductDifferenceCoordinateIndex

section FixedBaseCanonicalCertificate

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module K (W i)]
  [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible complement at a reversed vertex has dimension
`dim vertex - rank`, where the rank is `finrank U₀`.

This is the finite-dimensional complement count behind the p. 13 endpoint
residual block sizes. -/
theorem paperEndpointEndpointComplementIndex_card_eq_layerSubRank
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (j : Fin (N + 1)) :
    Fintype.card
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ j) =
      Module.finrank K (reverseVertex W j) - Module.finrank K U₀ := by
  classical
  let hUrev :=
    isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀
  have hcompl :
      IsCompl (throughSubspace (reverseVertex W) (reverseEdge W B) U₀ j)
        (throughSubspaceEndpointComplement
          (reverseVertex W) (reverseEdge W B) U₀ j) :=
    throughSubspace_isCompl_endpointComplement
      (reverseVertex W) (reverseEdge W B) U₀ hUrev j
  have hfactor :
      chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
          ((Fin.zero_le j).trans j.le_last) =
        (chainMap (reverseVertex W) (reverseEdge W B) j (Fin.last N) j.le_last).comp
          (chainMap (reverseVertex W) (reverseEdge W B) 0 j (Fin.zero_le j)) :=
    chainMap_zero_last_eq_suffix_comp_prefix (reverseVertex W) (reverseEdge W B) j
  have hdisj :
      Disjoint U₀
        (LinearMap.ker
          ((chainMap (reverseVertex W) (reverseEdge W B) j (Fin.last N) j.le_last).comp
            (chainMap (reverseVertex W) (reverseEdge W B) 0 j (Fin.zero_le j)))) := by
    simpa [← hfactor] using hUrev.disjoint
  have hthrough :
      Module.finrank K
          (throughSubspace (reverseVertex W) (reverseEdge W B) U₀ j) =
        Module.finrank K U₀ :=
    finrank_throughSubspace_eq_of_disjoint_ker_comp
      (reverseVertex W) (reverseEdge W B) U₀ j hdisj
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  have hcard :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ j) =
        Module.finrank K
          (throughSubspaceEndpointComplement
            (reverseVertex W) (reverseEdge W B) U₀ j) := by
    simp [throughSubspaceEndpointComplementIndex]
  rw [hcard]
  omega

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible scalar regular-coordinate index has exactly
Aoyagi's p. 13 regular-variable count, once the base product rank and layer
dimension convention are supplied. -/
theorem paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r := by
  classical
  have hU :
      Fintype.card (Fin (Module.finrank K U₀)) = r := by
    simp [(paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range,
      hprod]
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  exact
    AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount
      (ι := Fin (Module.finrank K U₀))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hU hsource htarget

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible residual scalar-coordinate index has the product
of the row/left and column/right residual endpoint dimensions. -/
theorem paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r) := by
  classical
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  exact
    AoyagiResidualBlockCoordinateIndex.card_eq_endpointResidualEntryCount
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hsource htarget

omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The endpoint-compatible full product-difference scalar-coordinate index
has exactly the number of entries in an `H 1` by `H(N+1)` endpoint product. -/
theorem paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {H : ℕ → ℕ} {r : ℕ}
    (hprod : Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1) := by
  classical
  have hU :
      Fintype.card (Fin (Module.finrank K U₀)) = r := by
    simp [(paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range,
      hprod]
  have htarget :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) =
        H (N + 1) - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ 0]
    have hvertex :
        Module.finrank K (reverseVertex W 0) = H (N + 1) := by
      simpa [reverseVertex] using (hH (Fin.last N)).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource :
      Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) =
        H 1 - r := by
    rw [paperEndpointEndpointComplementIndex_card_eq_layerSubRank W B U₀ hU₀ (Fin.last N)]
    have hvertex :
        Module.finrank K (reverseVertex W (Fin.last N)) = H 1 := by
      have hrev : (Fin.last N).rev = (0 : Fin (N + 1)) := by
        simp
      change Module.finrank K (W ((Fin.last N).rev)) = H 1
      rw [hrev]
      exact (hH (0 : Fin (N + 1))).symm
    have hUfin :
        Module.finrank K U₀ = r :=
      (paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀).finrank_eq_range.trans hprod
    rw [hvertex, hUfin]
  have hsource_le : r ≤ H 1 := by
    have hle :
        r ≤ Module.finrank K (W (0 : Fin (N + 1))) :=
      paperTotalMap_rank_le_layer_finrank W B hprod (0 : Fin (N + 1))
    simpa using hle.trans_eq (hH (0 : Fin (N + 1))).symm
  have htarget_le : r ≤ H (N + 1) := by
    have hle :
        r ≤ Module.finrank K (W (Fin.last N)) :=
      paperTotalMap_rank_le_layer_finrank W B hprod (Fin.last N)
    simpa using hle.trans_eq (hH (Fin.last N)).symm
  exact
    AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount
      (ι := Fin (Module.finrank K U₀))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
      (L := N) (H := H) (r := r) hU hsource htarget hsource_le htarget_le

namespace PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

set_option linter.unusedSectionVars false in
/-- The canonical product-difference entry ideal splits as the scalar
regular-coordinate ideal joined with the residual `D`-block entry ideal. -/
theorem canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        AoyagiRegularBlockCoordinateIndex.entryIdeal
          (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
  intro E EMat S
  calc
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
          matrixEntryIdeal S.D := by
      simpa [E, EMat, S] using
        cert.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
    _ = AoyagiRegularBlockCoordinateIndex.entryIdeal
          (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
      rw [AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal]

set_option linter.unusedSectionVars false in
/-- The canonical product-difference entry ideal is generated by the combined
p. 13 scalar product-difference coordinate family. -/
theorem canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
      AoyagiProductDifferenceCoordinateIndex.entryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
  intro E EMat S
  calc
    matrixEntryIdeal
        (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀)) K)
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
        fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      simpa [E, EMat, S] using
        cert.canonicalProductDifferenceEntryIdeal
    _ = AoyagiProductDifferenceCoordinateIndex.entryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      rw [AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal]

end PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

set_option linter.unusedSectionVars false in
/-- A fixed-base source-side neighborhood where the canonical product-difference
entry ideal is split into scalar regular-coordinate entries and the residual
`D`-block entries. -/
def PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U : Set α,
    U ∈ nhds x₀ ∧
    x₀ ∈ U ∧
    ∀ x, x ∈ U →
      x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge →
        let E : ∀ p : Fin N,
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
          fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
        let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
        let S := ChartLocalSuffixState.suffixState EMat
          (Fin.last N) 0 (Fin.zero_le (Fin.last N))
        matrixEntryIdeal
            (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (Fin (Module.finrank K U₀)) K)
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
          AoyagiRegularBlockCoordinateIndex.entryIdeal
              (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) ⊔
            matrixEntryIdeal S.D

set_option linter.unusedSectionVars false in
/-- A fixed-base source-side neighborhood where the canonical product-difference
entry ideal is generated by the combined p. 13 scalar coordinate family. -/
def PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U : Set α,
    U ∈ nhds x₀ ∧
    x₀ ∈ U ∧
    ∀ x, x ∈ U →
      x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge →
        let E : ∀ p : Fin N,
            reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
          fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
        let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
        let S := ChartLocalSuffixState.suffixState EMat
          (Fin.last N) 0 (Fin.zero_le (Fin.last N))
        matrixEntryIdeal
            (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (Fin (Module.finrank K U₀)) K)
                (0 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
          AoyagiProductDifferenceCoordinateIndex.entryIdeal
            (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- The local source certificate exposes an ordinary neighborhood where, on
the source-shaped rank stratum, the canonical product-difference entry ideal
splits as the scalar regular-coordinate ideal joined with the residual
`D`-block entry ideal. -/
theorem exists_regularCoordinateIdeal_source_neighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge := by
  rcases cert.exists_source_neighborhood with ⟨U, hU, hx₀U, hsource⟩
  refine ⟨U, hU, hx₀U, ?_⟩
  intro x hxU hxsrc
  exact
    (hsource x hxU hxsrc)
      |>.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal

/-- Alias for the named regular-coordinate/residual ideal source-neighborhood
predicate. -/
theorem regularCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge :=
  cert.exists_regularCoordinateIdeal_source_neighborhood

set_option linter.unusedSectionVars false in
/-- The local source certificate exposes an ordinary neighborhood where, on
the source-shaped rank stratum, the canonical product-difference entry ideal
is generated by the combined p. 13 scalar coordinate family. -/
theorem exists_productDifferenceCoordinateIdeal_source_neighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge := by
  rcases cert.exists_source_neighborhood with ⟨U, hU, hx₀U, hsource⟩
  refine ⟨U, hU, hx₀U, ?_⟩
  intro x hxU hxsrc
  exact
    (hsource x hxU hxsrc)
      |>.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal

/-- Alias for the named product-difference coordinate ideal source-neighborhood
predicate. -/
theorem productDifferenceCoordinateIdealSourceNeighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge :=
  cert.exists_productDifferenceCoordinateIdeal_source_neighborhood

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the three p. 13 regular blocks `Ctop - 1`, `-B`, and
`lowerLeftBlock L`.

The residual block `D` is intentionally not part of this regular-coordinate
index. -/
theorem regularBlockScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiRegularBlockCoordinateIndex.value
          ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiRegularBlockCoordinateIndex.value
              ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨hCtop0, hB0, hF30, _hD0, _hunit, hCtop, hB, hF3, _hD⟩
  exact
    AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
      (X := fun x : α ↦ (S x).Ctop - 1)
      (F2 := fun x : α ↦ -(S x).B)
      (F3 := fun x : α ↦ lowerLeftBlock (S x).L)
      hCtop0 hB0 hF30 hCtop hB hF3 c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the scalar regular-coordinate index cardinality with Aoyagi's p. 13 regular
variable count. -/
theorem regularBlockCoordinateIndex_card_eq_regularVariableCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r :=
  paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the p. 13 residual `D` block.

These coordinates describe the reduced block entries only; they are not part
of the regular-coordinate index. -/
theorem residualBlockScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
          (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiResidualBlockCoordinateIndex.value ((S x₀).D) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiResidualBlockCoordinateIndex.value ((S x).D) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨_hCtop0, _hB0, _hF30, hD0, _hunit, _hCtop, _hB, _hF3, hD⟩
  exact
    AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
      (D := fun x : α ↦ (S x).D) hD0 hD c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the residual scalar-coordinate index cardinality with the product of the
row/left and column/right residual endpoint dimensions. -/
theorem residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r) :=
  paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

set_option linter.unusedSectionVars false in
/-- The canonical local certificate gives centered continuous scalar
coordinates for the cleaned p. 13 product-difference ideal family. -/
theorem productDifferenceScalarCoordinates_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    ∀ c : AoyagiProductDifferenceCoordinateIndex
        (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
          (Fin.last N))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
      AoyagiProductDifferenceCoordinateIndex.value
          ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) ((S x₀).D) c = 0 ∧
        ContinuousAt
          (fun x : α =>
            AoyagiProductDifferenceCoordinateIndex.value
              ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) ((S x).D) c) x₀ := by
  intro E S c
  rcases cert.coefficientFields_centered_continuous with
    ⟨hCtop0, hB0, hF30, hD0, _hunit, hCtop, hB, hF3, hD⟩
  exact
    AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt
      (X := fun x : α ↦ (S x).Ctop - 1)
      (F2 := fun x : α ↦ -(S x).B)
      (F3 := fun x : α ↦ lowerLeftBlock (S x).L)
      (D := fun x : α ↦ (S x).D)
      hCtop0 hB0 hF30 hD0 hCtop hB hF3 hD c

omit [CompleteSpace K] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- The local source certificate carries enough basepoint rank data to identify
the full product-difference scalar-coordinate index cardinality with the
endpoint product entry count. -/
theorem productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {H : ℕ → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1) :=
  paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
    W B U₀ hU₀ cert.source_basepoint.1 hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

/-- Centered continuity of the scalar regular coordinates determined by the
fixed-base canonical product-difference suffix state. -/
def PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiRegularBlockCoordinateIndex.value
        ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiRegularBlockCoordinateIndex.value
            ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) c) x₀

/-- Centered continuity of the scalar residual `D`-block coordinates determined
by the fixed-base canonical product-difference suffix state. -/
def PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiResidualBlockCoordinateIndex
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiResidualBlockCoordinateIndex.value ((S x₀).D) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiResidualBlockCoordinateIndex.value ((S x).D) c) x₀

/-- Centered continuity of the scalar coordinates for the cleaned p. 13
product-difference ideal family. -/
def PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) : Prop :=
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  ∀ c : AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0),
    AoyagiProductDifferenceCoordinateIndex.value
        ((S x₀).Ctop - 1) (-(S x₀).B) (lowerLeftBlock (S x₀).L) ((S x₀).D) c = 0 ∧
      ContinuousAt
        (fun x : α =>
          AoyagiProductDifferenceCoordinateIndex.value
            ((S x).Ctop - 1) (-(S x).B) (lowerLeftBlock (S x).L) ((S x).D) c) x₀

/-- The Pi-valued map collecting the p. 13 regular block coordinates from the
fixed-base canonical product-difference suffix state.

This is only the coordinate family as a function into a product type.  It does
not assert that these coordinates form a chart. -/
def paperEndpointFixedBaseRegularBlockCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiRegularBlockCoordinateIndex.value
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L)

/-- The p. 13 `F2/F3` part of the fixed-base regular-block square-sum. -/
def paperEndpointFixedBaseRegularBlockF2F3SquareSum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) : K :=
  let ι := Fin (Module.finrank K U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  aoyagiCoordinateSquareSum
      (fun ij : ι × ν =>
        paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := K) W B U₀ hU₀ Cedge x
          (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
    aoyagiCoordinateSquareSum
      (fun ij : μ × ι =>
        paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := K) W B U₀ hU₀ Cedge x
          (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij)))

set_option linter.unusedSectionVars false in
/-- The fixed-base p. 13 `F2/F3` square-sum reads exactly the `-B` and
`lowerLeftBlock L` entries of the canonical suffix state. -/
theorem paperEndpointFixedBaseRegularBlockF2F3SquareSum_eq_suffixState_B_lowerLeftBlock
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    paperEndpointFixedBaseRegularBlockF2F3SquareSum
        (K := K) W B U₀ hU₀ Cedge x =
      let ι := Fin (Module.finrank K U₀)
      let μ :=
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
      let ν :=
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0
      let E : ∀ p : Fin N,
          Matrix
            (ι ⊕ throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (ι ⊕ throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
        fun p ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
      let S : ChartLocalSuffixState ι
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
        ChartLocalSuffixState.suffixState E (Fin.last N) 0
          (Fin.zero_le (Fin.last N))
      aoyagiCoordinateSquareSum (fun ij : ι × ν => (-(S.B)) ij.1 ij.2) +
        aoyagiCoordinateSquareSum (fun ij : μ × ι => lowerLeftBlock S.L ij.1 ij.2) := by
  simp [paperEndpointFixedBaseRegularBlockF2F3SquareSum,
    paperEndpointFixedBaseRegularBlockCoordinateMap,
    AoyagiRegularBlockCoordinateIndex.value]

/-- The Pi-valued map collecting the residual `D`-block coordinates from the
fixed-base canonical product-difference suffix state. -/
def paperEndpointFixedBaseResidualBlockCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiResidualBlockCoordinateIndex
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiResidualBlockCoordinateIndex.value S.D

/-- The Pi-valued map collecting the cleaned p. 13 product-difference
coordinates: regular block coordinates together with the residual `D` block. -/
def paperEndpointFixedBaseProductDifferenceCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiProductDifferenceCoordinateIndex.value
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

set_option linter.unusedSectionVars false in
/-- Fixed-base regular coordinates read the supplied suffix fields. -/
theorem paperEndpointFixedBaseRegularBlockCoordinateMap_eq_of_suffixState_fields
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) :
    let E : ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S :
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      ChartLocalSuffixState.suffixState E (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    S.B = -F2 →
    S.Ctop = Ctop →
    S.L =
      fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
        F3
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) →
    paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x =
      AoyagiRegularBlockCoordinateIndex.value (Ctop - 1) F2 F3 := by
  intro E S hB hCtop hL
  funext c
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      simp [paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, hCtop]
  | inr rest =>
      cases rest with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          simp [paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, hB]
      | inr ij =>
          rcases ij with ⟨i, j⟩
          simp [paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, hL]

set_option linter.unusedSectionVars false in
/-- Fixed-base residual coordinates read the supplied suffix-state `D` field. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_of_suffixState_D
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α)
    (D : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K) :
    let E : ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S :
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      ChartLocalSuffixState.suffixState E (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    S.D = D →
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
      AoyagiResidualBlockCoordinateIndex.value D := by
  intro E S hD
  funext c
  rcases c with ⟨i, j⟩
  simp [paperEndpointFixedBaseResidualBlockCoordinateMap, E, S, hD]

set_option linter.unusedSectionVars false in
/-- Fixed-base residual coordinates are the scalar entries of the deterministic
suffix residual product. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    (let E := fun p : Fin N ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ);
      paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct E
            (Fin.last N) 0 (Fin.zero_le (Fin.last N)))) := by
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hD :
      S.D = ChartLocalSuffixState.residualProduct E
        (Fin.last N) 0 (Fin.zero_le (Fin.last N)) := by
    simpa [S] using
      ChartLocalSuffixState.suffixState_D_eq_residualProduct
        (K := K) E (Fin.zero_le (Fin.last N))
  simpa [E] using
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_of_suffixState_D
      (K := K) W B U₀ hU₀ Cedge x
      (ChartLocalSuffixState.residualProduct E
        (Fin.last N) 0 (Fin.zero_le (Fin.last N))) hD

set_option linter.unusedSectionVars false in
/-- The fixed-base regular coordinate map depends only on the edge family at
the queried point. -/
theorem paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
    [∀ j, FiniteDimensional K (W j)]
    {α β : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {Cedge' : β → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {x : α} {y : β}
    (h : Cedge x = Cedge' y) :
    paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x =
      paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge' y := by
  funext c
  simp [paperEndpointFixedBaseRegularBlockCoordinateMap, h]

set_option linter.unusedSectionVars false in
/-- The fixed-base residual coordinate map depends only on the edge family at
the queried point. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
    [∀ j, FiniteDimensional K (W j)]
    {α β : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {Cedge' : β → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {x : α} {y : β}
    (h : Cedge x = Cedge' y) :
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x =
      paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge' y := by
  funext c
  simp [paperEndpointFixedBaseResidualBlockCoordinateMap, h]

set_option linter.unusedSectionVars false in
/-- Fixed-base cleaned product-difference coordinates read the supplied suffix fields. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (D : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K) :
    let E : ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let S :
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      ChartLocalSuffixState.suffixState E (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    S.B = -F2 →
    S.Ctop = Ctop →
    S.L =
      fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
        F3
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) →
    S.D = D →
    paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3 D := by
  intro E S hB hCtop hL hD
  funext c
  cases c with
  | inl c =>
      cases c with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          simp [paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, hCtop]
      | inr rest =>
          cases rest with
          | inl ij =>
              rcases ij with ⟨i, j⟩
              simp [paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, hB]
          | inr ij =>
              rcases ij with ⟨i, j⟩
              simp [paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, hL]
  | inr c =>
      rcases c with ⟨i, j⟩
      simp [paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, hD]

set_option linter.unusedSectionVars false in
/-- Fixed-base suffix fields for the single-edge product-family case. -/
theorem paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin 1,
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C0 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K) :
    let E : ∀ p : Fin 1,
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    ChartLocalSuffixState.transformedEdge EMat 0
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin 2 ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last 1)) =
      fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2) →
    IsUnit Ctop.det →
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last 1) 0 (Fin.zero_le (Fin.last 1))
    S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
      S.L =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1)) K) := by
  intro E EMat hM hCtop S
  simpa using
    ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one
      (K := K) EMat 0 F2 F3 Ctop C0 hM hCtop

set_option linter.unusedSectionVars false in
/-- Fixed-base product-difference coordinates read Aoyagi's single-edge
product-family fields. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin 1,
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C0 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K) :
    let E : ∀ p : Fin 1,
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    ChartLocalSuffixState.transformedEdge EMat 0
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin 2 ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last 1)) =
      fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2) →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := 1) V Bv U₀ hU₀ Cedge x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3 C0 := by
  intro E EMat hM hCtop
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last 1) 0 (Fin.zero_le (Fin.last 1))
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
        S.L =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1)) K) := by
    simpa [S] using
      paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one
        (K := K) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C0 hM hCtop
  refine
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
      (K := K) (N := 1) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C0
      ?_ ?_ ?_ ?_
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.2.2
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.2.1

set_option linter.unusedSectionVars false in
/-- Prescribed fixed-base single-edge product-family matrices give the
corresponding fixed-base continuous edge family and p. 13 coordinates. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrix_one
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (x : α)
    (G : ∀ p : Fin 1, Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) K)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C0 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K) :
    ChartLocalSuffixState.transformedEdge G 0
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin 2 ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last 1)) =
      fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2) →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := 1) V Bv U₀ hU₀
        (fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G)
        x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3 C0 := by
  intro hM hCtop
  let Cedge : α → ∀ p : Fin 1,
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ :=
    fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G
  let E : ∀ p : Fin 1, reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
    fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
  have hEMat : EMat = G := by
    funext p
    simpa [EMat, E, Cedge] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := K) V Bv U₀ hU₀ G p
  have hM' :
      ChartLocalSuffixState.transformedEdge EMat 0
          (ChartLocalSuffixState.terminal
            (ρ := Fin (Module.finrank K U₀))
            (κ := fun j : Fin 2 ↦
              throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
            (K := K) (Fin.last 1)) =
        fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2) := by
    simpa [hEMat] using hM
  have hmain :=
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one
      (K := K) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C0 hM' hCtop
  simpa [Cedge, E, EMat, hEMat] using hmain

set_option linter.unusedSectionVars false in
/-- The prescribed fixed-base matrix family for the one-edge p. 13
product-coordinate constructor attached to a regular Euclidean coordinate
vector and a residual matrix. -/
def paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (D : Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ) :
    ∀ p : Fin 1, Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ :=
  fun p ↦ by
    have hp : p = 0 := Subsingleton.elim p 0
    subst p
    exact
      ChartLocalSuffixState.productCoordinateSingleEdgeMatrix
        (AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c ↦ u c))
        (AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c ↦ u c))
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c))
        D

set_option linter.unusedSectionVars false in
/-- The one-edge p. 13 product-coordinate constructor has raw residual product
equal to the supplied residual matrix. -/
theorem paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (D : Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ)
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    ChartLocalSuffixState.residualProduct
        (paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ u D)
        (Fin.last 1) 0 (Fin.zero_le (Fin.last 1)) = D := by
  let G :=
    paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u D
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  have hE :
      G 0 = ChartLocalSuffixState.productCoordinateSingleEdgeMatrix F2 F3 Ctop D := by
    simp [G, F2, F3, Ctop,
      paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean]
  simpa [G] using
    ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq
      (K := ℝ) G 0 F2 F3 Ctop D hE (by simpa [Ctop] using hCtop)

set_option linter.unusedSectionVars false in
/-- Fixed-base product-difference coordinates read Aoyagi's single-edge raw
product-coordinate edge matrix. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin 1,
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C0 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last 1))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K) :
    let E : ∀ p : Fin 1,
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    EMat 0 = ChartLocalSuffixState.productCoordinateSingleEdgeMatrix F2 F3 Ctop C0 →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := 1) V Bv U₀ hU₀ Cedge x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3 C0 := by
  intro E EMat hE hCtop
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last 1) 0 (Fin.zero_le (Fin.last 1))
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
        S.L =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1)) K) := by
    simpa [S] using
      ChartLocalSuffixState.suffixState_productCoordinate_fields_one
        (K := K) EMat 0 F2 F3 Ctop C0 hE hCtop
  refine
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
      (K := K) (N := 1) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C0
      ?_ ?_ ?_ ?_
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.2.2
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, S] using hfields.2.2.1

set_option linter.unusedSectionVars false in
/-- The one-edge p. 13 product-coordinate constructor has regular coordinates
equal to the supplied Euclidean vector and residual coordinates equal to the
supplied residual matrix. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (D : Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ)
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := ℝ) (N := 1) V Bv U₀ hU₀
        (fun _ ↦
          paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
            (paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
              V Bv U₀ u D))
        x =
      Sum.elim (fun c ↦ u c) (AoyagiResidualBlockCoordinateIndex.value D) := by
  let G :=
    paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u D
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Cedge : α → ∀ p : Fin 1,
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
    fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G
  have hE :
      (let E : ∀ p : Fin 1,
          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ :=
        fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)
       let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
       EMat 0 = ChartLocalSuffixState.productCoordinateSingleEdgeMatrix F2 F3 Ctop D) := by
    dsimp [Cedge]
    calc
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
          (fun p ↦
            (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)) 0 =
          G 0 := by
            simpa using
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
                (K := ℝ) V Bv U₀ hU₀ G 0
      _ = ChartLocalSuffixState.productCoordinateSingleEdgeMatrix F2 F3 Ctop D := by
            simp [G, F2, F3, Ctop,
              paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean]
  have hread :=
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one
      (K := ℝ) V Bv U₀ hU₀ Cedge x F2 F3 Ctop D hE
      (by simpa [Ctop] using hCtop)
  calc
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := ℝ) (N := 1) V Bv U₀ hU₀
        (fun _ ↦
          paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
            (paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
              V Bv U₀ u D))
        x =
        AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3 D := by
          simpa [Cedge, G] using hread
    _ = Sum.elim (fun c ↦ u c) (AoyagiResidualBlockCoordinateIndex.value D) := by
          simpa [F2, F3, Ctop] using
            AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual
                (ι := Fin (Module.finrank ℝ U₀))
                (μ := throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
                (ν := throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ 0)
                u D

set_option linter.unusedSectionVars false in
/-- Source-dependent one-edge p. 13 product-coordinate edge family with a
prescribed residual matrix at the base point. -/
def paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Dbase : α → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ) :
    α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)) →
      ∀ p : Fin 1, reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
  fun xu ↦
    paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
      (paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
        V Bv U₀ xu.2 (Dbase xu.1))

set_option linter.unusedSectionVars false in
/-- Source-dependent split form of the one-edge p.13 product-coordinate
constructor.  At `(x,u)`, regular coordinates are `u` and residual coordinates
are the supplied matrix family `Dbase x`. -/
theorem paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Dbase : α → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ)
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd :=
      paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
        V Bv U₀ hU₀ Dbase
    (paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (x, u) = fun c ↦ u c) ∧
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeProd (x, u) =
        AoyagiResidualBlockCoordinateIndex.value (Dbase x) := by
  intro CedgeProd
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let CedgeConst : α × EuclideanSpace ℝ Coord →
      ∀ p : Fin 1, reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
    fun _ ↦
      paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
        (paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ u (Dbase x))
  have hpoint : CedgeProd (x, u) = CedgeConst (x, u) := by
    rfl
  have hfull :=
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (x := (x, u)) (u := u) (D := Dbase x) hCtop
  have hsplit :
      paperEndpointFixedBaseProductDifferenceCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u) =
        Sum.elim
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u))
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u)) := by
    funext c
    cases c <;>
      simp [paperEndpointFixedBaseProductDifferenceCoordinateMap,
        paperEndpointFixedBaseRegularBlockCoordinateMap,
        paperEndpointFixedBaseResidualBlockCoordinateMap]
  have hcomponents :
      Sum.elim
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u))
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u)) =
        Sum.elim (fun c ↦ u c)
          (AoyagiResidualBlockCoordinateIndex.value (Dbase x)) := by
    exact hsplit.symm.trans (by simpa [CedgeConst] using hfull)
  have hfixed_regular :
      paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u) = fun c ↦ u c := by
    funext c
    exact congrFun hcomponents (Sum.inl c)
  have hfixed_residual :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 1) V Bv U₀ hU₀ CedgeConst (x, u) =
        AoyagiResidualBlockCoordinateIndex.value (Dbase x) := by
    funext c
    exact congrFun hcomponents (Sum.inr c)
  constructor
  · exact
      (paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
        (K := ℝ) (N := 1) V Bv U₀ hU₀ hpoint).trans hfixed_regular
  · exact
      (paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 1) V Bv U₀ hU₀ hpoint).trans hfixed_residual

set_option linter.unusedSectionVars false in
/-- The one-edge source-dependent p.13 product-coordinate edge family is
continuous when the residual matrix family is continuous. -/
theorem continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
    (V : Fin 2 → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin 1, V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Dbase : α → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ)
    (hDbase : Continuous Dbase) :
    ContinuousAt
      (paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
        V Bv U₀ hU₀ Dbase) (x₀, u₀) := by
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let X := α × EuclideanSpace ℝ Coord
  let F2 : X → Matrix (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ :=
    fun xu ↦ AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ xu.2 c)
  let F3 : X → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (Fin (Module.finrank ℝ U₀)) ℝ :=
    fun xu ↦ AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ xu.2 c)
  let Ctop : X → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ :=
    fun xu ↦ AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ xu.2 c)
  let C0 : X → Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last 1))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0) ℝ :=
    fun xu ↦ Dbase xu.1
  have hF2 : Continuous F2 :=
    AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean.comp continuous_snd
  have hF3 : Continuous F3 :=
    AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean.comp continuous_snd
  have hCtop : Continuous Ctop :=
    AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean.comp continuous_snd
  have hC0 : Continuous C0 :=
    hDbase.comp continuous_fst
  have hmatrix : ContinuousAt
      (fun xu : X ↦
        paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ xu.2 (Dbase xu.1)) (x₀, u₀) := by
    refine continuousAt_pi.2 ?_
    intro p
    have hp : p = 0 := Subsingleton.elim p 0
    subst p
    simpa [paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean,
      F2, F3, Ctop, C0, X, Coord] using
      (continuous_productCoordinateSingleEdgeMatrix
        (K := ℝ) (F2 := F2) (F3 := F3) (Ctop := Ctop) (C0 := C0)
        hF2 hF3 hCtop hC0).continuousAt
  have hrealise :=
    paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
      (K := ℝ) (W := V) (B := Bv) U₀ hU₀
      (fun xu : X ↦
        paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ xu.2 (Dbase xu.1)) hmatrix
  simpa [paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean,
    X, Coord] using hrealise

set_option linter.unusedSectionVars false in
/-- The prescribed fixed-base matrix family for the multi-edge p. 13
product-coordinate constructor attached to a base edge family and a regular
Euclidean coordinate vector. -/
def paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ) :
    ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ :=
  fun p ↦ by
    classical
    let F2 :=
      AoyagiRegularBlockCoordinateIndex.f2Matrix
        (fun c :
          AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
    let F3 :=
      AoyagiRegularBlockCoordinateIndex.f3Matrix
        (fun c :
          AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
    let Ctop :=
      AoyagiRegularBlockCoordinateIndex.ctopMatrix
        (fun c :
          AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
    let j : Fin (M + 3) := Fin.last (M + 2)
    by_cases hlast : p = Fin.last (M + 1)
    · subst p
      exact
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3
          (ChartLocalSuffixState.residualBlock Ebase j (Fin.last (M + 1))
            (Fin.last (M + 1)).succ.le_last)
    by_cases hzero : p = 0
    · subst p
      exact
        ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop
          (ChartLocalSuffixState.residualBlock Ebase j 0 (0 : Fin (M + 2)).succ.le_last)
    exact
      ChartLocalSuffixState.productCoordinateMiddleMatrix
        (ρ := Fin (Module.finrank ℝ U₀))
        (ChartLocalSuffixState.residualBlock Ebase j p p.succ.le_last)

set_option linter.unusedSectionVars false in
/-- The source-dependent multi-edge p. 13 product-coordinate matrix family is
continuous at `(x₀,u₀)` when the base fixed-coordinate edge matrices are
continuous at `x₀` and satisfy the recursive determinant-chart hypotheses
there. -/
theorem continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Ebase : α → ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ)
    (hEbase : ContinuousAt Ebase x₀)
    (hchart : ∀ (p : Fin (M + 2))
        (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (Ebase x₀) p
          (ChartLocalSuffixState.suffixState (Ebase x₀) (Fin.last (M + 2))
            p.succ hpj))) :
    ContinuousAt
      (fun xu : α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) ↦
        paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ xu.2 (Ebase xu.1)) (x₀, u₀) := by
  classical
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let X := α × EuclideanSpace ℝ Coord
  let κ :=
    fun j ↦ throughSubspaceEndpointComplementIndex
      (reverseVertex V) (reverseEdge V Bv) U₀ j
  have hEpair : ContinuousAt (fun xu : X ↦ Ebase xu.1) (x₀, u₀) :=
    hEbase.comp continuous_fst.continuousAt
  have hchartPair : ∀ (p : Fin (M + 2)) (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge ((fun xu : X ↦ Ebase xu.1) (x₀, u₀)) p
          (ChartLocalSuffixState.suffixState ((fun xu : X ↦ Ebase xu.1) (x₀, u₀))
            (Fin.last (M + 2)) p.succ hpj)) := by
    intro p hpj
    simpa using hchart p hpj
  have hF2 : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.f2Matrix
          (fun c : Coord ↦ xu.2 c)) (x₀, u₀) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  have hF3 : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.f3Matrix
          (fun c : Coord ↦ xu.2 c)) (x₀, u₀) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  have hCtop : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.ctopMatrix
          (fun c : Coord ↦ xu.2 c)) (x₀, u₀) :=
    AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  refine continuousAt_pi.2 ?_
  intro p
  let j : Fin (M + 3) := Fin.last (M + 2)
  by_cases hlast : p = Fin.last (M + 1)
  · subst p
    let pLast : Fin (M + 2) := Fin.last (M + 1)
    let hpj : pLast.succ ≤ j := pLast.succ.le_last
    have hC : ContinuousAt
        (fun xu : X ↦
          ChartLocalSuffixState.residualBlock (Ebase xu.1) j pLast hpj) (x₀, u₀) :=
      continuousAt_chartLocalSuffixState_residualBlock
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (κ := κ)
        (E := fun xu : X ↦ Ebase xu.1) hEpair hchartPair pLast hpj
    have hraw : Continuous
        (fun q : Matrix (κ j) (Fin (Module.finrank ℝ U₀)) ℝ ×
            Matrix (κ j) (κ pLast.castSucc) ℝ ↦
          ChartLocalSuffixState.productCoordinateRightEndpointMatrix (K := ℝ) q.1 q.2) :=
      continuous_productCoordinateRightEndpointMatrix
        (K := ℝ) (F3 := fun q : Matrix (κ j) (Fin (Module.finrank ℝ U₀)) ℝ ×
            Matrix (κ j) (κ pLast.castSucc) ℝ ↦ q.1)
        (C := fun q : Matrix (κ j) (Fin (Module.finrank ℝ U₀)) ℝ ×
            Matrix (κ j) (κ pLast.castSucc) ℝ ↦ q.2)
        continuous_fst continuous_snd
    have hpair : ContinuousAt
        (fun xu : X ↦
          (AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ xu.2 c),
            ChartLocalSuffixState.residualBlock (Ebase xu.1) j pLast hpj)) (x₀, u₀) :=
      hF3.prodMk hC
    have hres := hraw.continuousAt.comp hpair
    simpa [paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean, Coord, X, κ, j,
      pLast, hpj] using hres
  by_cases hzero : p = 0
  · subst p
    let p0 : Fin (M + 2) := 0
    let hpj : p0.succ ≤ j := p0.succ.le_last
    have hC : ContinuousAt
        (fun xu : X ↦
          ChartLocalSuffixState.residualBlock (Ebase xu.1) j p0 hpj) (x₀, u₀) :=
      continuousAt_chartLocalSuffixState_residualBlock
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (κ := κ)
        (E := fun xu : X ↦ Ebase xu.1) hEpair hchartPair p0 hpj
    have hraw : Continuous
        (fun q : Matrix (Fin (Module.finrank ℝ U₀)) (κ p0.castSucc) ℝ ×
            Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ ×
              Matrix (κ p0.succ) (κ p0.castSucc) ℝ ↦
          ChartLocalSuffixState.productCoordinateLeftEndpointMatrix
            (K := ℝ) q.1 q.2.1 q.2.2) :=
      continuous_productCoordinateLeftEndpointMatrix
        (K := ℝ)
        (F2 := fun q : Matrix (Fin (Module.finrank ℝ U₀)) (κ p0.castSucc) ℝ ×
            Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ ×
              Matrix (κ p0.succ) (κ p0.castSucc) ℝ ↦ q.1)
        (Ctop := fun q : Matrix (Fin (Module.finrank ℝ U₀)) (κ p0.castSucc) ℝ ×
            Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ ×
              Matrix (κ p0.succ) (κ p0.castSucc) ℝ ↦ q.2.1)
        (C0 := fun q : Matrix (Fin (Module.finrank ℝ U₀)) (κ p0.castSucc) ℝ ×
            Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ ×
              Matrix (κ p0.succ) (κ p0.castSucc) ℝ ↦ q.2.2)
        continuous_fst (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)
    have hpair : ContinuousAt
        (fun xu : X ↦
          (AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ xu.2 c),
            (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ xu.2 c),
              ChartLocalSuffixState.residualBlock (Ebase xu.1) j p0 hpj))) (x₀, u₀) :=
      hF2.prodMk (hCtop.prodMk hC)
    have hres := hraw.continuousAt.comp hpair
    simpa [paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean, Coord, X, κ, j,
      p0, hpj, hlast] using hres
  · have hpj : p.succ ≤ j := p.succ.le_last
    have hC : ContinuousAt
        (fun xu : X ↦
          ChartLocalSuffixState.residualBlock (Ebase xu.1) j p hpj) (x₀, u₀) :=
      continuousAt_chartLocalSuffixState_residualBlock
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (κ := κ)
        (E := fun xu : X ↦ Ebase xu.1) hEpair hchartPair p hpj
    have hraw : Continuous
        (fun C : Matrix (κ p.succ) (κ p.castSucc) ℝ ↦
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) C) :=
      continuous_productCoordinateMiddleMatrix
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (C := fun C ↦ C) continuous_id
    have hres := hraw.continuousAt.comp hC
    simpa [paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean, Coord, X, κ, j,
      hlast, hzero] using hres

set_option linter.unusedSectionVars false in
/-- The multi-edge p. 13 product-coordinate matrix constructor preserves the
base suffix residual product. -/
theorem paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ) :
    ChartLocalSuffixState.residualProduct
        (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ u Ebase)
        (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
      ChartLocalSuffixState.residualProduct Ebase
        (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) := by
  let G :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u Ebase
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  have hLastG :
      G (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) (Fin.last (M + 1)) (Fin.last (M + 1)).succ.le_last) := by
    simp [G, F3, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean]
  have hMidG :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        G p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (ρ := Fin (Module.finrank ℝ U₀))
            (ChartLocalSuffixState.residualBlock Ebase
              (Fin.last (M + 2)) p p.succ.le_last) := by
    intro p hp0 hplast
    have hnotLast : p ≠ Fin.last (M + 1) := by
      intro hp
      have hval : p.val = M + 1 := by
        simp [hp]
      omega
    have hnotZero : p ≠ 0 := by
      intro hp
      have hval : p.val = 0 := by
        simp [hp]
      omega
    simp [G, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast, hnotZero]
  have hLeftG :
      let p0 : Fin (M + 2) := 0
      G p0 =
        ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) p0 p0.succ.le_last) := by
    have hnotLast : (0 : Fin (M + 2)) ≠ Fin.last (M + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    simp [G, F2, Ctop, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast]
  simpa [G] using
    ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
      (K := ℝ) Ebase G F2 F3 Ctop hLastG hMidG hLeftG

set_option linter.unusedSectionVars false in
/-- The multi-edge p. 13 product-coordinate constructor has regular
coordinates equal to the supplied Euclidean vector and residual coordinates
equal to the base residual product. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ)
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀
        (fun _ ↦
          paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
            (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
              V Bv U₀ u Ebase))
        x =
      Sum.elim (fun c ↦ u c)
        (AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct Ebase
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))) := by
  let G :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u Ebase
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Cedge : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
    fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G
  let E : ∀ p : Fin (M + 2), reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ :=
    fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
  have hEMat : EMat = G := by
    funext p
    simpa [EMat, E, Cedge] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := ℝ) V Bv U₀ hU₀ G p
  have hLastG :
      G (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) (Fin.last (M + 1)) (Fin.last (M + 1)).succ.le_last) := by
    simp [G, F3, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean]
  have hMidG :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        G p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (ρ := Fin (Module.finrank ℝ U₀))
            (ChartLocalSuffixState.residualBlock Ebase
              (Fin.last (M + 2)) p p.succ.le_last) := by
    intro p hp0 hplast
    have hnotLast : p ≠ Fin.last (M + 1) := by
      intro hp
      have hval : p.val = M + 1 := by
        simp [hp]
      omega
    have hnotZero : p ≠ 0 := by
      intro hp
      have hval : p.val = 0 := by
        simp [hp]
      omega
    simp [G, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast, hnotZero]
  have hLeftG :
      let p0 : Fin (M + 2) := 0
      G p0 =
        ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) p0 p0.succ.le_last) := by
    have hnotLast : (0 : Fin (M + 2)) ≠ Fin.last (M + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    simp [G, F2, Ctop, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast]
  have hLast :
      EMat (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) (Fin.last (M + 1)) (Fin.last (M + 1)).succ.le_last) := by
    rw [hEMat]
    exact hLastG
  have hMid :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        EMat p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (ρ := Fin (Module.finrank ℝ U₀))
            (ChartLocalSuffixState.residualBlock Ebase
              (Fin.last (M + 2)) p p.succ.le_last) := by
    intro p hp0 hplast
    rw [hEMat]
    exact hMidG p hp0 hplast
  have hLeft :
      let p0 : Fin (M + 2) := 0
      EMat p0 =
        ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop
          (ChartLocalSuffixState.residualBlock Ebase
            (Fin.last (M + 2)) p0 p0.succ.le_last) := by
    rw [hEMat]
    exact hLeftG
  let p0 : Fin (M + 2) := 0
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧
        S.D = ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last ∧
        S.L =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ) 0 F3
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2))) ℝ) := by
    simpa [p0, S] using
      ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
        (K := ℝ) EMat F2 F3 Ctop
        (fun p ↦ ChartLocalSuffixState.residualBlock Ebase
          (Fin.last (M + 2)) p p.succ.le_last)
        hLast hMid hLeft (by simpa [Ctop] using hCtop)
  have hread :
      paperEndpointFixedBaseProductDifferenceCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ Cedge x =
        AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
          (ChartLocalSuffixState.residualProduct EMat
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
    refine
      paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ Cedge x F2 F3 Ctop
          (ChartLocalSuffixState.residualProduct EMat
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))
        ?_ ?_ ?_ ?_
    · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.1
    · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.1
    · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.2
    · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.1
  have hresG :
      ChartLocalSuffixState.residualProduct G
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        ChartLocalSuffixState.residualProduct Ebase
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) :=
    ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
      (K := ℝ) Ebase G F2 F3 Ctop hLastG hMidG hLeftG
  have hresEMat :
      ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) =
        ChartLocalSuffixState.residualProduct Ebase
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))) := by
    simpa [hEMat] using hresG
  calc
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀
        (fun _ ↦
          paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
            (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
              V Bv U₀ u Ebase))
        x =
        AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
          (ChartLocalSuffixState.residualProduct EMat
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
          simpa [Cedge, E, EMat, G] using hread
    _ =
        AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
          (ChartLocalSuffixState.residualProduct Ebase
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
          rw [hresEMat]
    _ =
        Sum.elim (fun c ↦ u c)
          (AoyagiResidualBlockCoordinateIndex.value
            (ChartLocalSuffixState.residualProduct Ebase
              (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))) := by
          simpa [F2, F3, Ctop] using
            AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual
                  (ι := Fin (Module.finrank ℝ U₀))
                  (μ := throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                  (ν := throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ 0)
                  u
                  (ChartLocalSuffixState.residualProduct Ebase
                    (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))

set_option linter.unusedSectionVars false in
/-- Split form of the multi-edge p. 13 product-coordinate constructor: the
regular coordinates are the supplied Euclidean vector and the residual
coordinates are the base residual product. -/
theorem paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ)
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd : α → ∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
      fun _ ↦
        paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
          (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
            V Bv U₀ u Ebase);
      (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x = fun c ↦ u c) ∧
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct Ebase
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
  intro CedgeProd
  have hfull :=
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀) (x := x)
      (u := u) (Ebase := Ebase) hCtop
  have hsplit :
      paperEndpointFixedBaseProductDifferenceCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x =
        Sum.elim
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x)
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x) := by
    funext c
    cases c <;>
      simp [paperEndpointFixedBaseProductDifferenceCoordinateMap,
        paperEndpointFixedBaseRegularBlockCoordinateMap,
        paperEndpointFixedBaseResidualBlockCoordinateMap]
  have hcomponents :
      Sum.elim
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x)
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd x) =
        Sum.elim (fun c ↦ u c)
            (AoyagiResidualBlockCoordinateIndex.value
              (ChartLocalSuffixState.residualProduct Ebase
                (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))) := by
    exact hsplit.symm.trans (by simpa [CedgeProd] using hfull)
  constructor
  · funext c
    exact congrFun hcomponents (Sum.inl c)
  · funext c
    exact congrFun hcomponents (Sum.inr c)

set_option linter.unusedSectionVars false in
/-- The pointwise source-dependent fixed-base product-coordinate edge family:
at `(x,u)`, take the base edge matrices of `CedgeBase x`, choose their
transformed Schur residual blocks as the p.13 residual factors, and realise the
resulting fixed-base matrices as continuous edge maps. -/
def paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ) :
    α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)) →
      ∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
  fun xu ↦
    let Ebase : ∀ p : Fin (M + 2), Matrix
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
            p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeBase xu.1 p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
    paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
      (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
        V Bv U₀ xu.2 Ebase)

set_option linter.unusedSectionVars false in
/-- The source-dependent fixed-base product-coordinate edge family is
continuous at `(x₀,u₀)` under continuity of the base edge family at `x₀` and
the recursive determinant-chart hypotheses for its fixed-base matrix family
there. -/
theorem continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hchart : ∀ (p : Fin (M + 2))
        (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
            (fun q : Fin (M + 2) ↦
              (CedgeBase x₀ q :
                reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ))) p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun q : Fin (M + 2) ↦
                (CedgeBase x₀ q :
                  reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ)))
            (Fin.last (M + 2)) p.succ hpj))) :
    ContinuousAt
      (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase) (x₀, u₀) := by
  classical
  let Ebase : α → ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ :=
    fun x ↦
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p : Fin (M + 2) ↦
          (CedgeBase x p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  have hEbase : ContinuousAt Ebase x₀ := by
    simpa [Ebase] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
        (K := ℝ) V Bv U₀ hU₀ CedgeBase hCedgeBase
  have hmatrix :
      ContinuousAt
        (fun xu : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)) ↦
          paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
            V Bv U₀ xu.2 (Ebase xu.1)) (x₀, u₀) :=
    continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (u₀ := u₀) (Ebase := Ebase)
      hEbase (by simpa [Ebase] using hchart)
  have hrealise :=
    (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
      (K := ℝ) V Bv U₀ hU₀).continuousAt.comp hmatrix
  simpa [paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean,
    Ebase] using hrealise

set_option linter.unusedSectionVars false in
/-- Self-base version of the source-dependent product-coordinate edge-family
continuity theorem.  If the base source family is centered at the fixed paper
chain `Bv`, the recursive determinant-chart hypotheses are supplied by the
fixed-base self-base chart theorem. -/
theorem continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p)) :
    ContinuousAt
      (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase) (x₀, u₀) := by
  have hchart :=
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
      (K := ℝ) V Bv U₀ hU₀ CedgeBase hbase
  exact
    continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀) (u₀ := u₀)
      (CedgeBase := CedgeBase) hCedgeBase
      (by
        intro p hpj
        simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hchart p)

set_option linter.unusedSectionVars false in
/-- Source-dependent split form of the multi-edge p.13 product-coordinate
constructor.  At the point `(x,u)`, regular coordinates are `u` and residual
coordinates agree with the base edge family at `x`. -/
theorem paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    (paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) = fun c ↦ u c) ∧
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x := by
  intro CedgeProd
  let Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
      (fun p ↦
        (CedgeBase x p :
          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  let CedgeConst :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) →
        ∀ p : Fin (M + 2),
          reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ :=
    fun _ ↦
      paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀
        (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
          V Bv U₀ u Ebase)
  have hpoint : CedgeProd (x, u) = CedgeConst (x, u) := by
    rfl
  have hfixed :=
    paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (x := (x, u)) (u := u) (Ebase := Ebase) hCtop
  have hfixed_regular :
      paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeConst (x, u) = fun c ↦ u c := by
    simpa [CedgeConst] using hfixed.1
  have hfixed_residual :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeConst (x, u) =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct Ebase
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
    simpa [CedgeConst] using hfixed.2
  have hbase :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct Ebase
            (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
    simpa [Ebase, paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x
  constructor
  · exact
      (paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ hpoint).trans hfixed_regular
  · have hprod :
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
          AoyagiResidualBlockCoordinateIndex.value
            (ChartLocalSuffixState.residualProduct Ebase
              (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) :=
      (paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ hpoint).trans hfixed_residual
    exact hprod.trans hbase.symm

set_option linter.unusedSectionVars false in
/-- On a sufficiently small Euclidean regular-coordinate ball, the
source-dependent multi-edge p.13 product family has regular coordinates `u`
and residual coordinates equal to the base source residual coordinates. -/
theorem exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {r : ℕ} {rEdge : Fin (M + 2) → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let Coord :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      (∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
                fun i ↦ u i) ∧
      (∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) := by
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  dsimp only
  constructor
  · exact Filter.Eventually.of_forall fun x ↦ by
      intro u hu
      exact
        (paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
          (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
          (CedgeBase := CedgeBase) (x := x) (u := u) (hunit u hu)).1
  · exact Filter.Eventually.of_forall fun x ↦ by
      intro u hu
      exact
        (paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
          (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
          (CedgeBase := CedgeBase) (x := x) (u := u) (hunit u hu)).2

set_option linter.unusedSectionVars false in
/-- The explicit multi-edge source-dependent p.13 product-coordinate edge
family satisfies the fixed-base product-reduction certificate pointwise,
provided the decoded `Ctop(u)` block has unit determinant. -/
theorem paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (rEdge : Fin (M + 2) → ℕ)
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    PaperEndpointFixedBaseProductReductionCertificate
      (K := ℝ) (N := M + 2) V Bv U₀ hU₀
      (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase) rEdge (x, u) := by
  let Ebase : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) ℝ :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
      (fun p ↦
        (CedgeBase x p :
          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  let G :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u Ebase
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c :
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)
  let C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        p.castSucc) ℝ :=
    fun p ↦ ChartLocalSuffixState.residualBlock Ebase
      (Fin.last (M + 2)) p p.succ.le_last
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let E : ∀ p : Fin (M + 2), reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ :=
    fun p ↦ (CedgeProd (x, u) p : reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
  have hEMat : EMat = G := by
    funext p
    simpa [EMat, E, CedgeProd,
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean,
      Ebase, G] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := ℝ) V Bv U₀ hU₀ G p
  have hLast :
      EMat (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3 (C (Fin.last (M + 1))) := by
    rw [hEMat]
    simp [G, F3, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean]
  have hMid :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        EMat p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (ρ := Fin (Module.finrank ℝ U₀)) (C p) := by
    intro p hp0 hplast
    have hnotLast : p ≠ Fin.last (M + 1) := by
      intro hp
      have hval : p.val = M + 1 := by
        simp [hp]
      omega
    have hnotZero : p ≠ 0 := by
      intro hp
      have hval : p.val = 0 := by
        simp [hp]
      omega
    rw [hEMat]
    simp [G, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast, hnotZero]
  have hLeft :
      let p0 : Fin (M + 2) := 0
      EMat p0 = ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
    have hnotLast : (0 : Fin (M + 2)) ≠ Fin.last (M + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    rw [hEMat]
    simp [G, F2, Ctop, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast]
  have hdetCharts :
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
    intro p
    have hp :=
      ChartLocalSuffixState.recursiveDetCharts_productCoordinateEdges_succSucc
        (K := ℝ) EMat F2 F3 Ctop C hLast hMid hLeft (by simpa [Ctop] using hCtop) p
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts, E, EMat,
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hp
  exact
    paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts
      (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd rEdge (x, u) hdetCharts

set_option linter.unusedSectionVars false in
/-- On a sufficiently small Euclidean regular-coordinate ball, the explicit
multi-edge source-dependent p.13 product-coordinate edge family satisfies the
fixed-base product-reduction certificate, eventually on any base source
filter. -/
theorem exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {r : ℕ} (rEdge : Fin (M + 2) → ℕ) {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let Coord :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd rEdge (x, u) := by
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  dsimp only
  exact Filter.Eventually.of_forall fun x ↦ by
    intro u hu
    exact
      paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (x := x) (u := u) (rEdge := rEdge)
        (hunit u hu)

set_option linter.unusedSectionVars false in
/-- Fixed-base suffix fields for a product-family chain with at least two
edges, stated in the endpoint bases used by the coordinate maps. -/
theorem paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last (M + 2)))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        p.castSucc) K) :
    let E : ∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    ChartLocalSuffixState.transformedEdge EMat (Fin.last (M + 1))
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin (M + 3) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last (M + 2))) =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 (-F3)
        (C (Fin.last (M + 1))) →
    (∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
      ChartLocalSuffixState.transformedEdge EMat p
          (ChartLocalSuffixState.suffixState EMat
            (Fin.last (M + 2)) p.succ p.succ.le_last) =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
            (Fin (Module.finrank K U₀)) K)
          (C p)) →
    (let p0 : Fin (M + 2) := 0
     let one : Fin (M + 3) := ⟨1, by omega⟩
     ChartLocalSuffixState.transformedEdge EMat p0
          (ChartLocalSuffixState.suffixState EMat
            (Fin.last (M + 2)) one one.le_last) =
        fromBlocks Ctop (-(Ctop * F2))
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ one)
            (Fin (Module.finrank K U₀)) K)
          (C p0)) →
    IsUnit Ctop.det →
    let p0 : Fin (M + 2) := 0
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last
    S.B = -F2 ∧ S.Ctop = Ctop ∧
      S.D = ChartLocalSuffixState.residualProduct EMat
        (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last ∧
      S.L =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2))) K) := by
  intro E EMat hLast hMid hLeft hCtop p0 S
  exact
    ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_succSucc
      (K := K) EMat F2 F3 Ctop C hLast hMid hLeft hCtop

set_option linter.unusedSectionVars false in
/-- Fixed-base product-difference coordinates read Aoyagi's product-family
fields for a chain with at least two edges. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last (M + 2)))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        p.castSucc) K) :
    let E : ∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    ChartLocalSuffixState.transformedEdge EMat (Fin.last (M + 1))
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin (M + 3) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last (M + 2))) =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 (-F3)
        (C (Fin.last (M + 1))) →
    (∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
      ChartLocalSuffixState.transformedEdge EMat p
          (ChartLocalSuffixState.suffixState EMat
            (Fin.last (M + 2)) p.succ p.succ.le_last) =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
            (Fin (Module.finrank K U₀)) K)
          (C p)) →
    (let p0 : Fin (M + 2) := 0
     let one : Fin (M + 3) := ⟨1, by omega⟩
     ChartLocalSuffixState.transformedEdge EMat p0
          (ChartLocalSuffixState.suffixState EMat
            (Fin.last (M + 2)) one one.le_last) =
        fromBlocks Ctop (-(Ctop * F2))
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ one)
            (Fin (Module.finrank K U₀)) K)
          (C p0)) →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := M + 2) V Bv U₀ hU₀ Cedge x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
        (ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
  intro E EMat hLast hMid hLeft hCtop
  let p0 : Fin (M + 2) := 0
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧
        S.D = ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last ∧
        S.L =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2))) K) := by
    simpa [p0, S] using
      paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc
        (K := K) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C hLast hMid hLeft hCtop
  refine
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
      (K := K) (N := M + 2) V Bv U₀ hU₀ Cedge x F2 F3 Ctop
        (ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))
      ?_ ?_ ?_ ?_
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.2
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.1

set_option linter.unusedSectionVars false in
/-- Fixed-base product-difference coordinates read Aoyagi's raw
product-coordinate edge matrices for a chain with at least two edges. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdges_succSucc
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (Cedge : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ)
    (x : α)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last (M + 2)))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        p.castSucc) K) :
    let E : ∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
      fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
    EMat (Fin.last (M + 1)) =
      ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3 (C (Fin.last (M + 1))) →
    (∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
      EMat p =
        ChartLocalSuffixState.productCoordinateMiddleMatrix
          (ρ := Fin (Module.finrank K U₀)) (C p)) →
    (let p0 : Fin (M + 2) := 0
     EMat p0 =
      ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop (C p0)) →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := M + 2) V Bv U₀ hU₀ Cedge x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
        (ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
  intro E EMat hLast hMid hLeft hCtop
  let p0 : Fin (M + 2) := 0
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧
        S.D = ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) p0.castSucc p0.castSucc.le_last ∧
        S.L =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 F3
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2))) K) := by
    simpa [p0, S] using
      ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
        (K := K) EMat F2 F3 Ctop C hLast hMid hLeft hCtop
  refine
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
      (K := K) (N := M + 2) V Bv U₀ hU₀ Cedge x F2 F3 Ctop
        (ChartLocalSuffixState.residualProduct EMat
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2))))
      ?_ ?_ ?_ ?_
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.1
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.2
  · simpa [E, EMat, paperEndpointFixedBaseEdgeMatrixOfReverseEdges, p0, S] using hfields.2.2.1

set_option linter.unusedSectionVars false in
/-- Prescribed fixed-base product-family edge matrices give the corresponding
fixed-base continuous edge family and p. 13 product-difference coordinates. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrices_succSucc
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module K (V i)]
    [∀ i, ContinuousSMul K (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[K] V i.castSucc)
    [∀ j, FiniteDimensional K (V j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (x : α)
    (G : ∀ p : Fin (M + 2), Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
          p.castSucc) K)
    (F2 : Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ 0) K)
    (F3 : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        (Fin.last (M + 2)))
      (Fin (Module.finrank K U₀)) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀
        p.castSucc) K) :
    ChartLocalSuffixState.transformedEdge G (Fin.last (M + 1))
        (ChartLocalSuffixState.terminal
          (ρ := Fin (Module.finrank K U₀))
          (κ := fun j : Fin (M + 3) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (K := K) (Fin.last (M + 2))) =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 (-F3)
        (C (Fin.last (M + 1))) →
    (∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
      ChartLocalSuffixState.transformedEdge G p
          (ChartLocalSuffixState.suffixState G
            (Fin.last (M + 2)) p.succ p.succ.le_last) =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
            (Fin (Module.finrank K U₀)) K)
          (C p)) →
    (let p0 : Fin (M + 2) := 0
     let one : Fin (M + 3) := ⟨1, by omega⟩
     ChartLocalSuffixState.transformedEdge G p0
          (ChartLocalSuffixState.suffixState G
            (Fin.last (M + 2)) one one.le_last) =
        fromBlocks Ctop (-(Ctop * F2))
          (0 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ one)
            (Fin (Module.finrank K U₀)) K)
          (C p0)) →
    IsUnit Ctop.det →
    paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := K) (N := M + 2) V Bv U₀ hU₀
        (fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G)
        x =
      AoyagiProductDifferenceCoordinateIndex.value (Ctop - 1) F2 F3
        (ChartLocalSuffixState.residualProduct G
          (Fin.last (M + 2)) 0 (Fin.zero_le (Fin.last (M + 2)))) := by
  intro hLast hMid hLeft hCtop
  let Cedge : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[K] reverseVertex V p.succ :=
    fun _ ↦ paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices V Bv U₀ hU₀ G
  let E : ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ :=
    fun p ↦ (Cedge x p : reverseVertex V p.castSucc →ₗ[K] reverseVertex V p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀ E
  have hEMat : EMat = G := by
    funext p
    simpa [EMat, E, Cedge] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := K) V Bv U₀ hU₀ G p
  have hLast' :
      ChartLocalSuffixState.transformedEdge EMat (Fin.last (M + 1))
          (ChartLocalSuffixState.terminal
            (ρ := Fin (Module.finrank K U₀))
            (κ := fun j : Fin (M + 3) ↦
              throughSubspaceEndpointComplementIndex (reverseVertex V) (reverseEdge V Bv) U₀ j)
            (K := K) (Fin.last (M + 2))) =
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0 (-F3)
          (C (Fin.last (M + 1))) := by
    simpa [hEMat] using hLast
  have hMid' :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        ChartLocalSuffixState.transformedEdge EMat p
            (ChartLocalSuffixState.suffixState EMat
              (Fin.last (M + 2)) p.succ p.succ.le_last) =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
              (Fin (Module.finrank K U₀)) K)
            (C p) := by
    simpa [hEMat] using hMid
  have hLeft' :
      (let p0 : Fin (M + 2) := 0
       let one : Fin (M + 3) := ⟨1, by omega⟩
       ChartLocalSuffixState.transformedEdge EMat p0
            (ChartLocalSuffixState.suffixState EMat
              (Fin.last (M + 2)) one one.le_last) =
          fromBlocks Ctop (-(Ctop * F2))
            (0 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ one)
              (Fin (Module.finrank K U₀)) K)
            (C p0)) := by
    simpa [hEMat] using hLeft
  have hmain :=
    paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc
      (K := K) V Bv U₀ hU₀ Cedge x F2 F3 Ctop C hLast' hMid' hLeft' hCtop
  simpa [Cedge, E, EMat, hEMat] using hmain

/-- The Pi-valued map collecting the literal signed/corrected p. 13
product-difference coordinates:
`Ctop - 1`, `-B`, `lowerLeftBlock L`, and `D - F3 * F2`.

This is finite scalar bookkeeping for the literal block, not analytic
generator transport. -/
def paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    AoyagiProductDifferenceCoordinateIndex
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀
        (Fin.last N))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) → K :=
  let E : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  AoyagiProductDifferenceCoordinateIndex.literalValue
    (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D

/-- The untransformed endpoint product-difference square-sum in the fixed-base
adapted coordinates.

This is the square-sum of the adapted endpoint product matrix minus the
rank-`r` model block `[I,0;0,0]`.  It is not the original DLN/statistical
loss. -/
def paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) : K :=
  let ι := Fin (Module.finrank K U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  aoyagiCoordinateSquareSum
    (fun ij : (ι ⊕ μ) × (ι ⊕ ν) =>
      (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
        fromBlocks (1 : Matrix ι ι K) 0
          (0 : Matrix μ ι K) (0 : Matrix μ ν K)) ij.1 ij.2)

/-- The product of the coordinate square-sums of the deterministic p. 13
triangular endpoint multipliers in the fixed-base adapted coordinates.

This is a pointwise finite quantity.  Local boundedness of this quantity is a
separate analytic/topological input. -/
def paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) : K :=
  let ι := Fin (Module.finrank K U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  aoyagiCoordinateSquareSum
      (fun ij : (ι ⊕ μ) × (ι ⊕ μ) =>
        (fromBlocks (1 : Matrix ι ι K) 0 (lowerLeftBlock S.L)
          (1 : Matrix μ μ K)) ij.1 ij.2) *
    aoyagiCoordinateSquareSum
      (fun ij : (ι ⊕ ν) × (ι ⊕ ν) =>
        (fromBlocks (1 : Matrix ι ι K) (-(S.B)) 0
          (1 : Matrix ν ν K)) ij.1 ij.2)

set_option linter.unusedSectionVars false in
/-- The fixed-base cleaned product-difference coordinate map is the disjoint
sum of the regular block coordinate map and the residual coordinate map. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x =
      Sum.elim
        (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x)
        (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x) := by
  funext c
  cases c <;>
    simp [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      paperEndpointFixedBaseRegularBlockCoordinateMap,
      paperEndpointFixedBaseResidualBlockCoordinateMap]

set_option linter.unusedSectionVars false in
/-- The fixed-base cleaned product-difference coordinate square-sum splits into
the regular coordinate square-sum plus the residual coordinate square-sum.

This is only finite square-sum bookkeeping for the cleaned p. 13 coordinate
family; it is not analytic generator transport from the literal signed block. -/
theorem paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x) =
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x) +
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x) := by
  rw [paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim]
  exact aoyagiCoordinateSquareSum_sumElim
    (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x)
    (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x)

/-- Fixed-base source data for Aoyagi's p. 13 scalar regular coordinates.

This packages the source-produced local certificate, the regular/residual ideal
split, centered continuous scalar regular and residual coordinates, and the
regular-variable/residual-entry counts.  Analytic ideal transport, chart
coverage, Jacobian compatibility, regular-suspension chart construction,
normal crossings, and RLCT remain outside this source-side package. -/
structure PaperEndpointFixedBaseRegularCoordinateSourceData
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ) : Prop where
  dimensionConvention :
    ∀ k : Fin (N + 1), H (k.val + 1) = Module.finrank K (W k)
  localSourceCertificate :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge
  regularCoordinateIdealSourceNeighborhood :
    PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge
  productDifferenceCoordinateIdealSourceNeighborhood :
    PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
      W B U₀ hU₀ x₀ Cedge r rEdge
  scalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  residualScalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  productDifferenceScalarCoordinates_centered_continuousAt :
    PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
      W B U₀ hU₀ x₀ Cedge
  regularCoordinateIndex_card_eq_regularVariableCount :
    Fintype.card
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      aoyagiTheorem2RegularVariableCount N H r
  residualCoordinateIndex_card_eq_endpointResidualEntryCount :
    Fintype.card
        (AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      (H 1 - r) * (H (N + 1) - r)
  productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount :
    Fintype.card
        (AoyagiProductDifferenceCoordinateIndex
          (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) =
      H 1 * H (N + 1)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued regular
block coordinate map. -/
theorem regularBlockCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseRegularBlockCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap,
      PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.scalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap,
      PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.scalarCoordinates_centered_continuousAt c).2

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued residual
block coordinate map. -/
theorem residualBlockCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseResidualBlockCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseResidualBlockCoordinateMap,
      PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.residualScalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseResidualBlockCoordinateMap,
      PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      (sourceData.residualScalarCoordinates_centered_continuousAt c).2

set_option linter.unusedSectionVars false in
/-- The source-data package supplies a centered continuous Pi-valued
product-difference coordinate map. -/
theorem productDifferenceCoordinateMap_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        W B U₀ hU₀ x₀ Cedge H r rEdge) :
    paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge x₀ = 0 ∧
      ContinuousAt
        (paperEndpointFixedBaseProductDifferenceCoordinateMap W B U₀ hU₀ Cedge)
        x₀ := by
  constructor
  · funext c
    simpa [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      (sourceData.productDifferenceScalarCoordinates_centered_continuousAt c).1
  · refine continuousAt_pi.2 ?_
    intro c
    simpa [paperEndpointFixedBaseProductDifferenceCoordinateMap,
      PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      (sourceData.productDifferenceScalarCoordinates_centered_continuousAt c).2

end PaperEndpointFixedBaseRegularCoordinateSourceData

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- A fixed-base local source certificate supplies the regular-coordinate
source-data package once the layer-dimension convention is supplied. -/
theorem regularCoordinateSourceData
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    PaperEndpointFixedBaseRegularCoordinateSourceData
      W B U₀ hU₀ x₀ Cedge H r rEdge where
  dimensionConvention := hH
  localSourceCertificate := cert
  regularCoordinateIdealSourceNeighborhood :=
    cert.regularCoordinateIdealSourceNeighborhood
  productDifferenceCoordinateIdealSourceNeighborhood :=
    cert.productDifferenceCoordinateIdealSourceNeighborhood
  scalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  residualScalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  productDifferenceScalarCoordinates_centered_continuousAt := by
    simpa [PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt] using
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt
        (W := W) (B := B) cert.localCertificate
  regularCoordinateIndex_card_eq_regularVariableCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount
      (W := W) (B := B) cert hH
  residualCoordinateIndex_card_eq_endpointResidualEntryCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
      (W := W) (B := B) cert hH
  productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount :=
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
      (W := W) (B := B) cert hH

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- Source rank data based at `B` produce fixed-base regular/residual coordinate
source data after choosing a total-kernel complement.

The theorem exposes the regular and residual coordinates, their centered
continuity, the regular/residual ideal split, the p. 13 regular-variable
count, and the residual endpoint entry count.  It does not assert exact-rank
openness or any analytic regular-suspension transport field. -/
theorem exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    ∃ U₀ : Submodule K (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointFixedBaseRegularCoordinateSourceData
          W B U₀ hU₀ x₀ Cedge H r rEdge := by
  rcases exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
      W B Cedge r rEdge hCedge hbase hprod hedge with
    ⟨U₀, hU₀, cert⟩
  exact
    ⟨U₀, hU₀,
      cert.regularCoordinateSourceData (W := W) (B := B) hH⟩

set_option linter.unusedSectionVars false in
omit [CompleteSpace K] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, ContinuousSMul K (W i)] in
/-- In the fixed adapted endpoint bases, the base reversed total product is
the rank block `[I,0;0,0]`. -/
theorem paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ (reverseEdge W B) =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (0 : Matrix (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K) := by
  simpa [paperEndpointFixedBaseTotalMatrixOfReverseEdges, paperEndpointAdaptedTotalMatrix,
    paperTotalMap, chainMap_reverse_eq_paper] using
      paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero W B U₀ hU₀

set_option linter.unusedSectionVars false in
/-- The adapted product-difference square-sum is the coordinate square-sum of
the variable endpoint total matrix minus the base endpoint total matrix, both
in the fixed adapted endpoint bases. -/
theorem paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) :
    paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
        (K := K) W B U₀ hU₀ Cedge x =
      aoyagiCoordinateSquareSum
        (fun ij :
          (Fin (Module.finrank K U₀) ⊕
              throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) ×
            (Fin (Module.finrank K U₀) ⊕
              throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) =>
          (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀
              (fun p : Fin N =>
                (Cedge x p :
                  reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) -
            paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀
              (reverseEdge W B)) ij.1 ij.2) := by
  classical
  let ι := Fin (Module.finrank K U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  rw [paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero
    (W := W) (B := B) U₀ hU₀]
  simp [paperEndpointFixedBaseAdaptedProductDifferenceSquareSum]

end FixedBaseCanonicalCertificate

section FixedBaseRealSmallness

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

set_option linter.unusedSectionVars false in
/-- The square-Frobenius endpoint product-difference loss in fixed adapted
endpoint bases.

This is the trace form of the same p. 13 adapted endpoint matrix used by
`paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`.  It is not the
original `lossDLN` on a `Tuple d`, and no basis-change or chart comparison is
asserted here. -/
def paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (x : α) : ℝ :=
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let T : Matrix (ι ⊕ μ) (ι ⊕ ν) ℝ :=
    paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E
  let T0 : Matrix (ι ⊕ μ) (ι ⊕ ν) ℝ :=
    fromBlocks (1 : Matrix ι ι ℝ) 0
      (0 : Matrix μ ι ℝ) (0 : Matrix μ ν ℝ)
  (((T - T0)ᵀ * (T - T0)).trace : ℝ)

set_option linter.unusedSectionVars false in
/-- The fixed adapted endpoint Frobenius loss is exactly the adapted
product-difference coordinate square-sum.

This is finite matrix arithmetic in the fixed endpoint bases.  It does not
compare that fixed-basis endpoint loss with `lossDLN` or any statistical loss
in original network coordinates. -/
theorem paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (x : α) :
    paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
        W B U₀ hU₀ Cedge x =
      paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
        (K := ℝ) W B U₀ hU₀ Cedge x := by
  classical
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let T : Matrix (ι ⊕ μ) (ι ⊕ ν) ℝ :=
    paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E
  let T0 : Matrix (ι ⊕ μ) (ι ⊕ ν) ℝ :=
    fromBlocks (1 : Matrix ι ι ℝ) 0
      (0 : Matrix μ ι ℝ) (0 : Matrix μ ν ℝ)
  simpa [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss,
    paperEndpointFixedBaseAdaptedProductDifferenceSquareSum, E, T, T0, ι, μ, ν] using
    (matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum (M := T - T0))

set_option linter.unusedSectionVars false in
/-- Pointwise comparison form for the existing adapted-loss handoff when the
loss is chosen to be the fixed adapted endpoint Frobenius loss. -/
theorem one_mul_adaptedProductDifferenceSquareSum_le_frobeniusLoss
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (x : α) :
    (1 : ℝ) *
        paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
          (K := ℝ) W B U₀ hU₀ Cedge x ≤
      paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
        W B U₀ hU₀ Cedge x := by
  rw [one_mul, paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum]

set_option linter.unusedSectionVars false in
/-- The fixed-base residual `D`-block coordinate map is measurable whenever
the reversed edge family is measurably given in the fixed endpoint bases.

This is finite Borel bookkeeping for the deterministic p. 13 suffix recursion:
the fixed bases are those attached to the base chain `B`.  The hypothesis is
the actual measurable matrix family consumed by the recursion, so no measurable
structure on arbitrary continuous linear maps is chosen here.  No source-rank
openness, analytic chart construction, density/Jacobian transport, or normal-
crossing statement is asserted. -/
theorem measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) :
    Measurable
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge) := by
  classical
  let ι := Fin (Module.finrank ℝ U₀)
  let κ : Fin (N + 1) → Type :=
    fun j ↦
      throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j
  let E : α → ∀ p : Fin N,
      Matrix (ι ⊕ κ p.succ) (ι ⊕ κ p.castSucc) ℝ :=
    fun x p ↦
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges
        (K := ℝ) W B U₀ hU₀
        (fun q : Fin N ↦
          (Cedge x q : reverseVertex W q.castSucc →ₗ[ℝ] reverseVertex W q.succ)) p
  let S : α →
      ChartLocalSuffixState ι κ ℝ (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hE : Measurable E := by
    simpa [E] using hEdgeMatrix
  have hD :
      Measurable (fun x : α ↦ (S x).D) := by
    simpa [S] using
      (measurable_chartLocalSuffixState_suffixState_fields_real
        (E := E) hE (j := Fin.last N) 0 (Fin.zero_le (Fin.last N))).2.2.2
  refine measurable_pi_lambda _ ?_
  intro c
  rcases c with ⟨i, j⟩
  have hentry : Measurable (fun x : α ↦ (S x).D i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hD)
  simpa [paperEndpointFixedBaseResidualBlockCoordinateMap, E, S,
    AoyagiResidualBlockCoordinateIndex.value, ι, κ] using hentry

namespace PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- A fixed-base product-reduction certificate turns the p. 13 triangular
multiplier comparison into a pointwise adapted product-difference square-sum
bound.

The multiplier square-sum bound is supplied explicitly.  This is not a
comparison with the original DLN/statistical loss. -/
theorem const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseProductReductionCertificate
        (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hbound :
      paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
        (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    c * aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤
      paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
        (K := ℝ) W B U₀ hU₀ Cedge x := by
  classical
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let EMat : ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  let S :
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState EMat (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hSL :
      S.L =
        fromBlocks (1 : Matrix ι ι ℝ) 0 (lowerLeftBlock S.L)
          (1 : Matrix μ μ ℝ) := by
    rcases ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular
        (K := ℝ) EMat (i := 0) (j := Fin.last N)
        (Fin.zero_le (Fin.last N)) with
      ⟨F3, hF3⟩
    rw [hF3]
    rfl
  have hblock :
      IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
        S.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
            fromBlocks (1 : Matrix ι ι ℝ) (-(S.B)) 0 (1 : Matrix ν ν ℝ) =
          fromBlocks S.Ctop 0 0 S.D := by
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E, EMat, S, ι, μ, ν]
      using cert.blockDiagonal
  have htri :
      fromBlocks (1 : Matrix ι ι ℝ) 0 (lowerLeftBlock S.L)
          (1 : Matrix μ μ ℝ) *
        paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
        fromBlocks (1 : Matrix ι ι ℝ) (-(S.B)) 0 (1 : Matrix ν ν ℝ) =
          fromBlocks S.Ctop 0 0 S.D := by
    rw [← hSL]
    exact hblock.2.2
  have hraw :
      c * aoyagiCoordinateSquareSum
          (AoyagiProductDifferenceCoordinateIndex.literalValue
            (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D) ≤
        aoyagiCoordinateSquareSum
          (fun ij : (ι ⊕ μ) × (ι ⊕ ν) =>
            (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
              fromBlocks (1 : Matrix ι ι ℝ) 0
                (0 : Matrix μ ι ℝ) (0 : Matrix μ ν ℝ)) ij.1 ij.2) := by
    refine
      AoyagiProductDifferenceCoordinateIndex.const_mul_literalCoordinateSquareSum_le_productDifferenceSquareSum_of_triangularBlockProduct
        (F2 := -(S.B)) (F3 := lowerLeftBlock S.L)
        (Ctop := S.Ctop) (D := S.D)
        (T := paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E)
        (c := c) (K := Kmul) hc_nonneg hcK ?_ htri
    simpa [paperEndpointFixedBaseTriangularMultiplierSquareSumProduct, E, EMat, S, ι, μ, ν]
      using hbound
  simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
    paperEndpointFixedBaseAdaptedProductDifferenceSquareSum, E, EMat, S, ι, μ, ν] using hraw

set_option linter.unusedSectionVars false in
/-- Frobenius-loss form of the pointwise fixed-base product-reduction bound.

This is the same finite p. 13 comparison as
`const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum`,
after rewriting the adapted endpoint square-sum as the fixed-basis Frobenius
trace form.  It is not a comparison with the original DLN/statistical loss. -/
theorem const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceFrobeniusLoss
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseProductReductionCertificate
        (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hbound :
      paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
        (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    c * aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤
      paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
        W B U₀ hU₀ Cedge x := by
  rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (Cedge := Cedge) (x := x)]
  exact
    const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
      (W := W) (B := B) cert hc_nonneg hcK hbound

set_option linter.unusedSectionVars false in
/-- Source-filter form of the pointwise fixed-base adapted product-difference
bound.

The product-reduction certificate and multiplier square-sum bound are supplied
eventually on the source-rank stratum.  The conclusion is still only an
adapted fixed-base product-difference square-sum bound, not an original-loss
comparison. -/
theorem const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hcert :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    (hbound :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge),
      c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
          (K := ℝ) W B U₀ hU₀ Cedge x := by
  filter_upwards [hcert, hbound] with x hcert_x hbound_x
  exact
    const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
      (W := W) (B := B) hcert_x hc_nonneg hcK hbound_x

set_option linter.unusedSectionVars false in
/-- Source-filter Frobenius-loss form of the fixed-base product-reduction
bound.

This only rewrites the adapted endpoint square-sum by the fixed-basis
Frobenius identity.  It does not compare to `lossDLN` or a statistical loss in
original coordinates. -/
theorem const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hcert :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    (hbound :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge),
      c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
          W B U₀ hU₀ Cedge x := by
  filter_upwards [
    const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source
      (W := W) (B := B) hc_nonneg hcK hcert hbound] with x hx
  rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (Cedge := Cedge) (x := x)]
  exact hx

end PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- The fixed-base p.13 triangular multiplier square-sum product is locally
bounded near any continuous edge family satisfying the recursive determinant
charts at the base point. -/
theorem paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_of_recursiveDetCharts
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    (hCedge : ContinuousAt Cedge x₀)
    (hchart₀ :
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts
        (K := ℝ) W B U₀ hU₀ Cedge x₀) :
    ∃ Kmul : ℝ, 0 < Kmul ∧
      ∀ᶠ x in nhds x₀,
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul := by
  classical
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : α → ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  let Lmul : α → Matrix (ι ⊕ μ) (ι ⊕ μ) ℝ :=
    fun x ↦
      fromBlocks (1 : Matrix ι ι ℝ) 0 (lowerLeftBlock (S x).L)
        (1 : Matrix μ μ ℝ)
  let Rmul : α → Matrix (ι ⊕ ν) (ι ⊕ ν) ℝ :=
    fun x ↦
      fromBlocks (1 : Matrix ι ι ℝ) (-(S x).B) 0
        (1 : Matrix ν ν ℝ)
  have hfields :
      IsUnit ((S x₀).Ctop.det) ∧
        ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
        ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
        ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
    simpa [E, S, ι, μ, ν, paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts] using
      paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt
        (K := ℝ) W B U₀ hU₀ Cedge hCedge hchart₀
  rcases hfields with ⟨_, _, hB, hL, _⟩
  have hLmul : ContinuousAt Lmul x₀ := by
    have hfrom : Continuous
        (fun F3 : Matrix μ ι ℝ ↦
          fromBlocks (1 : Matrix ι ι ℝ) 0 F3 (1 : Matrix μ μ ℝ)) :=
      continuous_const.matrix_fromBlocks continuous_const continuous_id continuous_const
    exact hfrom.continuousAt.comp hL
  have hRmul : ContinuousAt Rmul x₀ := by
    have hfrom : Continuous
        (fun F2 : Matrix ι ν ℝ ↦
          fromBlocks (1 : Matrix ι ι ℝ) F2 0 (1 : Matrix ν ν ℝ)) :=
      continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
    exact hfrom.continuousAt.comp hB
  have hLcoord :
      ContinuousAt
        (fun x : α ↦ fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦
          Lmul x ij.1 ij.2) x₀ := by
    refine continuousAt_pi.2 ?_
    intro ij
    exact (continuous_apply ij.2).continuousAt.comp
      ((continuous_apply ij.1).continuousAt.comp hLmul)
  have hRcoord :
      ContinuousAt
        (fun x : α ↦ fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦
          Rmul x ij.1 ij.2) x₀ := by
    refine continuousAt_pi.2 ?_
    intro ij
    exact (continuous_apply ij.2).continuousAt.comp
      ((continuous_apply ij.1).continuousAt.comp hRmul)
  have hSL :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦ Lmul x ij.1 ij.2)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hLcoord
  have hSR :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦ Rmul x ij.1 ij.2)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hRcoord
  have hprod :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
              (fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦ Lmul x ij.1 ij.2) *
            aoyagiCoordinateSquareSum
              (fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦ Rmul x ij.1 ij.2)) x₀ :=
    hSL.mul hSR
  rcases continuousAt_exists_pos_eventually_le hprod with
    ⟨Kmul, hKmul_pos, hKmul⟩
  refine ⟨Kmul, hKmul_pos, ?_⟩
  filter_upwards [hKmul] with x hx
  simpa [paperEndpointFixedBaseTriangularMultiplierSquareSumProduct,
    E, S, Lmul, Rmul, ι, μ, ν] using hx

set_option linter.unusedSectionVars false in
/-- The fixed-base p. 13 triangular multiplier square-sum product is locally
bounded near a continuous edge family based at the paper chain `B`.

This is only local boundedness of the deterministic finite multiplier
square-sum product; it is not a comparison with the original DLN/statistical
loss. -/
theorem paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∃ Kmul : ℝ, 0 < Kmul ∧
      ∀ᶠ x in nhds x₀,
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul := by
  classical
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : α → ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let S : α →
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  let Lmul : α → Matrix (ι ⊕ μ) (ι ⊕ μ) ℝ :=
    fun x ↦
      fromBlocks (1 : Matrix ι ι ℝ) 0 (lowerLeftBlock (S x).L)
        (1 : Matrix μ μ ℝ)
  let Rmul : α → Matrix (ι ⊕ ν) (ι ⊕ ν) ℝ :=
    fun x ↦
      fromBlocks (1 : Matrix ι ι ℝ) (-(S x).B) 0
        (1 : Matrix ν ν ℝ)
  have hfields :
      IsUnit ((S x₀).Ctop.det) ∧
        ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
        ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
        ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
    simpa [E, S, ι, μ, ν] using
      paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt
        (K := ℝ) W B U₀ hU₀ Cedge hCedge hbase
  rcases hfields with ⟨_, _, hB, hL, _⟩
  have hLmul : ContinuousAt Lmul x₀ := by
    have hfrom : Continuous
        (fun F3 : Matrix μ ι ℝ ↦
          fromBlocks (1 : Matrix ι ι ℝ) 0 F3 (1 : Matrix μ μ ℝ)) :=
      continuous_const.matrix_fromBlocks continuous_const continuous_id continuous_const
    exact hfrom.continuousAt.comp hL
  have hRmul : ContinuousAt Rmul x₀ := by
    have hfrom : Continuous
        (fun F2 : Matrix ι ν ℝ ↦
          fromBlocks (1 : Matrix ι ι ℝ) F2 0 (1 : Matrix ν ν ℝ)) :=
      continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
    exact hfrom.continuousAt.comp hB
  have hLcoord :
      ContinuousAt
        (fun x : α ↦ fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦
          Lmul x ij.1 ij.2) x₀ := by
    refine continuousAt_pi.2 ?_
    intro ij
    exact (continuous_apply ij.2).continuousAt.comp
      ((continuous_apply ij.1).continuousAt.comp hLmul)
  have hRcoord :
      ContinuousAt
        (fun x : α ↦ fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦
          Rmul x ij.1 ij.2) x₀ := by
    refine continuousAt_pi.2 ?_
    intro ij
    exact (continuous_apply ij.2).continuousAt.comp
      ((continuous_apply ij.1).continuousAt.comp hRmul)
  have hSL :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦ Lmul x ij.1 ij.2)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hLcoord
  have hSR :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
            (fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦ Rmul x ij.1 ij.2)) x₀ :=
    aoyagiCoordinateSquareSum_continuousAt hRcoord
  have hprod :
      ContinuousAt
        (fun x : α ↦
          aoyagiCoordinateSquareSum
              (fun ij : (ι ⊕ μ) × (ι ⊕ μ) ↦ Lmul x ij.1 ij.2) *
            aoyagiCoordinateSquareSum
              (fun ij : (ι ⊕ ν) × (ι ⊕ ν) ↦ Rmul x ij.1 ij.2)) x₀ :=
    hSL.mul hSR
  rcases continuousAt_exists_pos_eventually_le hprod with
    ⟨Kmul, hKmul_pos, hKmul⟩
  refine ⟨Kmul, hKmul_pos, ?_⟩
  filter_upwards [hKmul] with x hx
  simpa [paperEndpointFixedBaseTriangularMultiplierSquareSumProduct,
    E, S, Lmul, Rmul, ι, μ, ν] using hx

set_option linter.unusedSectionVars false in
/-- Source-filter form of local boundedness for the fixed-base p. 13
triangular multiplier square-sum product.  No openness of the source stratum is
asserted or used. -/
theorem paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∃ Kmul : ℝ, 0 < Kmul ∧
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul := by
  rcases
      paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) hCedge hbase with
    ⟨Kmul, hKmul_pos, hKmul⟩
  exact
    ⟨Kmul, hKmul_pos,
      (inf_le_left :
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀) hKmul⟩

set_option linter.unusedSectionVars false in
/-- In the self-base case, the triangular multiplier square-sum product for the
explicit multi-edge source-dependent p.13 product-coordinate family is
uniformly bounded on a small source/regular-coordinate product neighborhood. -/
theorem exists_pos_radius_le_pos_const_triangularMultiplierSquareSumProduct_eventually_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    {r : ℕ} (rEdge : Fin (M + 2) → ℕ) {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, ∃ Kmul : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < Kmul ∧
      let Coord :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) ≤ Kmul := by
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let u₀ : EuclideanSpace ℝ Coord := 0
  have hCedgeProd :
      ContinuousAt CedgeProd (x₀, u₀) := by
    simpa [CedgeProd, Coord, u₀] using
      continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀) (u₀ := u₀)
        (CedgeBase := CedgeBase) hCedgeBase hbase
  have hCtop₀ :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix
          (fun c : Coord ↦ u₀ c)).det := by
    simp [Coord, u₀]
  have hcert₀ :
      PaperEndpointFixedBaseProductReductionCertificate
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd rEdge (x₀, u₀) :=
    paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (x := x₀) (u := u₀) (rEdge := rEdge) hCtop₀
  rcases
      paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_of_recursiveDetCharts
        (W := V) (B := Bv) (x₀ := (x₀, u₀))
        (U₀ := U₀) (hU₀ := hU₀) (Cedge := CedgeProd)
        hCedgeProd hcert₀.detCharts with
    ⟨Kmul, hKmul, hbound_nhds⟩
  rcases
      exists_pos_ball_eventually_forall_mem_of_mem_nhds_prod_zero
        (α := α) (η := Coord)
        (s := {xu : α × EuclideanSpace ℝ Coord |
          paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd xu ≤ Kmul})
        hbound_nhds with
    ⟨R₀, hR₀, hbound_prod⟩
  let R := min R₀ Rmax
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hR₀ hRmax
  have hR_le_R₀ : R ≤ R₀ := by
    dsimp [R]
    exact min_le_left _ _
  have hR_le_Rmax : R ≤ Rmax := by
    dsimp [R]
    exact min_le_right _ _
  refine ⟨R, Kmul, hR, hR_le_Rmax, hKmul, ?_⟩
  dsimp only
  exact
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) ≤ nhds x₀)
      ((hbound_prod).mono (fun x hx u hu ↦
        hx u (Metric.ball_subset_ball hR_le_R₀ hu)))

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Measurability of the residual square-sum positive set follows from
measurability of the residual coordinate map. -/
theorem measurableSet_residualSquareSum_pos_of_measurable
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    (hmeas :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge)) :
    MeasurableSet {x : α |
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)} := by
  have hsquare :
      Measurable (fun x : α =>
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) :=
    measurable_aoyagiCoordinateSquareSum hmeas
  simpa [Set.preimage] using hsquare measurableSet_Ioi

set_option linter.unusedSectionVars false in
/-- The real fixed-base source-data package gives a neighborhood where the
actual p. 13 `F2` and `F3` regular-coordinate square-sums are jointly small. -/
theorem regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    let ι := Fin (Module.finrank ℝ U₀)
    let μ :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
    let ν :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let coord : α → AoyagiRegularBlockCoordinateIndex ι μ ν → ℝ :=
    paperEndpointFixedBaseRegularBlockCoordinateMap (K := ℝ) W B U₀ hU₀ Cedge
  have hcenter :
      coord x₀ = 0 ∧ ContinuousAt coord x₀ := by
    simpa [coord, ι, μ, ν] using
      regularBlockCoordinateMap_centered_continuousAt
        (W := W) (B := B) sourceData
  have hcoord :
      ∀ c : AoyagiRegularBlockCoordinateIndex ι μ ν,
        coord x₀ c = 0 ∧ ContinuousAt (fun x : α => coord x c) x₀ := by
    intro c
    exact
      ⟨congrFun hcenter.1 c,
        (continuous_apply c).continuousAt.comp hcenter.2⟩
  simpa [coord, ι, μ, ν] using
    AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
        (coord := coord) (x₀ := x₀) hcoord

set_option linter.unusedSectionVars false in
/-- The same smallness conclusion holds relative to the source-rank stratum,
because it has already been proved in an ambient neighborhood. -/
theorem regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    let ι := Fin (Module.finrank ℝ U₀)
    let μ :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
    let ν :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inl (β := μ × ι) ij))) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι =>
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x
              (Sum.inr (α := ι × ι) (Sum.inr (α := ι × ν) ij))) ≤
          1 := by
  exact
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀)
      (regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- For the actual real fixed-base product-difference coordinate maps, the
literal signed/corrected square-sum and the cleaned square-sum are locally
equivalent up to factor `2`. -/
theorem literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ∧
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  have hsmall :=
    regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
      (W := W) (B := B) sourceData
  filter_upwards [hsmall] with x hxsmall
  let E : ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hsmallS :
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν => (-(S.B)) ij.1 ij.2) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι => lowerLeftBlock S.L ij.1 ij.2) ≤
          1 := by
    simpa [paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, ι, μ, ν] using hxsmall
  constructor
  · simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
      paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, ι, μ, ν] using
      AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
          (X := S.Ctop - 1) (F2 := -(S.B)) (F3 := lowerLeftBlock S.L) (D := S.D)
          hsmallS
  · simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
      paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, ι, μ, ν] using
      AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
          (X := S.Ctop - 1) (F2 := -(S.B)) (F3 := lowerLeftBlock S.L) (D := S.D)
          hsmallS

set_option linter.unusedSectionVars false in
/-- Directional form of the local factor-`2` comparison: the literal
signed/corrected square-sum is bounded by twice the cleaned square-sum. -/
theorem literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.1)

set_option linter.unusedSectionVars false in
/-- Directional form of the local factor-`2` comparison: the cleaned square-sum
is bounded by twice the literal signed/corrected square-sum. -/
theorem productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in nhds x₀,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.2)

set_option linter.unusedSectionVars false in
/-- The same factor-`2` comparison holds relative to the source-rank stratum,
as a filter weakening of the ambient comparison. -/
theorem literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ∧
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          2 * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀)
      (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- On the source-rank stratum filter, the literal signed/corrected p. 13
square-sum is locally equivalent up to factor `2` to the sum of the regular
block square-sum and the residual block square-sum.

This is a source-side finite loss comparison only.  It does not assert
regular-coordinate analytic status, prove a Fubini/polar shift, construct a
full regular-suspension chart, or extract an RLCT. -/
theorem literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  refine
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono ?_
  intro x hx
  rw [paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
    (K := ℝ) W B U₀ hU₀ Cedge x] at hx
  exact hx

set_option linter.unusedSectionVars false in
/-- On the source-rank stratum filter, the literal signed/corrected p. 13
square-sum is locally bounded below by one half of the regular-plus-residual
cleaned square-sum.

This is the lower-bound direction of the finite p. 13 comparison.  It does
not prove that an ambient DLN loss is comparable to the literal square-sum;
that triangular/determinant-chart comparison remains a supplied input. -/
theorem literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      (1 / 2 : ℝ) *
        (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  refine
    (literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono ?_
  intro x hx
  nlinarith [hx.2]

set_option linter.unusedSectionVars false in
/-- A supplied lower bound of an ambient loss by a positive multiple of the
literal p. 13 square-sum gives, on the source-rank stratum filter, a lower
bound by the regular-plus-residual cleaned square-sum with the constant halved.

This theorem only packages the finite p. 13 comparison.  The hypothesis
`hloss` is where any determinant-chart triangular-multiplier comparison with
the original DLN loss must be supplied. -/
theorem const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {loss : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤ loss x) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      (c / 2) *
        (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ≤ loss x := by
  have hhalf :=
    literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
      (W := W) (B := B) sourceData
  filter_upwards [hhalf, hloss] with x hhalf_x hloss_x
  have hmul := mul_le_mul_of_nonneg_left hhalf_x hc
  calc
    (c / 2) *
        (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x))
        = c * ((1 / 2 : ℝ) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x))) := by
          ring
    _ ≤ c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := hmul
    _ ≤ loss x := hloss_x

set_option linter.unusedSectionVars false in
/-- If the fixed-base product-reduction certificate and triangular multiplier
square-sum bound hold eventually on the source-rank stratum, then the adapted
fixed-base product-difference square-sum is eventually bounded below by the
cleaned regular-plus-residual p. 13 square-sum, with the usual factor `1/2`.

This composes the pointwise adapted product-difference bound with the finite
literal/cleaned p. 13 comparison.  The adapted product-difference square-sum
is not the original DLN/statistical loss. -/
theorem half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hcert :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    (hbound :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge),
      (c / 2) *
        (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
        paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
          (K := ℝ) W B U₀ hU₀ Cedge x := by
  have hloss :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) ≤
          paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W B U₀ hU₀ Cedge x :=
    PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source
      (W := W) (B := B) hc_nonneg hcK hcert hbound
  exact
    const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
      (W := W) (B := B) sourceData hc_nonneg hloss

set_option linter.unusedSectionVars false in
/-- Frobenius-loss form of the source-rank fixed-base product-reduction
lower bound.

This composes the finite p. 13 literal/cleaned comparison with the
product-reduction certificate and then rewrites the adapted endpoint
square-sum as the fixed-basis Frobenius trace form.  It is not an
original-coordinate DLN loss comparison. -/
theorem half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_of_productReductionCertificate_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {c Kmul : ℝ}
    (hc_nonneg : 0 ≤ c) (hcK : c * Kmul ≤ 1)
    (hcert :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x)
    (hbound :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
          (K := ℝ) W B U₀ hU₀ Cedge x ≤ Kmul) :
    ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge),
      (c / 2) *
        (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
        paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
          W B U₀ hU₀ Cedge x := by
  filter_upwards [
    half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source
      (W := W) (B := B) sourceData hc_nonneg hcK hcert hbound] with x hx
  rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (Cedge := Cedge) (x := x)]
  exact hx

set_option linter.unusedSectionVars false in
/-- At a continuous fixed-base paper chain, the adapted fixed-base
product-difference square-sum is locally bounded below by a positive constant
times the cleaned regular-plus-residual p. 13 square-sum.

This theorem removes the separately supplied product-reduction certificate and
triangular multiplier bound from the previous wrapper by deriving both near
the base.  The conclusion is still a comparison with the adapted fixed-base
product-difference square-sum, not with the original DLN/statistical loss. -/
theorem exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
          paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W B U₀ hU₀ Cedge x := by
  rcases
      paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge hbase with
    ⟨Kmul, hKmul_pos, hbound⟩
  let c : ℝ := Kmul⁻¹
  have hc_pos : 0 < c := by
    exact inv_pos.mpr hKmul_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hcK : c * Kmul ≤ 1 := by
    dsimp [c]
    rw [inv_mul_cancel₀ (ne_of_gt hKmul_pos)]
  have hcert_nhds :
      {x : α |
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x} ∈ nhds x₀ :=
    paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
      (K := ℝ) W B U₀ hU₀ Cedge rEdge hCedge hbase
  have hcert :
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        PaperEndpointFixedBaseProductReductionCertificate
          (K := ℝ) W B U₀ hU₀ Cedge rEdge x :=
    (inf_le_left :
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) ≤ nhds x₀) hcert_nhds
  exact
    ⟨c, hc_pos,
      half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source
        (W := W) (B := B) sourceData hc_nonneg hcK hcert hbound⟩

set_option linter.unusedSectionVars false in
/-- At a continuous fixed-base paper chain, the fixed adapted endpoint
Frobenius product-difference loss is locally bounded below by a positive
constant times the cleaned regular-plus-residual p. 13 square-sum.

This is the fixed-basis Frobenius rewrite of the existing adapted square-sum
lower bound.  It does not compare with the original DLN/statistical loss. -/
theorem exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_selfBase_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
          paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
            W B U₀ hU₀ Cedge x := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
        (W := W) (B := B) sourceData hCedge hbase with
    ⟨c, hc_pos, hbound⟩
  refine ⟨c, hc_pos, ?_⟩
  filter_upwards [hbound] with x hx
  rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (Cedge := Cedge) (x := x)]
  exact hx

set_option linter.unusedSectionVars false in
/-- Relative directional form: on the source-rank stratum filter, the literal
signed/corrected square-sum is bounded by twice the cleaned square-sum. -/
theorem literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.1)

set_option linter.unusedSectionVars false in
/-- Relative directional form: on the source-rank stratum filter, the cleaned
square-sum is bounded by twice the literal signed/corrected square-sum. -/
theorem productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤
        2 * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    (literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
      (W := W) (B := B) sourceData).mono (fun _ hx => hx.2)

set_option linter.unusedSectionVars false in
/-- Pointwise form: `F2/F3` smallness for the fixed-base p. 13 regular block
implies the cleaned product-difference square-sum is bounded by twice the
literal signed/corrected square-sum. -/
theorem productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {x : α}
    (hsmall :
      paperEndpointFixedBaseRegularBlockF2F3SquareSum
          (W := W) (B := B) U₀ hU₀ Cedge x ≤ 1) :
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseProductDifferenceCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤
      2 * aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) := by
  let ι := Fin (Module.finrank ℝ U₀)
  let μ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)
  let ν :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀ 0
  let E : ∀ p : Fin N,
      Matrix
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (ι ⊕ throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) ℝ :=
    fun p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let S :
      ChartLocalSuffixState ι
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        ℝ (Fin.last N) 0 :=
    ChartLocalSuffixState.suffixState E (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hsmallS :
      aoyagiCoordinateSquareSum
          (fun ij : ι × ν => (-(S.B)) ij.1 ij.2) +
        aoyagiCoordinateSquareSum
          (fun ij : μ × ι => lowerLeftBlock S.L ij.1 ij.2) ≤
          1 := by
    simpa [paperEndpointFixedBaseRegularBlockF2F3SquareSum,
      paperEndpointFixedBaseRegularBlockCoordinateMap, E, S, ι, μ, ν] using hsmall
  simpa [paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap,
      paperEndpointFixedBaseProductDifferenceCoordinateMap, E, S, ι, μ, ν] using
    AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
        (X := S.Ctop - 1) (F2 := -(S.B)) (F3 := lowerLeftBlock S.L) (D := S.D)
        hsmallS

set_option linter.unusedSectionVars false in
/-- The fixed-base p. 13 `F2/F3` square-sum is bounded by the full regular
coordinate square-sum. -/
theorem paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {x : α} :
    paperEndpointFixedBaseRegularBlockF2F3SquareSum
        (W := W) (B := B) U₀ hU₀ Cedge x ≤
      aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) := by
  simpa [paperEndpointFixedBaseRegularBlockF2F3SquareSum] using
    AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_add_le_coordinateSquareSum
      (coord :=
        paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x)

set_option linter.unusedSectionVars false in
/-- If the regular block coordinates are the Euclidean parameter `u` and the
regular radius is at most `1`, then the p. 13 `F2/F3` square-sum is small. -/
theorem paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {x : α} {Rmax : ℝ}
    {u : EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0))}
    (hregular :
      paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge x = fun i => u i)
    (hu :
      u ∈ Metric.ball
        (0 : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax)
    (hRmax_le_one : Rmax ≤ 1) :
    paperEndpointFixedBaseRegularBlockF2F3SquareSum
        (W := W) (B := B) U₀ hU₀ Cedge x ≤ 1 := by
  have hsub :
      paperEndpointFixedBaseRegularBlockF2F3SquareSum
          (W := W) (B := B) U₀ hU₀ Cedge x ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) :=
    paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (x := x)
  have hu_square :
      aoyagiCoordinateSquareSum (fun i => u i) ≤ 1 :=
    aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one hu hRmax_le_one
  have hregular_square :
      aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) ≤ 1 := by
    rw [hregular]
    exact hu_square
  exact hsub.trans hregular_square

set_option linter.unusedSectionVars false in
/-- Product-family form of the radius-derived p. 13 `F2/F3` smallness. -/
theorem paperEndpointFixedBaseRegularBlockF2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {Rmax : ℝ}
    (hregular :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = fun i => u i)
    (hRmax_le_one : Rmax ≤ 1) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge),
      ∀ u : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        u ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
          paperEndpointFixedBaseRegularBlockF2F3SquareSum
            (W := W) (B := B) U₀ hU₀ CedgeProd (x, u) ≤ 1 := by
  filter_upwards [hregular] with x hregular_x
  intro u hu
  exact
    paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := CedgeProd) (x := (x, u)) (u := u)
      (hregular_x u hu) hu hRmax_le_one

set_option linter.unusedSectionVars false in
/-- Product-family form: a supplied `F2/F3` smallness bound on the product
family gives the cleaned-to-literal comparison required by the product
coordinate socket. -/
theorem productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {Rmax : ℝ}
    (hsmall :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockF2F3SquareSum
              (W := W) (B := B) U₀ hU₀ CedgeProd (x, u) ≤ 1) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge),
      ∀ u : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        u ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) ≤
            2 * aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) := by
  filter_upwards [hsmall] with x hx
  intro u hu
  exact
    productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := CedgeProd) (x := (x, u)) (hx u hu)

set_option linter.unusedSectionVars false in
/-- Product-coordinate shape from component coordinate identities.

If the product family has regular-block coordinates exactly `u` and residual
block coordinates equal to the base residual coordinates, then the cleaned
p.13 product-difference square-sum has the shape
`residualSquareSumBase(x) + squareSum(u)`. -/
theorem productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {Rmax : ℝ}
    (hregular :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = fun i => u i)
    (hresidual :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) =
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x) :
    ∀ᶠ x in
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge),
      ∀ u : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        u ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) =
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i) := by
  filter_upwards [hregular, hresidual] with x hregular_x hresidual_x
  intro u hu
  calc
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseProductDifferenceCoordinateMap
          (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) =
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) +
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) := by
        exact
          paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
            (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)
    _ =
      aoyagiCoordinateSquareSum (fun i => u i) +
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x) := by
        rw [hregular_x u hu, hresidual_x u hu]
    _ =
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x) +
        aoyagiCoordinateSquareSum (fun i => u i) := by
        rw [add_comm]

set_option linter.unusedSectionVars false in
/-- Product-coordinate socket for the p.13 adapted square-sum lower bound.

If a supplied product family has the cleaned p.13 square-sum
`residualSquareSumBase(x) + squareSum(u)`, the cleaned square-sum is controlled
by the literal signed/corrected square-sum, and the product-reduction
certificate has uniformly bounded triangular multipliers, then the adapted
product-difference square-sum has the lower-bound shape consumed by the local
finite-integral front ends.

This theorem does not construct the product chart or prove the product-shape
hypotheses. -/
theorem exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {Rmax Kmul : ℝ}
    (hRmax : 0 < Rmax)
    (hKmul : 0 < Kmul)
    (hshape :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseProductDifferenceCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) =
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
                aoyagiCoordinateSquareSum (fun i => u i))
    (hclean_le_literal :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseProductDifferenceCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) ≤
              2 * aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)))
    (hcert :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) W B U₀ hU₀ CedgeProd rEdge (x, u))
    (hmult_bound :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ Kmul) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
  classical
  have _hRmax : 0 < Rmax := hRmax
  let cLit : ℝ := Kmul⁻¹
  have hcLit_nonneg : 0 ≤ cLit := by
    exact inv_nonneg.mpr (le_of_lt hKmul)
  have hcLit_pos : 0 < cLit := by
    exact inv_pos.mpr hKmul
  have hcLitK : cLit * Kmul ≤ 1 := by
    rw [show cLit * Kmul = 1 by
      simp [cLit, inv_mul_cancel₀ (ne_of_gt hKmul)]]
  refine ⟨cLit / 2, half_pos hcLit_pos, ?_⟩
  filter_upwards [hshape, hclean_le_literal, hcert, hmult_bound] with x hshape_x
    hclean_x hcert_x hmult_x
  intro u hu
  let cleaned :=
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseProductDifferenceCoordinateMap
        (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
  let literal :=
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
        (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
  let baseRegularResidual :=
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ CedgeBase x) +
      aoyagiCoordinateSquareSum (fun i => u i)
  have hshape_xu : cleaned = baseRegularResidual := by
    simpa [cleaned, baseRegularResidual] using hshape_x u hu
  have hclean_xu : cleaned ≤ 2 * literal := by
    simpa [cleaned, literal] using hclean_x u hu
  have hlit_to_adapted :
      cLit * literal ≤
        paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
          (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
    simpa [literal, cLit] using
      PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
        (W := W) (B := B) (cert := hcert_x u hu)
        (c := cLit) (Kmul := Kmul) hcLit_nonneg hcLitK (hmult_x u hu)
  calc
    (cLit / 2) * baseRegularResidual = (cLit / 2) * cleaned := by
      rw [hshape_xu]
    _ ≤ cLit * literal := by
      nlinarith
    _ ≤ paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
          (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := hlit_to_adapted

set_option linter.unusedSectionVars false in
/-- Product-coordinate socket with the cleaned-to-literal comparison derived
from supplied product-family `F2/F3` smallness. -/
theorem exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {Rmax Kmul : ℝ}
    (hRmax : 0 < Rmax)
    (hKmul : 0 < Kmul)
    (hshape :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseProductDifferenceCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) =
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
                aoyagiCoordinateSquareSum (fun i => u i))
    (hsmall :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockF2F3SquareSum
              (W := W) (B := B) U₀ hU₀ CedgeProd (x, u) ≤ 1)
    (hcert :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) W B U₀ hU₀ CedgeProd rEdge (x, u))
    (hmult_bound :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ Kmul) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
  exact
    exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
      (r := r) (rEdge := rEdge) (Rmax := Rmax) (Kmul := Kmul)
      hRmax hKmul hshape
      (productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one
        (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
        (r := r) (rEdge := rEdge) (Rmax := Rmax) hsmall)
      hcert hmult_bound

set_option linter.unusedSectionVars false in
/-- Product-coordinate socket with both finite-coordinate assumptions exposed:
regular/residual component identities give the square-sum shape, and
product-family `F2/F3` smallness gives the cleaned-to-literal comparison. -/
theorem exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {Rmax Kmul : ℝ}
    (hRmax : 0 < Rmax)
    (hKmul : 0 < Kmul)
    (hregular :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = fun i => u i)
    (hresidual :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) =
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x)
    (hsmall :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockF2F3SquareSum
              (W := W) (B := B) U₀ hU₀ CedgeProd (x, u) ≤ 1)
    (hcert :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) W B U₀ hU₀ CedgeProd rEdge (x, u))
    (hmult_bound :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ Kmul) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
  exact
    exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
      (r := r) (rEdge := rEdge) (Rmax := Rmax) (Kmul := Kmul)
      hRmax hKmul
      (productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq
        (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
        (r := r) (rEdge := rEdge) (Rmax := Rmax) hregular hresidual)
      hsmall hcert hmult_bound

set_option linter.unusedSectionVars false in
/-- Product-coordinate socket with the product-family `F2/F3` smallness
derived from literal regular-coordinate equality and a radius bound `Rmax ≤ 1`.

The strict positivity `0 < Rmax` is retained as the existing socket's
positive-radius interface condition; the finite `F2/F3` smallness derivation
itself only uses `Rmax ≤ 1`. -/
theorem exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {Rmax Kmul : ℝ}
    (hRmax : 0 < Rmax)
    (hRmax_le_one : Rmax ≤ 1)
    (hKmul : 0 < Kmul)
    (hregular :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = fun i => u i)
    (hresidual :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) =
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x)
    (hcert :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) W B U₀ hU₀ CedgeProd rEdge (x, u))
    (hmult_bound :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ Kmul) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
  exact
    exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
      (r := r) (rEdge := rEdge) (Rmax := Rmax) (Kmul := Kmul)
      hRmax hKmul hregular hresidual
      (paperEndpointFixedBaseRegularBlockF2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
        (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
        (r := r) (rEdge := rEdge) (Rmax := Rmax) hregular hRmax_le_one)
      hcert hmult_bound

end PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Self-base source-dependent p.13 product-family lower bound against the
adapted fixed-base product-difference square-sum.

This combines the small-ball coordinate identities, the pointwise
product-reduction certificate, and the local triangular-multiplier bound for
the explicit multi-edge product-coordinate family. -/
theorem exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    {r : ℕ} (rEdge : Fin (M + 2) → ℕ) {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, ∃ c : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧
      let Coord :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
  let Rcap := min Rmax 1
  have hRcap : 0 < Rcap := by
    dsimp [Rcap]
    exact lt_min hRmax zero_lt_one
  have hRcap_le_Rmax : Rcap ≤ Rmax := by
    dsimp [Rcap]
    exact min_le_left _ _
  have hRcap_le_one : Rcap ≤ 1 := by
    dsimp [Rcap]
    exact min_le_right _ _
  rcases
      exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (r := r) (rEdge := rEdge)
        (Rmax := Rcap) hRcap with
    ⟨Rcoord, hRcoord, hRcoord_le, hcoord⟩
  dsimp only at hcoord
  rcases hcoord with ⟨hregular_coord, hresidual_coord⟩
  rcases
      exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (r := r) (rEdge := rEdge)
        (Rmax := Rcoord) hRcoord with
    ⟨Rcert, hRcert, hRcert_le, hcert_eventual⟩
  dsimp only at hcert_eventual
  rcases
      exists_pos_radius_le_pos_const_triangularMultiplierSquareSumProduct_eventually_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) hCedgeBase hbase
        (r := r) (rEdge := rEdge) (Rmax := Rcert) hRcert with
    ⟨R, Kmul, hR, hR_le_Rcert, hKmul, hmult_bound⟩
  dsimp only at hmult_bound
  have hR_le_Rcoord : R ≤ Rcoord := hR_le_Rcert.trans hRcert_le
  have hR_le_Rcap : R ≤ Rcap := hR_le_Rcoord.trans hRcoord_le
  have hR_le_Rmax : R ≤ Rmax := hR_le_Rcap.trans hRcap_le_Rmax
  have hR_le_one : R ≤ 1 := hR_le_Rcap.trans hRcap_le_one
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  have hregular :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) = fun i => u i :=
    hregular_coord.mono (fun x hx u hu ↦
      hx u (Metric.ball_subset_ball hR_le_Rcoord hu))
  have hresidual :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x :=
    hresidual_coord.mono (fun x hx u hu ↦
      hx u (Metric.ball_subset_ball hR_le_Rcoord hu))
  have hcert :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd rEdge (x, u) :=
    hcert_eventual.mono (fun x hx u hu ↦
      hx u (Metric.ball_subset_ball hR_le_Rcert hu))
  rcases
      PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source
        (W := V) (B := Bv) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (CedgeProd := CedgeProd)
        (r := r) (rEdge := rEdge) (Rmax := R) (Kmul := Kmul)
        hR hR_le_one hKmul hregular hresidual hcert hmult_bound with
    ⟨c, hc, hineq⟩
  refine ⟨R, c, hR, hR_le_Rmax, hc, ?_⟩
  simpa [Coord, CedgeProd] using hineq

set_option linter.unusedSectionVars false in
/-- Source rank data produce fixed-base regular-coordinate source data and the
source-stratum factor-`2` comparison between the literal and cleaned p. 13
product-difference square-sums.

This is only a source-side finite square-sum wrapper.  It does not construct a
regular-suspension chart, prove analytic ideal transport, compute a Jacobian,
produce normal crossings, or extract an RLCT. -/
theorem exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank ℝ (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank ℝ (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank ℝ (W k)) :
    ∃ U₀ : Submodule ℝ (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointFixedBaseRegularCoordinateSourceData
            (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge ∧
          ∀ᶠ x in
            nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge),
            aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) ≤
                2 * aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) ∧
              aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) ≤
                2 * aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) := by
  rcases exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
      (K := ℝ) W B Cedge H r rEdge hCedge hbase hprod hedge hH with
    ⟨U₀, hU₀, sourceData⟩
  exact
    ⟨U₀, hU₀, sourceData,
      PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
          (W := W) (B := B) sourceData⟩

set_option linter.unusedSectionVars false in
/-- Source rank data produce fixed-base regular-coordinate source data and the
source-stratum half lower bound of the literal p. 13 square-sum by the cleaned
regular-plus-residual square-sum.

This is only source-side finite square-sum bookkeeping.  It does not supply a
comparison with the original DLN loss, construct a regular-suspension chart,
compute a Jacobian, produce normal crossings, or extract an RLCT. -/
theorem exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (H : ℕ → ℕ) (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank ℝ (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank ℝ (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hH : ∀ k : Fin (N + 1),
      H (k.val + 1) = Module.finrank ℝ (W k)) :
    ∃ U₀ : Submodule ℝ (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointFixedBaseRegularCoordinateSourceData
            (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge ∧
          ∀ᶠ x in
            nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge),
            (1 / 2 : ℝ) *
              (aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseRegularBlockCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x) +
                aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                    (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) := by
  rcases exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
      (K := ℝ) W B Cedge H r rEdge hCedge hbase hprod hedge hH with
    ⟨U₀, hU₀, sourceData⟩
  exact
    ⟨U₀, hU₀, sourceData,
      PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
          (W := W) (B := B) sourceData⟩

end FixedBaseRealSmallness

end Aoyagi
end DLN
end DLNFibre
