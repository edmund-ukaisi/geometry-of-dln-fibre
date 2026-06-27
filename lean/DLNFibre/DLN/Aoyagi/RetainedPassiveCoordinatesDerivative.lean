import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Derivative footholds for retained-passive raw-order coordinates

This file contains the first analytic derivative layer for the
retained-passive raw-order tuple endomap.  It proves differentiability of the
endpoint-solved top-left and lower-left families and assembles these component
facts into differentiability of the full raw-order map on the tuple
determinant chart.

These are local coordinate differentiability facts.  They do not prove a
Jacobian determinant formula, measure pushforward, normal crossings, pole
order, or RLCT extraction.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator
open scoped Topology

namespace DLNFibre
namespace DLN
namespace Aoyagi
namespace ChartLocalSuffixState
namespace RetainedPassiveNonredundantCoordinateData

/-- Matrix inversion is differentiable at determinant-unit real square
matrices. -/
theorem differentiableAt_matrix_inv_of_isUnit_det
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ρ ρ ℝ) (hA : IsUnit A.det) :
    DifferentiableAt ℝ (fun B : Matrix ρ ρ ℝ ↦ B⁻¹) A :=
  (hasFDerivAt_matrix_inv_of_isUnit_det A hA).differentiableAt

/-- Matrix inversion is `C^n` at determinant-unit real square matrices. -/
theorem contDiffAt_matrix_inv_of_isUnit_det
    {N : WithTop ℕ∞} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ρ ρ ℝ) (hA : IsUnit A.det) :
    ContDiffAt ℝ N (fun B : Matrix ρ ρ ℝ ↦ B⁻¹) A := by
  have hUnit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  rcases hUnit with ⟨u, rfl⟩
  rw [show (fun B : Matrix ρ ρ ℝ ↦ B⁻¹) = Ring.inverse from by
    funext B
    exact Matrix.nonsing_inv_eq_ringInverse (A := B)]
  exact contDiffAt_ringInverse ℝ u

/-- Heterogeneous finite matrix multiplication is differentiable in two
differentiable matrix-valued arguments. -/
theorem differentiableAt_matrix_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l m n : Type*} [Finite l] [Fintype m] [Finite n]
    {A : E → Matrix l m ℝ} {B : E → Matrix m n ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y : E ↦ A y * B y) x := by
  let _ : Fintype l := Fintype.ofFinite l
  let _ : Fintype n := Fintype.ofFinite n
  have hbilin :
      DifferentiableAt ℝ
        (fun q : Matrix l m ℝ × Matrix m n ℝ ↦ q.1 * q.2)
        (A x, B x) := by
    simpa [matrixMulContinuousLinearMap_apply] using
      (matrixMulContinuousLinearMap (l := l) (m := m) (n := n)).isBoundedBilinearMap
        |>.differentiableAt (A x, B x)
  simpa using hbilin.comp x (hA.prodMk hB)

set_option linter.unusedFintypeInType false in
/-- Heterogeneous finite matrix multiplication is `C^n` in two `C^n`
matrix-valued arguments. -/
theorem contDiffAt_matrix_mul
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    {A : E → Matrix l m ℝ} {B : E → Matrix m n ℝ} {x : E}
    (hA : ContDiffAt ℝ N A x) (hB : ContDiffAt ℝ N B x) :
    ContDiffAt ℝ N (fun y : E ↦ A y * B y) x := by
  simpa [matrixMulContinuousLinearMap_apply] using
    (matrixMulContinuousLinearMap (l := l) (m := m) (n := n)).isBoundedBilinearMap
      |>.contDiff.comp₂_contDiffAt hA hB

set_option linter.unusedFintypeInType false in
/-- Taking a finite submatrix is differentiable in a differentiable
matrix-valued family. -/
theorem differentiableAt_matrix_submatrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n l o : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    {A : E → Matrix m n ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (r : l → m) (c : o → n) :
    DifferentiableAt ℝ (fun y : E ↦ (A y).submatrix r c) x := by
  change DifferentiableAt ℝ
    (fun y : E ↦ fun i : l ↦ fun j : o ↦ A y (r i) (c j)) x
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  exact differentiableAt_pi.1 (differentiableAt_pi.1 hA (r i)) (c j)

set_option linter.unusedFintypeInType false in
/-- Taking a finite submatrix is `C^n` in a `C^n` matrix-valued family. -/
theorem contDiffAt_matrix_submatrix
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n l o : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    {A : E → Matrix m n ℝ} {x : E}
    (hA : ContDiffAt ℝ N A x) (r : l → m) (c : o → n) :
    ContDiffAt ℝ N (fun y : E ↦ (A y).submatrix r c) x := by
  let L : Matrix m n ℝ →ₗ[ℝ] Matrix l o ℝ :=
    { toFun := fun A ↦ A.submatrix r c
      map_add' := by
        intro A B
        ext i j
        simp
      map_smul' := by
        intro a A
        ext i j
        simp }
  let Lc : Matrix m n ℝ →L[ℝ] Matrix l o ℝ :=
    LinearMap.toContinuousLinearMap L
  change ContDiffAt ℝ N (fun y : E ↦ Lc (A y)) x
  exact Lc.contDiff.contDiffAt.comp x hA

set_option linter.unusedFintypeInType false in
/-- Reassembling four differentiable block families is differentiable. -/
theorem differentiableAt_matrix_fromBlocks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n l o : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    {A : E → Matrix m l ℝ} {B : E → Matrix m o ℝ}
    {C : E → Matrix n l ℝ} {D : E → Matrix n o ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hC : DifferentiableAt ℝ C x) (hD : DifferentiableAt ℝ D x) :
    DifferentiableAt ℝ
      (fun y : E ↦ fromBlocks (A y) (B y) (C y) (D y)) x := by
  change DifferentiableAt ℝ
    (fun y : E ↦ fun i : m ⊕ n ↦ fun j : l ⊕ o ↦
      fromBlocks (A y) (B y) (C y) (D y) i j) x
  rw [differentiableAt_pi]
  intro i
  cases i with
  | inl i =>
      rw [differentiableAt_pi]
      intro j
      cases j with
      | inl j =>
          simpa [Matrix.fromBlocks] using
            differentiableAt_pi.1 (differentiableAt_pi.1 hA i) j
      | inr j =>
          simpa [Matrix.fromBlocks] using
            differentiableAt_pi.1 (differentiableAt_pi.1 hB i) j
  | inr i =>
      rw [differentiableAt_pi]
      intro j
      cases j with
      | inl j =>
          simpa [Matrix.fromBlocks] using
            differentiableAt_pi.1 (differentiableAt_pi.1 hC i) j
      | inr j =>
          simpa [Matrix.fromBlocks] using
            differentiableAt_pi.1 (differentiableAt_pi.1 hD i) j

set_option linter.unusedFintypeInType false in
/-- Reassembling four `C^n` block families is `C^n`. -/
theorem contDiffAt_matrix_fromBlocks
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n l o : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype o]
    {A : E → Matrix m l ℝ} {B : E → Matrix m o ℝ}
    {C : E → Matrix n l ℝ} {D : E → Matrix n o ℝ} {x : E}
    (hA : ContDiffAt ℝ N A x) (hB : ContDiffAt ℝ N B x)
    (hC : ContDiffAt ℝ N C x) (hD : ContDiffAt ℝ N D x) :
    ContDiffAt ℝ N
      (fun y : E ↦ fromBlocks (A y) (B y) (C y) (D y)) x := by
  let P :=
    Matrix m l ℝ ×
      (Matrix m o ℝ × (Matrix n l ℝ × Matrix n o ℝ))
  let L : P →ₗ[ℝ] Matrix (m ⊕ n) (l ⊕ o) ℝ :=
    { toFun := fun q ↦ fromBlocks q.1 q.2.1 q.2.2.1 q.2.2.2
      map_add' := by
        intro q q'
        ext i j
        cases i <;> cases j <;> simp [P, Matrix.fromBlocks]
      map_smul' := by
        intro a q
        ext i j
        cases i <;> cases j <;> simp [P, Matrix.fromBlocks] }
  let Lc : P →L[ℝ] Matrix (m ⊕ n) (l ⊕ o) ℝ :=
    LinearMap.toContinuousLinearMap L
  have hprod :
      ContDiffAt ℝ N
        (fun y : E ↦ (A y, (B y, (C y, D y)))) x :=
    hA.prodMk (hB.prodMk (hC.prodMk hD))
  change ContDiffAt ℝ N
    (fun y : E ↦ Lc (A y, (B y, (C y, D y)))) x
  exact Lc.contDiff.contDiffAt.comp x hprod

set_option linter.unusedFintypeInType false in
/-- The top-left block projection is differentiable on differentiable matrix
families. -/
theorem differentiableAt_topLeftCorner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : DifferentiableAt ℝ M x) :
    DifferentiableAt ℝ (fun y : E ↦ topLeftCorner (M y)) x := by
  simpa [topLeftCorner] using
    differentiableAt_matrix_submatrix hM Sum.inl Sum.inl

set_option linter.unusedFintypeInType false in
/-- The top-left block projection is `C^n` on `C^n` matrix families. -/
theorem contDiffAt_topLeftCorner
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : ContDiffAt ℝ N M x) :
    ContDiffAt ℝ N (fun y : E ↦ topLeftCorner (M y)) x := by
  simpa [topLeftCorner] using
    contDiffAt_matrix_submatrix hM Sum.inl Sum.inl

set_option linter.unusedFintypeInType false in
/-- The upper-right block projection is differentiable on differentiable matrix
families. -/
theorem differentiableAt_upperRightBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : DifferentiableAt ℝ M x) :
    DifferentiableAt ℝ (fun y : E ↦ upperRightBlock (M y)) x := by
  simpa [upperRightBlock] using
    differentiableAt_matrix_submatrix hM Sum.inl Sum.inr

set_option linter.unusedFintypeInType false in
/-- The upper-right block projection is `C^n` on `C^n` matrix families. -/
theorem contDiffAt_upperRightBlock
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : ContDiffAt ℝ N M x) :
    ContDiffAt ℝ N (fun y : E ↦ upperRightBlock (M y)) x := by
  simpa [upperRightBlock] using
    contDiffAt_matrix_submatrix hM Sum.inl Sum.inr

set_option linter.unusedFintypeInType false in
/-- The lower-left block projection is differentiable on differentiable matrix
families. -/
theorem differentiableAt_lowerLeftBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : DifferentiableAt ℝ M x) :
    DifferentiableAt ℝ (fun y : E ↦ lowerLeftBlock (M y)) x := by
  simpa [lowerLeftBlock] using
    differentiableAt_matrix_submatrix hM Sum.inr Sum.inl

set_option linter.unusedFintypeInType false in
/-- The lower-left block projection is `C^n` on `C^n` matrix families. -/
theorem contDiffAt_lowerLeftBlock
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : ContDiffAt ℝ N M x) :
    ContDiffAt ℝ N (fun y : E ↦ lowerLeftBlock (M y)) x := by
  simpa [lowerLeftBlock] using
    contDiffAt_matrix_submatrix hM Sum.inr Sum.inl

set_option linter.unusedFintypeInType false in
/-- The lower-right block projection is differentiable on differentiable matrix
families. -/
theorem differentiableAt_lowerRightBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : DifferentiableAt ℝ M x) :
    DifferentiableAt ℝ (fun y : E ↦ lowerRightBlock (M y)) x := by
  simpa [lowerRightBlock] using
    differentiableAt_matrix_submatrix hM Sum.inr Sum.inr

set_option linter.unusedFintypeInType false in
/-- The lower-right block projection is `C^n` on `C^n` matrix families. -/
theorem contDiffAt_lowerRightBlock
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : ContDiffAt ℝ N M x) :
    ContDiffAt ℝ N (fun y : E ↦ lowerRightBlock (M y)) x := by
  simpa [lowerRightBlock] using
    contDiffAt_matrix_submatrix hM Sum.inr Sum.inr

set_option linter.unusedFintypeInType false in
/-- The Schur residual block is differentiable at determinant-chart points of
a differentiable block-matrix family. -/
theorem differentiableAt_schurResidualBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : DifferentiableAt ℝ M x)
    (hchart : identityCornerDetChart (M x)) :
    DifferentiableAt ℝ (fun y : E ↦ schurResidualBlock (M y)) x := by
  have htop : DifferentiableAt ℝ (fun y : E ↦ topLeftCorner (M y)) x :=
    differentiableAt_topLeftCorner hM
  have htopInv :
      DifferentiableAt ℝ (fun y : E ↦ (topLeftCorner (M y))⁻¹) x :=
    (differentiableAt_matrix_inv_of_isUnit_det (topLeftCorner (M x)) hchart).comp x htop
  have hupper : DifferentiableAt ℝ (fun y : E ↦ upperRightBlock (M y)) x :=
    differentiableAt_upperRightBlock hM
  have hlower : DifferentiableAt ℝ (fun y : E ↦ lowerLeftBlock (M y)) x :=
    differentiableAt_lowerLeftBlock hM
  have hright : DifferentiableAt ℝ (fun y : E ↦ lowerRightBlock (M y)) x :=
    differentiableAt_lowerRightBlock hM
  have hleftInv :
      DifferentiableAt ℝ
        (fun y : E ↦ lowerLeftBlock (M y) * (topLeftCorner (M y))⁻¹) x :=
    differentiableAt_matrix_mul hlower htopInv
  have hcorr :
      DifferentiableAt ℝ
        (fun y : E ↦
          lowerLeftBlock (M y) * (topLeftCorner (M y))⁻¹ * upperRightBlock (M y)) x :=
    differentiableAt_matrix_mul hleftInv hupper
  simpa [schurResidualBlock] using hright.sub hcorr

set_option linter.unusedFintypeInType false in
/-- The Schur residual block is `C^n` at determinant-chart points of a `C^n`
block-matrix family. -/
theorem contDiffAt_schurResidualBlock
    {N : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ] [Fintype ν]
    {M : E → Matrix (ρ ⊕ μ) (ρ ⊕ ν) ℝ} {x : E}
    (hM : ContDiffAt ℝ N M x)
    (hchart : identityCornerDetChart (M x)) :
    ContDiffAt ℝ N (fun y : E ↦ schurResidualBlock (M y)) x := by
  have htop : ContDiffAt ℝ N (fun y : E ↦ topLeftCorner (M y)) x :=
    contDiffAt_topLeftCorner hM
  have htopInv :
      ContDiffAt ℝ N (fun y : E ↦ (topLeftCorner (M y))⁻¹) x :=
    (contDiffAt_matrix_inv_of_isUnit_det (topLeftCorner (M x)) hchart).comp x htop
  have hupper : ContDiffAt ℝ N (fun y : E ↦ upperRightBlock (M y)) x :=
    contDiffAt_upperRightBlock hM
  have hlower : ContDiffAt ℝ N (fun y : E ↦ lowerLeftBlock (M y)) x :=
    contDiffAt_lowerLeftBlock hM
  have hright : ContDiffAt ℝ N (fun y : E ↦ lowerRightBlock (M y)) x :=
    contDiffAt_lowerRightBlock hM
  have hleftInv :
      ContDiffAt ℝ N
        (fun y : E ↦ lowerLeftBlock (M y) * (topLeftCorner (M y))⁻¹) x :=
    contDiffAt_matrix_mul hlower htopInv
  have hcorr :
      ContDiffAt ℝ N
        (fun y : E ↦
          lowerLeftBlock (M y) * (topLeftCorner (M y))⁻¹ * upperRightBlock (M y)) x :=
    contDiffAt_matrix_mul hleftInv hupper
  simpa [schurResidualBlock] using hright.sub hcorr

/-- One deterministic suffix-state update is differentiable in the source
edge and previous suffix fields at determinant-chart points. -/
theorem differentiableAt_chartLocalSuffixState_step_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {x₀ : E}
    (F : E → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : E → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (hF : DifferentiableAt ℝ (fun x : E ↦ F x p) x₀)
    (hL : DifferentiableAt ℝ (fun x : E ↦ (S x).L) x₀)
    (hB : DifferentiableAt ℝ (fun x : E ↦ (S x).B) x₀)
    (hCtop : DifferentiableAt ℝ (fun x : E ↦ (S x).Ctop) x₀)
    (hD : DifferentiableAt ℝ (fun x : E ↦ (S x).D) x₀)
    (hCtopUnit : IsUnit ((S x₀).Ctop.det))
    (hchart :
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (F x₀) p (S x₀))) :
    IsUnit ((ChartLocalSuffixState.step (F x₀) p (S x₀)).Ctop.det) ∧
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).L) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).B) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).Ctop) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).D) x₀ := by
  let M : E → Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    fun x ↦ ChartLocalSuffixState.transformedEdge (F x) p (S x)
  have hleft :
      DifferentiableAt ℝ
        (fun x : E ↦
          fromBlocks (1 : Matrix ρ ρ ℝ) (S x).B 0
            (1 : Matrix (κ p.succ) (κ p.succ) ℝ)) x₀ := by
    exact differentiableAt_matrix_fromBlocks (by fun_prop) hB (by fun_prop) (by fun_prop)
  have hM : DifferentiableAt ℝ M x₀ := by
    have hmul := differentiableAt_matrix_mul hleft hF
    simpa [M, ChartLocalSuffixState.transformedEdge] using hmul
  have htop : DifferentiableAt ℝ (fun x : E ↦ topLeftCorner (M x)) x₀ :=
    differentiableAt_topLeftCorner hM
  have htopUnit : IsUnit ((topLeftCorner (M x₀)).det) := by
    have hchartUnit :
        IsUnit
          ((topLeftCorner
            (ChartLocalSuffixState.transformedEdge (F x₀) p (S x₀))).det) := by
      simpa only [identityCornerDetChart] using hchart
    simpa only [M] using hchartUnit
  have htopInv :
      DifferentiableAt ℝ (fun x : E ↦ (topLeftCorner (M x))⁻¹) x₀ :=
    (differentiableAt_matrix_inv_of_isUnit_det (topLeftCorner (M x₀)) htopUnit).comp
      x₀ htop
  have hupper : DifferentiableAt ℝ (fun x : E ↦ upperRightBlock (M x)) x₀ :=
    differentiableAt_upperRightBlock hM
  have hlower : DifferentiableAt ℝ (fun x : E ↦ lowerLeftBlock (M x)) x₀ :=
    differentiableAt_lowerLeftBlock hM
  have hCtopTop :
      DifferentiableAt ℝ
        (fun x : E ↦ (S x).Ctop * topLeftCorner (M x)) x₀ :=
    differentiableAt_matrix_mul hCtop htop
  have hCtopTopUnit : IsUnit (((S x₀).Ctop * topLeftCorner (M x₀)).det) := by
    rw [Matrix.det_mul]
    exact hCtopUnit.mul htopUnit
  have hCtopTopInv :
      DifferentiableAt ℝ
        (fun x : E ↦ ((S x).Ctop * topLeftCorner (M x))⁻¹) x₀ :=
    (differentiableAt_matrix_inv_of_isUnit_det
      ((S x₀).Ctop * topLeftCorner (M x₀)) hCtopTopUnit).comp x₀ hCtopTop
  have hBstep :
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).B) x₀ := by
    change DifferentiableAt ℝ
      (fun x : E ↦ (topLeftCorner (M x))⁻¹ * upperRightBlock (M x)) x₀
    exact differentiableAt_matrix_mul htopInv hupper
  have hCtopStep :
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).Ctop) x₀ := by
    change DifferentiableAt ℝ
      (fun x : E ↦ (S x).Ctop * topLeftCorner (M x)) x₀
    exact hCtopTop
  have hschur : DifferentiableAt ℝ (fun x : E ↦ schurResidualBlock (M x)) x₀ :=
    differentiableAt_schurResidualBlock hM htopUnit
  have hDstep :
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).D) x₀ := by
    change DifferentiableAt ℝ
      (fun x : E ↦ (S x).D * schurResidualBlock (M x)) x₀
    exact differentiableAt_matrix_mul hD hschur
  have hDlower :
      DifferentiableAt ℝ
        (fun x : E ↦ (S x).D * lowerLeftBlock (M x)) x₀ :=
    differentiableAt_matrix_mul hD hlower
  have hX :
      DifferentiableAt ℝ
        (fun x : E ↦
          (S x).D * lowerLeftBlock (M x) *
            ((S x).Ctop * topLeftCorner (M x))⁻¹) x₀ :=
    differentiableAt_matrix_mul hDlower hCtopTopInv
  have hfactor :
      DifferentiableAt ℝ
        (fun x : E ↦
          fromBlocks (1 : Matrix ρ ρ ℝ) 0
            (-((S x).D * lowerLeftBlock (M x) *
              ((S x).Ctop * topLeftCorner (M x))⁻¹))
            (1 : Matrix (κ j) (κ j) ℝ)) x₀ := by
    exact differentiableAt_matrix_fromBlocks (by fun_prop) (by fun_prop) hX.neg (by fun_prop)
  have hLstep :
      DifferentiableAt ℝ
        (fun x : E ↦ (ChartLocalSuffixState.step (F x) p (S x)).L) x₀ := by
    change DifferentiableAt ℝ
      (fun x : E ↦
        fromBlocks (1 : Matrix ρ ρ ℝ) 0
          (-((S x).D * lowerLeftBlock (M x) *
            ((S x).Ctop * topLeftCorner (M x))⁻¹))
          (1 : Matrix (κ j) (κ j) ℝ) * (S x).L) x₀
    exact differentiableAt_matrix_mul hfactor hL
  have hCtopUnitStep :
      IsUnit ((ChartLocalSuffixState.step (F x₀) p (S x₀)).Ctop.det) := by
    change IsUnit (((S x₀).Ctop * topLeftCorner (M x₀)).det)
    exact hCtopTopUnit
  exact ⟨hCtopUnitStep, hLstep, hBstep, hCtopStep, hDstep⟩

/-- All deterministic suffix-state fields are differentiable along a
differentiable edge-family curve satisfying the recursive determinant chart at
the basepoint. -/
theorem differentiableAt_chartLocalSuffixState_suffixState_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {x₀ : E}
    (F : E → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    (hF : DifferentiableAt ℝ F x₀)
    {j : Fin (N + 1)}
    (hchart : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (F x₀) p
          (ChartLocalSuffixState.suffixState (F x₀) j p.succ hpj))) :
    ∀ (i : Fin (N + 1)) (hij : i ≤ j),
      IsUnit ((ChartLocalSuffixState.suffixState (F x₀) j i hij).Ctop.det) ∧
        DifferentiableAt ℝ
          (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j i hij).L) x₀ ∧
        DifferentiableAt ℝ
          (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j i hij).B) x₀ ∧
        DifferentiableAt ℝ
          (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j i hij).Ctop) x₀ ∧
        DifferentiableAt ℝ
          (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j i hij).D) x₀ := by
  intro i hij
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    IsUnit ((ChartLocalSuffixState.suffixState (F x₀) j im
          (Fin.val_fin_le.mpr hmj)).Ctop.det) ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j im
            (Fin.val_fin_le.mpr hmj)).L) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j im
            (Fin.val_fin_le.mpr hmj)).B) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j im
            (Fin.val_fin_le.mpr hmj)).Ctop) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j im
            (Fin.val_fin_le.mpr hmj)).D) x₀
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal]
    · simp [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal]
    · simp [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal]
    · simp [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal]
    · simp [ChartLocalSuffixState.suffixState_self, ChartLocalSuffixState.terminal]
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (hms.trans_lt j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        IsUnit ((ChartLocalSuffixState.suffixState (F x₀) j p.succ hpj).Ctop.det) ∧
          DifferentiableAt ℝ
            (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j p.succ hpj).L) x₀ ∧
          DifferentiableAt ℝ
            (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j p.succ hpj).B) x₀ ∧
          DifferentiableAt ℝ
            (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j p.succ hpj).Ctop) x₀ ∧
          DifferentiableAt ℝ
            (fun x : E ↦ (ChartLocalSuffixState.suffixState (F x) j p.succ hpj).D) x₀ := by
      simpa [motive, p, hpj] using ih
    rcases ih' with ⟨hCtopUnit, hL, hB, hCtop, hD⟩
    have hF_p : DifferentiableAt ℝ (fun x : E ↦ F x p) x₀ :=
      differentiableAt_pi.1 hF p
    have hnext :=
      differentiableAt_chartLocalSuffixState_step_fields F p
        (fun x : E ↦ ChartLocalSuffixState.suffixState (F x) j p.succ hpj)
        hF_p hL hB hCtop hD hCtopUnit (hchart p hpj)
    rcases hnext with ⟨hCtopUnitNext, hLnext, hBnext, hCtopNext, hDnext⟩
    have hstate0 :
        ChartLocalSuffixState.suffixState (F x₀) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj) =
          ChartLocalSuffixState.step (F x₀) p
            (ChartLocalSuffixState.suffixState (F x₀) j p.succ hpj) :=
      ChartLocalSuffixState.suffixState_castSucc (F x₀) p hpj
    have hstateL :
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)).L) =
        (fun x : E ↦
          (ChartLocalSuffixState.step (F x) p
            (ChartLocalSuffixState.suffixState (F x) j p.succ hpj)).L) := by
      funext x
      rw [ChartLocalSuffixState.suffixState_castSucc]
    have hstateB :
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)).B) =
        (fun x : E ↦
          (ChartLocalSuffixState.step (F x) p
            (ChartLocalSuffixState.suffixState (F x) j p.succ hpj)).B) := by
      funext x
      rw [ChartLocalSuffixState.suffixState_castSucc]
    have hstateCtop :
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)).Ctop) =
        (fun x : E ↦
          (ChartLocalSuffixState.step (F x) p
            (ChartLocalSuffixState.suffixState (F x) j p.succ hpj)).Ctop) := by
      funext x
      rw [ChartLocalSuffixState.suffixState_castSucc]
    have hstateD :
        (fun x : E ↦
          (ChartLocalSuffixState.suffixState (F x) j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)).D) =
        (fun x : E ↦
          (ChartLocalSuffixState.step (F x) p
            (ChartLocalSuffixState.suffixState (F x) j p.succ hpj)).D) := by
      funext x
      rw [ChartLocalSuffixState.suffixState_castSucc]
    rw [← hstate0] at hCtopUnitNext
    rw [← hstateL] at hLnext
    rw [← hstateB] at hBnext
    rw [← hstateCtop] at hCtopNext
    rw [← hstateD] at hDnext
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [motive, p, hpj] using hCtopUnitNext
    · simpa [motive, p, hpj] using hLnext
    · simpa [motive, p, hpj] using hBnext
    · simpa [motive, p, hpj] using hCtopNext
    · simpa [motive, p, hpj] using hDnext
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase
    (Fin.val_fin_le.mp hij)
  simpa [motive] using hcanon

/-- The source-readback suffix-state fields are differentiable along a
differentiable source edge-family curve satisfying the recursive determinant
chart at the basepoint. -/
theorem differentiableAt_sourceReadbackSuffixState_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {x₀ : E}
    (F : E → EdgeFamilyTuple ρ κ' ℝ)
    (hF : DifferentiableAt ℝ F x₀)
    (hchart : sourceRecursiveDetChart (K := ℝ) (ρ := ρ) (F x₀))
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1)) :
    IsUnit ((sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x₀) i hi).Ctop.det) ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x) i hi).L) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x) i hi).B) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x) i hi).Ctop) x₀ ∧
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x) i hi).D) x₀ := by
  have hchart' :
      ∀ (p : Fin (M + 1)) (hp : p.succ ≤ Fin.last (M + 1)),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge (F x₀) p
            (ChartLocalSuffixState.suffixState (F x₀) (Fin.last (M + 1)) p.succ hp)) := by
    simpa [sourceRecursiveDetChart] using hchart
  simpa [sourceReadbackSuffixState] using
    (differentiableAt_chartLocalSuffixState_suffixState_fields
      (F := F) hF (j := Fin.last (M + 1)) hchart' i hi)

/-- The transformed edge used by source readback is differentiable along a
differentiable source edge-family curve satisfying the recursive determinant
chart at the basepoint. -/
theorem differentiableAt_sourceReadbackTransformedEdge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {x₀ : E}
    (F : E → EdgeFamilyTuple ρ κ' ℝ)
    (hF : DifferentiableAt ℝ F x₀)
    (hchart : sourceRecursiveDetChart (K := ℝ) (ρ := ρ) (F x₀))
    (p : Fin (M + 1)) :
    DifferentiableAt ℝ
      (fun x : E ↦ sourceReadbackTransformedEdge (K := ℝ) (ρ := ρ) (F x) p) x₀ := by
  let S : E → ChartLocalSuffixState ρ κ' ℝ (Fin.last (M + 1)) p.succ :=
    fun x ↦ sourceReadbackSuffixState (K := ℝ) (ρ := ρ) (F x)
      p.succ p.succ.le_last
  have hfields :=
    differentiableAt_sourceReadbackSuffixState_fields
      (ρ := ρ) (κ' := κ') F hF hchart p.succ p.succ.le_last
  rcases hfields with ⟨_, _hL, hB, _hCtop, _hD⟩
  have hF_p : DifferentiableAt ℝ (fun x : E ↦ F x p) x₀ :=
    differentiableAt_pi.1 hF p
  have hleft :
      DifferentiableAt ℝ
        (fun x : E ↦
          fromBlocks (1 : Matrix ρ ρ ℝ) (S x).B 0
            (1 : Matrix (κ' p.succ) (κ' p.succ) ℝ)) x₀ :=
    differentiableAt_matrix_fromBlocks (by fun_prop) hB (by fun_prop) (by fun_prop)
  have hmul := differentiableAt_matrix_mul hleft hF_p
  simpa [sourceReadbackTransformedEdge, sourceReadbackSuffixState, S,
    ChartLocalSuffixState.transformedEdge] using hmul

@[fun_prop]
theorem differentiableAt_A1passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin M)
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1passive p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.1 p) z
  fun_prop

@[fun_prop]
theorem differentiableAt_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F2 p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.1 p) z
  fun_prop

@[fun_prop]
theorem differentiableAt_A3passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin M)
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3passive p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.1 p) z
  fun_prop

@[fun_prop]
theorem differentiableAt_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.1 p) z
  fun_prop

@[fun_prop]
theorem differentiableAt_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).Ctop) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.2.1) z
  fun_prop

@[fun_prop]
theorem differentiableAt_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  change DifferentiableAt ℝ (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.2.2) z
  fun_prop

@[fun_prop]
theorem differentiableAt_A1seed
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  cases p using Fin.cases with
  | zero =>
      change DifferentiableAt ℝ
        (fun _z : TopologyTuple ρ κ' ℝ ↦ (0 : Matrix ρ ρ ℝ)) z
      fun_prop
  | succ p =>
      simpa [A1seed] using
        differentiableAt_A1passive (ρ := ρ) (κ' := κ') p z

@[fun_prop]
theorem differentiableAt_F2full
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (i : Fin (M + 2))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F2full i) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  induction i using Fin.lastCases with
  | last =>
      simp [F2full]
  | cast i =>
      simpa [F2full] using
        differentiableAt_F2 (ρ := ρ) (κ' := κ') i z

@[fun_prop]
theorem differentiableAt_A3seed
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  induction p using Fin.lastCases with
  | last =>
      simp [A3seed]
  | cast p =>
      simpa [A3seed] using
        differentiableAt_A3passive (ρ := ρ) (κ' := κ') p z

@[fun_prop]
theorem contDiffAt_A1passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin M)
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1passive p) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.1 p) z
  have hproj : ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.1) z :=
    (contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).fst
  exact contDiffAt_pi.1 hproj p

@[fun_prop]
theorem contDiffAt_F2
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F2 p) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.1 p) z
  have hproj : ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.1) z :=
    (contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).snd.fst
  exact contDiffAt_pi.1 hproj p

@[fun_prop]
theorem contDiffAt_A3passive
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin M)
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3passive p) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.1 p) z
  have hproj : ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.1) z :=
    (contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).snd.snd.fst
  exact contDiffAt_pi.1 hproj p

@[fun_prop]
theorem contDiffAt_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.1 p) z
  have hproj : ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.1) z :=
    (contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).snd.snd.snd.fst
  exact contDiffAt_pi.1 hproj p

@[fun_prop]
theorem contDiffAt_Ctop
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).Ctop) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.2.1) z
  exact
    ((contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).snd.snd.snd.snd.fst)

@[fun_prop]
theorem contDiffAt_F3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3) z := by
  change ContDiffAt ℝ 1 (fun z : TopologyTuple ρ κ' ℝ ↦ z.2.2.2.2.2) z
  exact
    ((contDiffAt_id :
      ContDiffAt ℝ 1 (id : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ) z).snd.snd.snd.snd.snd)

@[fun_prop]
theorem contDiffAt_A1seed
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z := by
  cases p using Fin.cases with
  | zero =>
      change ContDiffAt ℝ 1
        (fun _z : TopologyTuple ρ κ' ℝ ↦ (0 : Matrix ρ ρ ℝ)) z
      fun_prop
  | succ p =>
      simpa [A1seed] using
        contDiffAt_A1passive (ρ := ρ) (κ' := κ') p z

@[fun_prop]
theorem contDiffAt_F2full
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (i : Fin (M + 2))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F2full i) z := by
  induction i using Fin.lastCases with
  | last =>
      simpa [F2full] using
        (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
          (c := (0 : Matrix ρ (κ' (Fin.last (M + 1))) ℝ)))
  | cast i =>
      simpa [F2full] using
        contDiffAt_F2 (ρ := ρ) (κ' := κ') i z

@[fun_prop]
theorem contDiffAt_A3seed
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z := by
  induction p using Fin.lastCases with
  | last =>
      simpa [A3seed] using
        (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
          (c := (0 : Matrix (κ' (Fin.last (M + 1))) ρ ℝ)))
  | cast p =>
      simpa [A3seed] using
        contDiffAt_A3passive (ρ := ρ) (κ' := κ') p z

/-- The passive top-left tail product is differentiable as a function of the
ambient tuple coordinates. -/
theorem differentiableAt_retainedPassiveA1TailAfterFirst
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed) z := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    1 ≤ m →
      DifferentiableAt ℝ
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
            j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    intro _hmpos
    change DifferentiableAt ℝ
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          _ j j le_rfl) z
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih (Nat.succ_pos m)
    have hfactor :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      differentiableAt_A1seed (ρ := ρ) (κ' := κ') p z
    have hmul :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      hnext.mul hfactor
    change DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p hpj]
    simpa [p] using hmul
  have htail :=
    Nat.decreasingInduction (motive := motive) hstep hbase
      (Nat.succ_le_succ (Nat.zero_le M))
  have htail' := htail le_rfl
  simpa [retainedPassiveA1TailAfterFirst, j, motive] using htail'

/-- Every suffix of the passive top-left seed product is differentiable as a
function of the retained-passive tuple coordinates. -/
theorem differentiableAt_retainedPassiveA1seed_residualFactorProduct
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
          (Fin.last (M + 1)) i hi) z := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    change DifferentiableAt ℝ
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          _ j j le_rfl) z
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih
    have hfactor :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      differentiableAt_A1seed (ρ := ρ) (κ' := κ') p z
    have hmul :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      hnext.mul hfactor
    change DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- The endpoint passive top-left seed product is empty, so its Frechet
derivative is zero. -/
theorem fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (z v : TopologyTuple ρ κ' ℝ) :
    let j : Fin (M + 2) := Fin.last (M + 1)
    (fderiv ℝ
      (fun y : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          j j le_rfl) z) v = 0 := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  simp

set_option maxRecDepth 2048 in
/-- The Frechet derivative of one passive top-left seed-product suffix obeys
the noncommutative product rule, with the new passive seed derivative rewritten
as the corresponding source tangent. -/
theorem fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (z v : TopologyTuple ρ κ' ℝ) (q : Fin M) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let p : Fin (M + 1) := q.succ
    let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
    let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    (fderiv ℝ Pcast z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let p : Fin (M + 1) := q.succ
  let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let Afun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed p
  let B : Matrix ρ ρ ℝ →L[ℝ] Matrix ρ ρ ℝ →L[ℝ] Matrix ρ ρ ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := ρ) (n := ρ)
  have hPsuccdiff : DifferentiableAt ℝ Psucc z := by
    simpa [Psucc] using
      differentiableAt_retainedPassiveA1seed_residualFactorProduct
        (ρ := ρ) (κ' := κ') p.succ p.succ.le_last z
  have hAdiff : DifferentiableAt ℝ Afun z := by
    simpa [Afun] using
      differentiableAt_A1seed (ρ := ρ) (κ' := κ') p z
  have hPcast_eq : Pcast = fun y ↦ Psucc y * Afun y := by
    funext y
    simpa [Pcast, Psucc, Afun, p, A1seed, ofTopologyTuple] using
      residualFactorProduct_castSucc
        (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (j := Fin.last (M + 1)) p p.succ.le_last
  have hmulDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Psucc y * Afun y) z =
        B.precompR _ (Psucc z) (fderiv ℝ Afun z) +
          B.precompL _ (fderiv ℝ Psucc z) (Afun z) := by
    simpa [B] using
      (B.hasFDerivAt_of_bilinear hPsuccdiff.hasFDerivAt hAdiff.hasFDerivAt).fderiv
  have hA_apply : (fderiv ℝ Afun z) v = v.1 q := by
    let LA : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.1 q
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hAfun : Afun = fun y : TopologyTuple ρ κ' ℝ ↦ y.1 q := by
      funext y
      simp [Afun, p, A1seed, ofTopologyTuple]
    have hLA :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.1 q) z = LA :=
      LA.fderiv
    rw [hAfun, hLA]
    rfl
  calc
    (fderiv ℝ Pcast z) v =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Psucc y * Afun y) z) v := by
          rw [hPcast_eq]
    _ = Psucc z * (fderiv ℝ Afun z) v + (fderiv ℝ Psucc z) v * Afun z := by
          rw [hmulDeriv]
          simp [B, matrixMulContinuousLinearMap_apply]
    _ = (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
          rw [hA_apply]
          simp [Afun, data]
          abel

/-- In the single-edge case, the retained-passive top-left tail after the first
edge is the empty product, so its Frechet derivative is zero. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_zero_apply
    {ρ : Type*} {κ' : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (z v : TopologyTuple ρ κ' ℝ) :
    (fderiv ℝ
      (fun y : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v = 0 := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  simp [retainedPassiveA1TailAfterFirst]

/-- For a nonempty retained-passive top-left tail, the derivative of the actual
tail map is the first step of the passive suffix-product recurrence. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_succ_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin ((M + 1) + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (z v : TopologyTuple ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let q : Fin (M + 1) := 0
    let p : Fin ((M + 1) + 1) := q.succ
    let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last ((M + 1) + 1)) p.succ p.succ.le_last
    (fderiv ℝ
      (fun y : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (M := M + 1) (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let q : Fin (M + 1) := 0
  let p : Fin ((M + 1) + 1) := q.succ
  let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last ((M + 1) + 1)) p.castSucc p.castSucc.le_last
  let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin ((M + 1) + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last ((M + 1) + 1)) p.succ p.succ.le_last
  have htail_eq :
      (fun y : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (M := M + 1) (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) = Pcast := by
    funext y
    simp [Pcast, retainedPassiveA1TailAfterFirst, p, q]
  have hrec :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
      (M := M + 1) (ρ := ρ) (κ' := κ') z v q
  calc
    (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦
          retainedPassiveA1TailAfterFirst (M := M + 1) (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v =
        (fderiv ℝ Pcast z) v := by
          rw [htail_eq]
    _ = (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
          simpa [Pcast, Psucc, p, q, data] using hrec

/-- Positive-length wrapper for the retained-passive top-left tail derivative:
the actual tail derivative is the first step of the passive suffix-product
recurrence. -/
theorem fderiv_retainedPassive_A1TailAfterFirst_pos_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (hM : 0 < M)
    (z v : TopologyTuple ρ κ' ℝ) :
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let q : Fin M := ⟨0, hM⟩
    let p : Fin (M + 1) := q.succ
    let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
          (Fin.last (M + 1)) p.succ p.succ.le_last
    (fderiv ℝ
      (fun y : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v =
      (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let q : Fin M := ⟨0, hM⟩
  let p : Fin (M + 1) := q.succ
  let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Psucc : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
        (Fin.last (M + 1)) p.succ p.succ.le_last
  have htail_eq :
      (fun y : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) = Pcast := by
    funext y
    simp [Pcast, retainedPassiveA1TailAfterFirst, p, q]
  have hrec :=
    fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply
      (M := M) (ρ := ρ) (κ' := κ') z v q
  calc
    (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦
          retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed) z) v =
        (fderiv ℝ Pcast z) v := by
          rw [htail_eq]
    _ = (fderiv ℝ Psucc z) v * data.A1seed p + Psucc z * v.1 q := by
          simpa [Pcast, Psucc, p, q, data] using hrec

/-- On the tuple determinant chart, each solved full `A1` block is
differentiable as an ambient tuple-coordinate function. -/
theorem differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := by
    exact hz
  cases p using Fin.cases with
  | zero =>
      have htail :=
        differentiableAt_retainedPassiveA1TailAfterFirst
          (ρ := ρ) (κ' := κ') z
      have htailUnit :
          IsUnit
            (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              data.A1seed).det := by
        exact
          retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
            (K := ℝ) (ρ := ρ) data.A1seed
            (data.toCoordinateData_passiveA1_units hdet.2)
      have hinv :
          DifferentiableAt ℝ
            (fun z : TopologyTuple ρ κ' ℝ ↦
              (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹) z :=
        (differentiableAt_matrix_inv_of_isUnit_det
          (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ) data.A1seed)
          htailUnit).comp z htail
      have hCtop := differentiableAt_Ctop (ρ := ρ) (κ' := κ') z
      have hmul :
          DifferentiableAt ℝ
            (fun z : TopologyTuple ρ κ' ℝ ↦
              (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹ *
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).Ctop) z :=
        hinv.mul hCtop
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData] using hmul
  | succ p =>
      have hseed := differentiableAt_A1seed (ρ := ρ) (κ' := κ') p.succ z
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData, Fin.succ_ne_zero] using hseed

/-- The passive top-left tail product is `C^1` as a function of the ambient
tuple coordinates. -/
theorem contDiffAt_retainedPassiveA1TailAfterFirst
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed) z := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    1 ≤ m →
      ContDiffAt ℝ 1
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
            j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    intro _hmpos
    change ContDiffAt ℝ 1
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          _ j j le_rfl) z
    simpa using
      (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
        (c := (1 : Matrix ρ ρ ℝ)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih (Nat.succ_pos m)
    have hfactor :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      contDiffAt_A1seed (ρ := ρ) (κ' := κ') p z
    have hmul :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p) z :=
      contDiffAt_matrix_mul hnext hfactor
    change ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed p hpj]
    simpa [p] using hmul
  have htail :=
    Nat.decreasingInduction (motive := motive) hstep hbase
      (Nat.succ_le_succ (Nat.zero_le M))
  have htail' := htail le_rfl
  simpa [retainedPassiveA1TailAfterFirst, j, motive] using htail'

/-- On the tuple determinant chart, each solved full `A1` block is `C^1` as an
ambient tuple-coordinate function. -/
theorem contDiffAt_solvedA1_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := by
    exact hz
  cases p using Fin.cases with
  | zero =>
      have htail :=
        contDiffAt_retainedPassiveA1TailAfterFirst
          (ρ := ρ) (κ' := κ') z
      have htailUnit :
          IsUnit
            (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              data.A1seed).det := by
        exact
          retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
            (K := ℝ) (ρ := ρ) data.A1seed
            (data.toCoordinateData_passiveA1_units hdet.2)
      have hinv :
          ContDiffAt ℝ 1
            (fun z : TopologyTuple ρ κ' ℝ ↦
              (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹) z :=
        (contDiffAt_matrix_inv_of_isUnit_det
          (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ) data.A1seed)
          htailUnit).comp z htail
      have hCtop := contDiffAt_Ctop (ρ := ρ) (κ' := κ') z
      have hmul :
          ContDiffAt ℝ 1
            (fun z : TopologyTuple ρ κ' ℝ ↦
              (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹ *
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).Ctop) z :=
        contDiffAt_matrix_mul hinv hCtop
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData] using hmul
  | succ p =>
      have hseed := contDiffAt_A1seed (ρ := ρ) (κ' := κ') p.succ z
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData, Fin.succ_ne_zero] using hseed

/-- The zeroed-final lower-left family is differentiable componentwise as a
function of the ambient tuple coordinates. -/
theorem differentiableAt_retainedPassiveA3WithoutLast
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  by_cases hp : p = Fin.last M
  · subst p
    simp [retainedPassiveA3WithoutLast]
  · simpa [retainedPassiveA3WithoutLast, hp] using
      differentiableAt_A3seed (ρ := ρ) (κ' := κ') p z

/-- The zeroed-final lower-left family is `C^1` componentwise as a function of
the ambient tuple coordinates. -/
theorem contDiffAt_retainedPassiveA3WithoutLast
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)]
    (p : Fin (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z := by
  by_cases hp : p = Fin.last M
  · subst p
    simpa [retainedPassiveA3WithoutLast] using
      (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
        (c := (0 : Matrix (κ' (Fin.last (M + 1))) ρ ℝ)))
  · simpa [retainedPassiveA3WithoutLast, hp] using
      contDiffAt_A3seed (ρ := ρ) (κ' := κ') p z

/-- Residual products of the stored `C` blocks are differentiable as functions
of the ambient tuple coordinates. -/
theorem differentiableAt_residualFactorProduct_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          (Fin.last (M + 1)) i hi) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    change DifferentiableAt ℝ
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ') _ j j le_rfl) z
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih
    have hfactor :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z :=
      differentiableAt_C (ρ := ρ) (κ' := κ') p z
    have hmul :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z :=
      differentiableAt_matrix_mul hnext hfactor
    change DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := κ')
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- Residual products of the solved full `A1` family are differentiable at
tuple determinant-chart points. -/
theorem differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Finite (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1))
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) i hi) z := by
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    change DifferentiableAt ℝ
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          _ j j le_rfl) z
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih
    have hfactor :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z :=
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hmul :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                j p.succ hpj *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z :=
      differentiableAt_matrix_mul hnext hfactor
    change DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                j p.succ hpj *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- Residual products of the stored `C` blocks are `C^1` as functions of the
ambient tuple coordinates. -/
theorem contDiffAt_residualFactorProduct_C
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1))
    (z : TopologyTuple ρ κ' ℝ) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          (Fin.last (M + 1)) i hi) z := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    change ContDiffAt ℝ 1
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ') _ j j le_rfl) z
    simpa using
      (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
        (c := (1 :
          Matrix (κ' (Fin.last (M + 1))) (κ' (Fin.last (M + 1))) ℝ)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih
    have hfactor :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z :=
      contDiffAt_C (ρ := ρ) (κ' := κ') p z
    have hmul :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z :=
      contDiffAt_matrix_mul hnext hfactor
    change ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := κ')
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                j p.succ hpj *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := κ')
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- Residual products of the solved full `A1` family are `C^1` at tuple
determinant-chart points. -/
theorem contDiffAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1))
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) i hi) z := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)) z
  have hbase : motive (M + 1) le_rfl := by
    change ContDiffAt ℝ 1
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          _ j j le_rfl) z
    simpa using
      (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
        (c := (1 : Matrix ρ ρ ℝ)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              j p.succ hpj) z := by
      simpa [motive, j, p] using ih
    have hfactor :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z :=
      contDiffAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hmul :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                j p.succ hpj *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p) z :=
      contDiffAt_matrix_mul hnext hfactor
    change ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun z ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                j p.succ hpj *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p by
      funext z
      exact
        residualFactorProduct_castSucc
          (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- The explicit lower-left product-tail sum built from solved `A1`, zeroed
early `A3`, and stored `C` blocks is differentiable at tuple determinant-chart
points. -/
theorem differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M + 1)
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C m hm) z := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := by
    exact hz
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C m hm) z
  have hbase : motive (M + 1) le_rfl := by
    change DifferentiableAt ℝ
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          _ _ _ (M + 1) le_rfl) z
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ Fin.last (M + 1) := Fin.val_fin_le.mpr hms
    have hCprod :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
              (Fin.last (M + 1)) p.succ hpj) z :=
      differentiableAt_residualFactorProduct_C
        (ρ := ρ) (κ' := κ') p.succ hpj z
    have hA3early :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z :=
      differentiableAt_retainedPassiveA3WithoutLast
        (ρ := ρ) (κ' := κ') p z
    have hA1prod :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj)) z :=
      differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc
        ((Fin.castSucc_le_succ p).trans hpj) z hz
    have hA1unit :
        IsUnit
          (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦ (data.toCoordinateData).solvedA1 p)
            (Fin.last (M + 1)) p.castSucc
              ((Fin.castSucc_le_succ p).trans hpj)).det :=
      residualFactorProduct_solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p.castSucc
        ((Fin.castSucc_le_succ p).trans hpj)
    have hA1prodInv :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj))⁻¹) z :=
      (differentiableAt_matrix_inv_of_isUnit_det
        (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦ (data.toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj))
        hA1unit).comp z hA1prod
    have hC_A3 :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                (Fin.last (M + 1)) p.succ hpj *
              retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z :=
      differentiableAt_matrix_mul hCprod hA3early
    have hsummand :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹)) z :=
      (differentiableAt_matrix_mul hC_A3 hA1prodInv).neg
    have htail : motive (m + 1) hms := ih
    have hsum :
        DifferentiableAt ℝ
          (fun z : TopologyTuple ρ κ' ℝ ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C (m + 1) hms) z :=
      hsummand.add htail
    change DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          p.val (Nat.le_of_lt p.isLt)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            p.val (Nat.le_of_lt p.isLt)) =
          fun z ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C (m + 1) hms by
      funext z
      simpa [p] using
        retainedPassiveLowerLeftProductTailSum_castSucc
          (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p]
    simpa [p] using hsum
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase hm
  simpa [motive] using hcanon

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The Frechet derivative of the retained-passive lower-left product-tail sum
unfolds by differentiating the current product summand and adding the
successor-tail derivative.  This is only a derivative expansion; it does not
source-stage or target-stage the displayed derivative pieces. -/
theorem fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y r ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 r
    let A3fun :
        TopologyTuple ρ κ' ℝ →
          ∀ r : Fin (M + 1), Matrix (κ' r.succ) ρ ℝ :=
      fun y ↦
        retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        TopologyTuple ρ κ' ℝ →
          ∀ r : Fin (M + 1), Matrix (κ' r.succ) (κ' r.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Tailfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p.val (Nat.le_of_lt p.isLt)
    let Cprod : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let A3p : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦ A3fun y p
    let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
    let Nextfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p.val + 1) (Nat.succ_le_of_lt p.isLt)
    (fderiv ℝ Tailfun z) v =
      (fderiv ℝ (fun y ↦ -(Cprod y * A3p y * (Pcast y)⁻¹)) z) v +
        (fderiv ℝ Nextfun z) v := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := hz
  let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y r ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 r
  let A3fun :
      TopologyTuple ρ κ' ℝ →
        ∀ r : Fin (M + 1), Matrix (κ' r.succ) ρ ℝ :=
    fun y ↦
      retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      TopologyTuple ρ κ' ℝ →
        ∀ r : Fin (M + 1), Matrix (κ' r.succ) (κ' r.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Tailfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p.val (Nat.le_of_lt p.isLt)
  let Cprod : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let A3p : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦ A3fun y p
  let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (A1fun y) (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Summand : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ -(Cprod y * A3p y * (Pcast y)⁻¹)
  let Nextfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p.val + 1) (Nat.succ_le_of_lt p.isLt)
  have hTailfun :
      Tailfun = fun y ↦ Summand y + Nextfun y := by
    funext y
    simpa [Tailfun, Summand, Cprod, A3p, Pcast, Nextfun, A1fun, A3fun, Cfun] using
      retainedPassiveLowerLeftProductTailSum_castSucc
        (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p
  have hCprod :
      DifferentiableAt ℝ Cprod z := by
    simpa [Cprod, Cfun] using
      differentiableAt_residualFactorProduct_C
        (ρ := ρ) (κ' := κ') p.succ p.succ.le_last z
  have hA3p :
      DifferentiableAt ℝ A3p z := by
    simpa [A3p, A3fun] using
      differentiableAt_retainedPassiveA3WithoutLast
        (ρ := ρ) (κ' := κ') p z
  have hPcast :
      DifferentiableAt ℝ Pcast z := by
    simpa [Pcast, A1fun] using
      differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc p.castSucc.le_last z hz
  have hPunit : IsUnit (Pcast z).det := by
    simpa [Pcast, A1fun, data] using
      residualFactorProduct_solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p.castSucc p.castSucc.le_last
  have hPinv :
      DifferentiableAt ℝ (fun y ↦ (Pcast y)⁻¹) z :=
    (differentiableAt_matrix_inv_of_isUnit_det (Pcast z) hPunit).comp z hPcast
  have hC_A3 :
      DifferentiableAt ℝ (fun y ↦ Cprod y * A3p y) z :=
    differentiableAt_matrix_mul hCprod hA3p
  have hSummand : DifferentiableAt ℝ Summand z := by
    simpa [Summand] using
      (differentiableAt_matrix_mul hC_A3 hPinv).neg
  have hNext : DifferentiableAt ℝ Nextfun z := by
    simpa [Nextfun, A1fun, A3fun, Cfun] using
      differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (p.val + 1) (Nat.succ_le_of_lt p.isLt) z hz
  change (fderiv ℝ Tailfun z) v =
      (fderiv ℝ Summand z) v + (fderiv ℝ Nextfun z) v
  rw [hTailfun]
  rw [fderiv_fun_add hSummand hNext]
  rfl

set_option maxRecDepth 2048 in
set_option linter.style.longLine false in
/-- The recursive derivative unfold with the current retained-passive summand
expanded by the noncommutative product rule and the matrix-inverse derivative.

This still leaves the derivatives of `Cprod`, `A3p`, and `Pcast` explicit; it
does not source-stage or target-stage those derivative pieces. -/
theorem fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y r ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 r
    let A3fun :
        TopologyTuple ρ κ' ℝ →
          ∀ r : Fin (M + 1), Matrix (κ' r.succ) ρ ℝ :=
      fun y ↦
        retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
    let Cfun :
        TopologyTuple ρ κ' ℝ →
          ∀ r : Fin (M + 1), Matrix (κ' r.succ) (κ' r.castSucc) ℝ :=
      fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
    let Tailfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) p.val (Nat.le_of_lt p.isLt)
    let Cprod : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
          (Fin.last (M + 1)) p.succ p.succ.le_last
    let A3p : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
      fun y ↦ A3fun y p
    let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
    let Nextfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y) (A3fun y) (Cfun y) (p.val + 1) (Nat.succ_le_of_lt p.isLt)
    (fderiv ℝ Tailfun z) v =
      -((fderiv ℝ Cprod z) v * A3p z * (Pcast z)⁻¹)
        - (Cprod z * (fderiv ℝ A3p z) v * (Pcast z)⁻¹)
        + Cprod z * A3p z * (Pcast z)⁻¹ * (fderiv ℝ Pcast z) v * (Pcast z)⁻¹
        + (fderiv ℝ Nextfun z) v := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := hz
  let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y r ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 r
  let A3fun :
      TopologyTuple ρ κ' ℝ →
        ∀ r : Fin (M + 1), Matrix (κ' r.succ) ρ ℝ :=
    fun y ↦
      retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
  let Cfun :
      TopologyTuple ρ κ' ℝ →
        ∀ r : Fin (M + 1), Matrix (κ' r.succ) (κ' r.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
  let Tailfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) p.val (Nat.le_of_lt p.isLt)
  let Cprod : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := κ') (Cfun y)
        (Fin.last (M + 1)) p.succ p.succ.le_last
  let A3p : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦ A3fun y p
  let Pcast : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (A1fun y) (Fin.last (M + 1)) p.castSucc p.castSucc.le_last
  let Pinv : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ (Pcast y)⁻¹
  let Product : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ Cprod y * A3p y * Pinv y
  let Summand : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ -(Product y)
  let Nextfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y) (A3fun y) (Cfun y) (p.val + 1) (Nat.succ_le_of_lt p.isLt)
  let BCA : Matrix (κ' (Fin.last (M + 1))) (κ' p.succ) ℝ →L[ℝ]
      Matrix (κ' p.succ) ρ ℝ →L[ℝ]
        Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    matrixMulContinuousLinearMap
      (l := κ' (Fin.last (M + 1))) (m := κ' p.succ) (n := ρ)
  let BHP : Matrix (κ' (Fin.last (M + 1))) ρ ℝ →L[ℝ]
      Matrix ρ ρ ℝ →L[ℝ]
        Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    matrixMulContinuousLinearMap (l := κ' (Fin.last (M + 1))) (m := ρ) (n := ρ)
  have hCprod :
      DifferentiableAt ℝ Cprod z := by
    simpa [Cprod, Cfun] using
      differentiableAt_residualFactorProduct_C
        (ρ := ρ) (κ' := κ') p.succ p.succ.le_last z
  have hA3p :
      DifferentiableAt ℝ A3p z := by
    simpa [A3p, A3fun] using
      differentiableAt_retainedPassiveA3WithoutLast
        (ρ := ρ) (κ' := κ') p z
  have hPcast :
      DifferentiableAt ℝ Pcast z := by
    simpa [Pcast, A1fun] using
      differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc p.castSucc.le_last z hz
  have hPunit : IsUnit (Pcast z).det := by
    simpa [Pcast, A1fun, data] using
      residualFactorProduct_solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p.castSucc p.castSucc.le_last
  have hPinv :
      DifferentiableAt ℝ Pinv z := by
    exact (differentiableAt_matrix_inv_of_isUnit_det (Pcast z) hPunit).comp z hPcast
  have hCA :
      DifferentiableAt ℝ (fun y ↦ Cprod y * A3p y) z :=
    differentiableAt_matrix_mul hCprod hA3p
  have hProduct : DifferentiableAt ℝ Product z := by
    simpa [Product, Pinv] using differentiableAt_matrix_mul hCA hPinv
  have hSummand : DifferentiableAt ℝ Summand z := by
    simpa [Summand] using hProduct.neg
  have hNext : DifferentiableAt ℝ Nextfun z := by
    simpa [Nextfun, A1fun, A3fun, Cfun] using
      differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (p.val + 1) (Nat.succ_le_of_lt p.isLt) z hz
  have hTail :
      (fderiv ℝ Tailfun z) v =
        (fderiv ℝ Summand z) v + (fderiv ℝ Nextfun z) v := by
    simpa [Tailfun, Summand, Product, Pinv, Cprod, A3p, Pcast, Nextfun,
      A1fun, A3fun, Cfun] using
      fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply
        (ρ := ρ) (κ' := κ') hz v p
  have hInvHas : HasFDerivAt Pinv
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ)
          (Pcast z)⁻¹ (Pcast z)⁻¹)).comp
        (fderiv ℝ Pcast z)) z := by
    simpa [Pinv, Function.comp_def] using
      ((hasFDerivAt_matrix_inv_of_isUnit_det (Pcast z) hPunit).comp
        (x := z) hPcast.hasFDerivAt)
  have hPinv_fderiv :
      fderiv ℝ Pinv z =
        ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ)
          (Pcast z)⁻¹ (Pcast z)⁻¹)).comp
        (fderiv ℝ Pcast z)) :=
    hInvHas.fderiv
  have hPinv_apply :
      (fderiv ℝ Pinv z) v =
        -((Pcast z)⁻¹ * (fderiv ℝ Pcast z) v * (Pcast z)⁻¹) := by
    rw [hPinv_fderiv]
    simp [ContinuousLinearMap.mulLeftRight_apply]
  have hCA_fderiv :
      fderiv ℝ (fun y ↦ Cprod y * A3p y) z =
        BCA.precompR _ (Cprod z) (fderiv ℝ A3p z) +
          BCA.precompL _ (fderiv ℝ Cprod z) (A3p z) := by
    simpa [BCA] using
      (BCA.hasFDerivAt_of_bilinear hCprod.hasFDerivAt hA3p.hasFDerivAt).fderiv
  have hCA_apply :
      (fderiv ℝ (fun y ↦ Cprod y * A3p y) z) v =
        Cprod z * (fderiv ℝ A3p z) v + (fderiv ℝ Cprod z) v * A3p z := by
    simpa [BCA, matrixMulContinuousLinearMap_apply] using
      congrArg
        (fun L : TopologyTuple ρ κ' ℝ →L[ℝ]
          Matrix (κ' (Fin.last (M + 1))) ρ ℝ ↦ L v)
        hCA_fderiv
  have hProduct_fderiv :
      fderiv ℝ Product z =
        BHP.precompR _ ((fun y ↦ Cprod y * A3p y) z) (fderiv ℝ Pinv z) +
          BHP.precompL _ (fderiv ℝ (fun y ↦ Cprod y * A3p y) z) (Pinv z) := by
    simpa [Product, BHP] using
      (BHP.hasFDerivAt_of_bilinear hCA.hasFDerivAt hPinv.hasFDerivAt).fderiv
  have hProduct_apply :
      (fderiv ℝ Product z) v =
        (Cprod z * A3p z) * (fderiv ℝ Pinv z) v +
          (fderiv ℝ (fun y ↦ Cprod y * A3p y) z) v * Pinv z := by
    simpa [Product, BHP, matrixMulContinuousLinearMap_apply] using
      congrArg
        (fun L : TopologyTuple ρ κ' ℝ →L[ℝ]
          Matrix (κ' (Fin.last (M + 1))) ρ ℝ ↦ L v)
        hProduct_fderiv
  have hSummand_apply :
      (fderiv ℝ Summand z) v =
        -((fderiv ℝ Cprod z) v * A3p z * (Pcast z)⁻¹)
          - (Cprod z * (fderiv ℝ A3p z) v * (Pcast z)⁻¹)
          + Cprod z * A3p z * (Pcast z)⁻¹ * (fderiv ℝ Pcast z) v *
              (Pcast z)⁻¹ := by
    calc
      (fderiv ℝ Summand z) v
          = -((fderiv ℝ Product z) v) := by
              simp [Summand]
      _ =
          -((Cprod z * A3p z) * (fderiv ℝ Pinv z) v +
              (fderiv ℝ (fun y ↦ Cprod y * A3p y) z) v * Pinv z) := by
            rw [hProduct_apply]
      _ =
          -((fderiv ℝ Cprod z) v * A3p z * (Pcast z)⁻¹)
            - (Cprod z * (fderiv ℝ A3p z) v * (Pcast z)⁻¹)
            + Cprod z * A3p z * (Pcast z)⁻¹ * (fderiv ℝ Pcast z) v *
                (Pcast z)⁻¹ := by
            rw [hPinv_apply, hCA_apply]
            simp only [Pinv, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_neg]
            abel_nf
  calc
    (fderiv ℝ Tailfun z) v
        = (fderiv ℝ Summand z) v + (fderiv ℝ Nextfun z) v := hTail
    _ =
        -((fderiv ℝ Cprod z) v * A3p z * (Pcast z)⁻¹)
          - (Cprod z * (fderiv ℝ A3p z) v * (Pcast z)⁻¹)
          + Cprod z * A3p z * (Pcast z)⁻¹ * (fderiv ℝ Pcast z) v *
              (Pcast z)⁻¹
          + (fderiv ℝ Nextfun z) v := by
        rw [hSummand_apply]

/-- The explicit lower-left product-tail sum built from solved `A1`, zeroed
early `A3`, and stored `C` blocks is `C^1` at tuple determinant-chart
points. -/
theorem contDiffAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M + 1)
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C m hm) z := by
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := by
    exact hz
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C m hm) z
  have hbase : motive (M + 1) le_rfl := by
    change ContDiffAt ℝ 1
      (fun _z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          _ _ _ (M + 1) le_rfl) z
    simpa using
      (contDiffAt_const (𝕜 := ℝ) (n := 1) (x := z)
        (c := (0 : Matrix (κ' (Fin.last (M + 1))) ρ ℝ)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ Fin.last (M + 1) := Fin.val_fin_le.mpr hms
    have hCprod :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
              (Fin.last (M + 1)) p.succ hpj) z :=
      contDiffAt_residualFactorProduct_C
        (ρ := ρ) (κ' := κ') p.succ hpj z
    have hA3early :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z :=
      contDiffAt_retainedPassiveA3WithoutLast
        (ρ := ρ) (κ' := κ') p z
    have hA1prod :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj)) z :=
      contDiffAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc
        ((Fin.castSucc_le_succ p).trans hpj) z hz
    have hA1unit :
        IsUnit
          (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦ (data.toCoordinateData).solvedA1 p)
            (Fin.last (M + 1)) p.castSucc
              ((Fin.castSucc_le_succ p).trans hpj)).det :=
      residualFactorProduct_solvedA1_det_isUnit_of_detChart
        (K := ℝ) (ρ := ρ) data hdet p.castSucc
        ((Fin.castSucc_le_succ p).trans hpj)
    have hA1prodInv :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj))⁻¹) z :=
      (contDiffAt_matrix_inv_of_isUnit_det
        (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦ (data.toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj))
        hA1unit).comp z hA1prod
    have hC_A3 :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            residualFactorProduct (K := ℝ) (κ := κ')
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                (Fin.last (M + 1)) p.succ hpj *
              retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p) z :=
      contDiffAt_matrix_mul hCprod hA3early
    have hsummand :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹)) z :=
      (contDiffAt_matrix_mul hC_A3 hA1prodInv).neg
    have htail : motive (m + 1) hms := ih
    have hsum :
        ContDiffAt ℝ 1
          (fun z : TopologyTuple ρ κ' ℝ ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C (m + 1) hms) z :=
      hsummand.add htail
    change ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          p.val (Nat.le_of_lt p.isLt)) z
    rw [show
        (fun z : TopologyTuple ρ κ' ℝ ↦
          retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            p.val (Nat.le_of_lt p.isLt)) =
          fun z ↦
            -(residualFactorProduct (K := ℝ) (κ := κ')
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p *
                (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C (m + 1) hms by
      funext z
      simpa [p] using
        retainedPassiveLowerLeftProductTailSum_castSucc
          (K := ℝ) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p]
    simpa [p] using hsum
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase hm
  simpa [motive] using hcanon

/-- On the tuple determinant chart, each solved full `A3` block is
differentiable as an ambient tuple-coordinate function. -/
theorem differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA3 p) z := by
  induction p using Fin.lastCases with
  | last =>
      have hF3 := differentiableAt_F3 (ρ := ρ) (κ' := κ') z
      have hEarlyTail :
          DifferentiableAt ℝ
            (fun z : TopologyTuple ρ κ' ℝ ↦
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C 0
                (Nat.zero_le (M + 1))) z :=
        differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') 0 (Nat.zero_le (M + 1)) z hz
      have hCtopLast :
          DifferentiableAt ℝ
            (fun z : TopologyTuple ρ κ' ℝ ↦
              residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (Fin.last (M + 1)) (Fin.last M).castSucc
                  (Fin.last M).castSucc.le_last) z :=
        differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last z hz
      have hlast :
          DifferentiableAt ℝ
            (fun z : TopologyTuple ρ κ' ℝ ↦
              -((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3 -
                  retainedPassiveLowerLeftProductTailSum
                    (K := ℝ) (ρ := ρ) (κ := κ')
                    (fun p : Fin (M + 1) ↦
                      ((ofTopologyTuple (K := ℝ) (ρ := ρ)
                        (κ' := κ') z).toCoordinateData).solvedA1 p)
                    (retainedPassiveA3WithoutLast
                      (K := ℝ) (ρ := ρ)
                      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                    (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                    0 (Nat.zero_le (M + 1))) *
                residualFactorProduct (K := ℝ)
                  (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) (Fin.last M).castSucc
                    (Fin.last M).castSucc.le_last) z :=
        differentiableAt_matrix_mul (hF3.sub hEarlyTail).neg hCtopLast
      simpa [RetainedPassiveCoordinateData.solvedA3,
        RetainedPassiveCoordinateData.solvedA1, toCoordinateData] using hlast
  | cast p =>
      have hseed := differentiableAt_A3seed (ρ := ρ) (κ' := κ') p.castSucc z
      have hfun :
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ)
              (κ' := κ') z).toCoordinateData).solvedA3 p.castSucc) =
          fun z ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p.castSucc := by
        funext z
        exact
          retainedPassiveSolvedA3_eq_of_ne_last
            (K := ℝ) (ρ := ρ) (κ' := κ')
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3
            (Fin.castSucc_ne_last p)
      rw [hfun]
      exact hseed

/-- On the tuple determinant chart, each solved full `A3` block is `C^1` as an
ambient tuple-coordinate function. -/
theorem contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContDiffAt ℝ 1
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA3 p) z := by
  induction p using Fin.lastCases with
  | last =>
      have hF3 := contDiffAt_F3 (ρ := ρ) (κ' := κ') z
      have hEarlyTail :
          ContDiffAt ℝ 1
            (fun z : TopologyTuple ρ κ' ℝ ↦
              retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C 0
                (Nat.zero_le (M + 1))) z :=
        contDiffAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') 0 (Nat.zero_le (M + 1)) z hz
      have hCtopLast :
          ContDiffAt ℝ 1
            (fun z : TopologyTuple ρ κ' ℝ ↦
              residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                (Fin.last (M + 1)) (Fin.last M).castSucc
                  (Fin.last M).castSucc.le_last) z :=
        contDiffAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last z hz
      have hlast :
          ContDiffAt ℝ 1
            (fun z : TopologyTuple ρ κ' ℝ ↦
              -((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3 -
                  retainedPassiveLowerLeftProductTailSum
                    (K := ℝ) (ρ := ρ) (κ := κ')
                    (fun p : Fin (M + 1) ↦
                      ((ofTopologyTuple (K := ℝ) (ρ := ρ)
                        (κ' := κ') z).toCoordinateData).solvedA1 p)
                    (retainedPassiveA3WithoutLast
                      (K := ℝ) (ρ := ρ)
                      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
                    (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
                    0 (Nat.zero_le (M + 1))) *
                residualFactorProduct (K := ℝ)
                  (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) (Fin.last M).castSucc
                    (Fin.last M).castSucc.le_last) z :=
        contDiffAt_matrix_mul (hF3.sub hEarlyTail).neg hCtopLast
      simpa [RetainedPassiveCoordinateData.solvedA3,
        RetainedPassiveCoordinateData.solvedA1, toCoordinateData] using hlast
  | cast p =>
      have hseed := contDiffAt_A3seed (ρ := ρ) (κ' := κ') p.castSucc z
      have hfun :
          (fun z : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ)
              (κ' := κ') z).toCoordinateData).solvedA3 p.castSucc) =
          fun z ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed p.castSucc := by
        funext z
        exact
          retainedPassiveSolvedA3_eq_of_ne_last
            (K := ℝ) (ρ := ρ) (κ' := κ')
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F3
            (Fin.castSucc_ne_last p)
      rw [hfun]
      exact hseed

/-- On the tuple determinant chart, the retained-passive edge tuple read in
raw block order is differentiable as an ambient tuple-coordinate map.

This is only the differentiability assembly for the already-expanded raw-order
components.  It does not state a Jacobian determinant formula, a measure
pushforward, normal crossings, pole order, or an RLCT extraction. -/
theorem differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hA1passive :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).1) z := by
    rw [differentiableAt_pi]
    intro p
    have hA1 :=
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
    have hF2 :=
      differentiableAt_F2full
        (ρ := ρ) (κ' := κ') p.succ.succ z
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
    simpa [raw, topologyTupleEdgeRawOrder_A1passive, toCoordinateData] using
      hA1.add (differentiableAt_matrix_mul hF2 hA3)
  have hF2target :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.1) z := by
    rw [differentiableAt_pi]
    intro p
    have hA1 :=
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hF2left :=
      differentiableAt_F2full
        (ρ := ρ) (κ' := κ') p.castSucc z
    have hF2right :=
      differentiableAt_F2full
        (ρ := ρ) (κ' := κ') p.succ z
    have hC :=
      differentiableAt_C (ρ := ρ) (κ' := κ') p z
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hA1_F2 :
        DifferentiableAt ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.castSucc) z :=
      differentiableAt_matrix_mul hA1 hF2left
    have hA3_F2 :
        DifferentiableAt ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3 p *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.castSucc) z :=
      differentiableAt_matrix_mul hA3 hF2left
    have hright :
        DifferentiableAt ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2 p.succ *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.C p -
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3 p *
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                    p.castSucc)) z :=
      differentiableAt_matrix_mul hF2right (hC.sub hA3_F2)
    simpa [raw, topologyTupleEdgeRawOrder_F2, toCoordinateData] using
      hA1_F2.neg.add hright
  have hA3passive :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.1) z := by
    rw [differentiableAt_pi]
    intro p
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc z hz
    simpa [raw, topologyTupleEdgeRawOrder_A3passive, toCoordinateData] using hA3
  have hCtarget :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.1) z := by
    rw [differentiableAt_pi]
    intro p
    have hC :=
      differentiableAt_C (ρ := ρ) (κ' := κ') p z
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hF2 :=
      differentiableAt_F2full
        (ρ := ρ) (κ' := κ') p.castSucc z
    simpa [raw, topologyTupleEdgeRawOrder_C, toCoordinateData] using
      hC.sub (differentiableAt_matrix_mul hA3 hF2)
  have hCtopTarget :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.1) z := by
    have hA1 :=
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)) z hz
    have hF2 :=
      differentiableAt_F2full
        (ρ := ρ) (κ' := κ') ((0 : Fin (M + 1)).succ) z
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)) z hz
    simpa [raw, topologyTupleEdgeRawOrder_Ctop, toCoordinateData] using
      hA1.add (differentiableAt_matrix_mul hF2 hA3)
  have hF3target :
      DifferentiableAt ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.2) z := by
    have hA3 :=
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (Fin.last M) z hz
    simpa [raw, topologyTupleEdgeRawOrder_F3, toCoordinateData] using hA3
  change DifferentiableAt ℝ
    (fun y : TopologyTuple ρ κ' ℝ ↦
      ((raw y).1,
        ((raw y).2.1,
          ((raw y).2.2.1,
            ((raw y).2.2.2.1,
              ((raw y).2.2.2.2.1, (raw y).2.2.2.2.2)))))) z
  exact
    hA1passive.prodMk
      (hF2target.prodMk
        (hA3passive.prodMk
          (hCtarget.prodMk
            (hCtopTarget.prodMk hF3target))))

set_option maxRecDepth 2048 in
/-- The `C` component of the actual raw-order derivative becomes the formal
`C` component after the lower-left target shear. -/
theorem fderiv_topologyTupleEdgeRawOrder_C_component_unshear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.1 p) z) v
      + (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) z) v *
        coord.F2 p.castSucc =
      v.2.2.2.1 p - coord.solvedA3 p * v.2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Cfun : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.C p
  let Gfun : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3 p
  let Ffun : TopologyTuple ρ κ' ℝ → Matrix ρ (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2 p.castSucc
  let B : Matrix (κ' p.succ) ρ ℝ →L[ℝ]
      Matrix ρ (κ' p.castSucc) ℝ →L[ℝ]
        Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    matrixMulContinuousLinearMap (l := κ' p.succ) (m := ρ) (n := κ' p.castSucc)
  have hCdiff : DifferentiableAt ℝ Cfun z := by
    simpa [Cfun, toCoordinateData] using
      differentiableAt_C (ρ := ρ) (κ' := κ') p z
  have hGdiff : DifferentiableAt ℝ Gfun z := by
    simpa [Gfun] using
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
  have hFdiff : DifferentiableAt ℝ Ffun z := by
    simpa [Ffun, toCoordinateData] using
      differentiableAt_F2full (ρ := ρ) (κ' := κ') p.castSucc z
  have hrawC :
      (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.1 p) =
        fun y ↦ Cfun y - Gfun y * Ffun y := by
    funext y
    simp [raw, Cfun, Gfun, Ffun, toCoordinateData]
  have hrawG :
      (fun y : TopologyTuple ρ κ' ℝ ↦
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) =
        Gfun := by
    funext y
    simp [raw, Gfun]
  have hmulFDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Gfun y * Ffun y) z =
        B.precompR _ (Gfun z) (fderiv ℝ Ffun z) +
          B.precompL _ (fderiv ℝ Gfun z) (Ffun z) := by
    simpa [B] using
      (B.hasFDerivAt_of_bilinear hGdiff.hasFDerivAt hFdiff.hasFDerivAt).fderiv
  have hC_apply : (fderiv ℝ Cfun z) v = v.2.2.2.1 p := by
    let LC : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.2.2.1 p
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLC :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.1 p) z = LC :=
      LC.fderiv
    change (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.1 p) z) v = v.2.2.2.1 p
    rw [hLC]
    rfl
  have hF_apply : (fderiv ℝ Ffun z) v = v.2.1 p := by
    let LF : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ (κ' p.castSucc) ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.1 p
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hFfun :
        Ffun = fun y : TopologyTuple ρ κ' ℝ ↦ y.2.1 p := by
      funext y
      simp [Ffun, toCoordinateData, ofTopologyTuple]
    have hLF :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.1 p) z = LF :=
      LF.fderiv
    rw [hFfun, hLF]
    rfl
  calc
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.1 p) z) v
        + (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) z) v *
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.castSucc
      = (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Cfun y - Gfun y * Ffun y) z) v
          + (fderiv ℝ Gfun z) v * Ffun z := by
          rw [hrawC, hrawG]
    _ = ((fderiv ℝ Cfun z) v -
          (Gfun z * (fderiv ℝ Ffun z) v + (fderiv ℝ Gfun z) v * Ffun z))
          + (fderiv ℝ Gfun z) v * Ffun z := by
          rw [fderiv_fun_sub hCdiff (differentiableAt_matrix_mul hGdiff hFdiff)]
          rw [hmulFDeriv]
          simp [B, matrixMulContinuousLinearMap_apply]
    _ = (fderiv ℝ Cfun z) v - Gfun z * (fderiv ℝ Ffun z) v := by
          abel
    _ = v.2.2.2.1 p -
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3 p *
          v.2.1 p := by
          simp [hC_apply, hF_apply, Gfun]

set_option maxHeartbeats 800000 in
-- This component proof expands five coupled matrix-product derivatives and
-- then performs one entrywise cancellation; the default heartbeat budget is
-- too small for the finite bookkeeping.
set_option maxRecDepth 2048 in
/-- The `F2` component of the actual raw-order derivative becomes the formal
`F2` component after the top-left and next-`F2` shear corrections. -/
theorem fderiv_topologyTupleEdgeRawOrder_F2_component_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.1 p) z) v
      + (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) z) v *
          coord.F2 p.castSucc
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
          coord.C p =
      -(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) * v.2.1 p
        + coord.F2 p.succ * v.2.2.2.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Afun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA1 p
  let Ffun : TopologyTuple ρ κ' ℝ → Matrix ρ (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2 p.castSucc
  let Hfun : TopologyTuple ρ κ' ℝ → Matrix ρ (κ' p.succ) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2 p.succ
  let Gfun : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3 p
  let Cfun : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.C p
  let BAF : Matrix ρ ρ ℝ →L[ℝ]
      Matrix ρ (κ' p.castSucc) ℝ →L[ℝ]
        Matrix ρ (κ' p.castSucc) ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := ρ) (n := κ' p.castSucc)
  let BHG : Matrix ρ (κ' p.succ) ℝ →L[ℝ]
      Matrix (κ' p.succ) ρ ℝ →L[ℝ]
        Matrix ρ ρ ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := κ' p.succ) (n := ρ)
  let BGF : Matrix (κ' p.succ) ρ ℝ →L[ℝ]
      Matrix ρ (κ' p.castSucc) ℝ →L[ℝ]
        Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    matrixMulContinuousLinearMap (l := κ' p.succ) (m := ρ) (n := κ' p.castSucc)
  let BHB : Matrix ρ (κ' p.succ) ℝ →L[ℝ]
      Matrix (κ' p.succ) (κ' p.castSucc) ℝ →L[ℝ]
        Matrix ρ (κ' p.castSucc) ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := κ' p.succ) (n := κ' p.castSucc)
  have hAdiff : DifferentiableAt ℝ Afun z := by
    simpa [Afun] using
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
  have hFdiff : DifferentiableAt ℝ Ffun z := by
    simpa [Ffun, toCoordinateData] using
      differentiableAt_F2full (ρ := ρ) (κ' := κ') p.castSucc z
  have hHdiff : DifferentiableAt ℝ Hfun z := by
    simpa [Hfun, toCoordinateData] using
      differentiableAt_F2full (ρ := ρ) (κ' := κ') p.succ z
  have hGdiff : DifferentiableAt ℝ Gfun z := by
    simpa [Gfun] using
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
  have hCdiff : DifferentiableAt ℝ Cfun z := by
    simpa [Cfun, toCoordinateData] using
      differentiableAt_C (ρ := ρ) (κ' := κ') p z
  have hrawF :
      (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.1 p) =
        fun y ↦ -(Afun y * Ffun y) +
          Hfun y * (Cfun y - Gfun y * Ffun y) := by
    funext y
    simp [raw, Afun, Ffun, Hfun, Gfun, Cfun, toCoordinateData]
  have hrawA :
      (fun y : TopologyTuple ρ κ' ℝ ↦
          rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) =
        fun y ↦ Afun y + Hfun y * Gfun y := by
    funext y
    cases p using Fin.cases with
    | zero =>
        change (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y).2.2.2.2.1 =
          Afun y + Hfun y * Gfun y
        rw [topologyTupleEdgeRawOrder_Ctop]
    | succ p =>
        change (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y).1 p =
          Afun y + Hfun y * Gfun y
        rw [topologyTupleEdgeRawOrder_A1passive]
  have hAFDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Afun y * Ffun y) z =
        BAF.precompR _ (Afun z) (fderiv ℝ Ffun z) +
          BAF.precompL _ (fderiv ℝ Afun z) (Ffun z) := by
    simpa [BAF] using
      (BAF.hasFDerivAt_of_bilinear hAdiff.hasFDerivAt hFdiff.hasFDerivAt).fderiv
  have hHGDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z =
        BHG.precompR _ (Hfun z) (fderiv ℝ Gfun z) +
          BHG.precompL _ (fderiv ℝ Hfun z) (Gfun z) := by
    simpa [BHG] using
      (BHG.hasFDerivAt_of_bilinear hHdiff.hasFDerivAt hGdiff.hasFDerivAt).fderiv
  have hGFDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Gfun y * Ffun y) z =
        BGF.precompR _ (Gfun z) (fderiv ℝ Ffun z) +
          BGF.precompL _ (fderiv ℝ Gfun z) (Ffun z) := by
    simpa [BGF] using
      (BGF.hasFDerivAt_of_bilinear hGdiff.hasFDerivAt hFdiff.hasFDerivAt).fderiv
  have hHCDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Hfun y * (Cfun y - Gfun y * Ffun y)) z =
        BHB.precompR _ (Hfun z)
            (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
              Cfun y - Gfun y * Ffun y) z) +
          BHB.precompL _ (fderiv ℝ Hfun z) (Cfun z - Gfun z * Ffun z) := by
    have hinner :
        DifferentiableAt ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦ Cfun y - Gfun y * Ffun y) z :=
      hCdiff.sub (differentiableAt_matrix_mul hGdiff hFdiff)
    simpa [BHB] using
      (BHB.hasFDerivAt_of_bilinear hHdiff.hasFDerivAt hinner.hasFDerivAt).fderiv
  have hrawFDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          -(Afun y * Ffun y) + Hfun y * (Cfun y - Gfun y * Ffun y)) z =
        -fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Afun y * Ffun y) z +
          fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
            Hfun y * (Cfun y - Gfun y * Ffun y)) z := by
    calc
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          -(Afun y * Ffun y) + Hfun y * (Cfun y - Gfun y * Ffun y)) z =
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ -(Afun y * Ffun y)) z +
          fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
            Hfun y * (Cfun y - Gfun y * Ffun y)) z := by
          simpa only using
            fderiv_fun_add
              ((differentiableAt_matrix_mul hAdiff hFdiff).neg)
              (differentiableAt_matrix_mul hHdiff
                (hCdiff.sub (differentiableAt_matrix_mul hGdiff hFdiff)))
      _ =
        -fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Afun y * Ffun y) z +
          fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
            Hfun y * (Cfun y - Gfun y * Ffun y)) z := by
          rw [fderiv_fun_neg]
  have hrawADeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Afun y + Hfun y * Gfun y) z =
        fderiv ℝ Afun z +
          fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z := by
    rw [fderiv_fun_add hAdiff (differentiableAt_matrix_mul hHdiff hGdiff)]
  have hF_apply : (fderiv ℝ Ffun z) v = v.2.1 p := by
    let LF : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ (κ' p.castSucc) ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.1 p
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hFfun :
        Ffun = fun y : TopologyTuple ρ κ' ℝ ↦ y.2.1 p := by
      funext y
      simp [Ffun, toCoordinateData, ofTopologyTuple]
    have hLF :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.1 p) z = LF :=
      LF.fderiv
    rw [hFfun, hLF]
    rfl
  have hC_apply : (fderiv ℝ Cfun z) v = v.2.2.2.1 p := by
    let LC : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.2.2.1 p
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLC :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.1 p) z = LC :=
      LC.fderiv
    change (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.1 p) z) v = v.2.2.2.1 p
    rw [hLC]
    rfl
  let dA : Matrix ρ ρ ℝ := (fderiv ℝ Afun z) v
  let dF : Matrix ρ (κ' p.castSucc) ℝ := (fderiv ℝ Ffun z) v
  let dH : Matrix ρ (κ' p.succ) ℝ := (fderiv ℝ Hfun z) v
  let dG : Matrix (κ' p.succ) ρ ℝ := (fderiv ℝ Gfun z) v
  let dC : Matrix (κ' p.succ) (κ' p.castSucc) ℝ := (fderiv ℝ Cfun z) v
  have hAF_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Afun y * Ffun y) z) v =
        Afun z * dF + dA * Ffun z := by
    dsimp [dA, dF]
    rw [hAFDeriv]
    simp [BAF, matrixMulContinuousLinearMap_apply]
  have hHG_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z) v =
        Hfun z * dG + dH * Gfun z := by
    dsimp [dH, dG]
    rw [hHGDeriv]
    simp [BHG, matrixMulContinuousLinearMap_apply]
  have hGF_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Gfun y * Ffun y) z) v =
        Gfun z * dF + dG * Ffun z := by
    dsimp [dF, dG]
    rw [hGFDeriv]
    simp [BGF, matrixMulContinuousLinearMap_apply]
  have hCFDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Cfun y - Gfun y * Ffun y) z =
        fderiv ℝ Cfun z -
          (BGF.precompR _ (Gfun z) (fderiv ℝ Ffun z) +
            BGF.precompL _ (fderiv ℝ Gfun z) (Ffun z)) := by
    simpa [BGF] using
      (hCdiff.hasFDerivAt.sub
        (BGF.hasFDerivAt_of_bilinear hGdiff.hasFDerivAt hFdiff.hasFDerivAt)).fderiv
  have hCF_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Cfun y - Gfun y * Ffun y) z) v =
        dC - (Gfun z * dF + dG * Ffun z) := by
    dsimp [dC, dF, dG]
    rw [hCFDeriv]
    simp [BGF, matrixMulContinuousLinearMap_apply]
  have hHC_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Hfun y * (Cfun y - Gfun y * Ffun y)) z) v =
        Hfun z * (dC - (Gfun z * dF + dG * Ffun z)) +
          dH * (Cfun z - Gfun z * Ffun z) := by
    dsimp [dH]
    rw [hHCDeriv]
    simp [BHB, matrixMulContinuousLinearMap_apply, hCF_apply, Matrix.mul_sub]
  have hrawF_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          -(Afun y * Ffun y) + Hfun y * (Cfun y - Gfun y * Ffun y)) z) v =
        -(Afun z * dF + dA * Ffun z) +
          (Hfun z * (dC - (Gfun z * dF + dG * Ffun z)) +
            dH * (Cfun z - Gfun z * Ffun z)) := by
    rw [hrawFDeriv]
    simp [hAF_apply, hHC_apply]
  have hrawA_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Afun y + Hfun y * Gfun y) z) v =
        dA + (Hfun z * dG + dH * Gfun z) := by
    rw [hrawADeriv]
    simp [hHG_apply, dA]
  have hcancel :
      (-(Afun z * dF + dA * Ffun z)
          + (Hfun z * (dC - (Gfun z * dF + dG * Ffun z))
            + dH * (Cfun z - Gfun z * Ffun z)))
        + (dA + (Hfun z * dG + dH * Gfun z)) * Ffun z
        - dH * Cfun z =
      -(Afun z + Hfun z * Gfun z) * dF + Hfun z * dC := by
    ext i j
    simp [sub_eq_add_neg, Matrix.mul_apply, Matrix.mul_assoc, Matrix.mul_add,
      Matrix.add_mul]
    abel_nf
  calc
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.1 p) z) v
        + (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') (raw y) p) z) v *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.castSucc
        - (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.succ) z) v *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.C p
      =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
            -(Afun y * Ffun y) +
              Hfun y * (Cfun y - Gfun y * Ffun y)) z) v
        + (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
            Afun y + Hfun y * Gfun y) z) v * Ffun z
        - (fderiv ℝ Hfun z) v * Cfun z := by
          rw [hrawF, hrawA]
    _ =
        (-(Afun z * dF + dA * Ffun z)
          + (Hfun z * (dC - (Gfun z * dF + dG * Ffun z))
            + dH * (Cfun z - Gfun z * Ffun z)))
        + (dA + (Hfun z * dG + dH * Gfun z)) * Ffun z
        - dH * Cfun z := by
          rw [hrawF_apply, hrawA_apply]
    _ = -(Afun z + Hfun z * Gfun z) * (fderiv ℝ Ffun z) v
        + Hfun z * (fderiv ℝ Cfun z) v := by
          simpa [dF, dC] using hcancel
    _ =
        -((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA1 p +
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.succ *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3 p) *
            v.2.1 p +
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.succ *
            v.2.2.2.1 p := by
          simp [Afun, Ffun, Hfun, Gfun, Cfun, hF_apply, hC_apply]

/-- On the tuple determinant chart, the retained-passive edge tuple read in
raw block order is `C^1` as an ambient tuple-coordinate map.

This is only the `C^1` assembly for the already-expanded raw-order components.
It does not state a Jacobian determinant formula, a measure pushforward,
normal crossings, pole order, or an RLCT extraction. -/
theorem contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' ℝ)
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContDiffAt ℝ 1
      (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hA1passive :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).1) z := by
    rw [contDiffAt_pi]
    intro p
    have hA1 :=
      contDiffAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
    have hF2 :=
      contDiffAt_F2full
        (ρ := ρ) (κ' := κ') p.succ.succ z
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
    simpa [raw, topologyTupleEdgeRawOrder_A1passive, toCoordinateData] using
      hA1.add (contDiffAt_matrix_mul hF2 hA3)
  have hF2target :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.1) z := by
    rw [contDiffAt_pi]
    intro p
    have hA1 :=
      contDiffAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hF2left :=
      contDiffAt_F2full
        (ρ := ρ) (κ' := κ') p.castSucc z
    have hF2right :=
      contDiffAt_F2full
        (ρ := ρ) (κ' := κ') p.succ z
    have hC :=
      contDiffAt_C (ρ := ρ) (κ' := κ') p z
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hA1_F2 :
        ContDiffAt ℝ 1
          (fun y : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.castSucc) z :=
      contDiffAt_matrix_mul hA1 hF2left
    have hA3_F2 :
        ContDiffAt ℝ 1
          (fun y : TopologyTuple ρ κ' ℝ ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3 p *
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.castSucc) z :=
      contDiffAt_matrix_mul hA3 hF2left
    have hright :
        ContDiffAt ℝ 1
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2 p.succ *
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.C p -
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3 p *
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                    p.castSucc)) z :=
      contDiffAt_matrix_mul hF2right (hC.sub hA3_F2)
    simpa [raw, topologyTupleEdgeRawOrder_F2, toCoordinateData] using
      hA1_F2.neg.add hright
  have hA3passive :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.1) z := by
    rw [contDiffAt_pi]
    intro p
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.castSucc z hz
    simpa [raw, topologyTupleEdgeRawOrder_A3passive, toCoordinateData] using hA3
  have hCtarget :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.1) z := by
    rw [contDiffAt_pi]
    intro p
    have hC :=
      contDiffAt_C (ρ := ρ) (κ' := κ') p z
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p z hz
    have hF2 :=
      contDiffAt_F2full
        (ρ := ρ) (κ' := κ') p.castSucc z
    simpa [raw, topologyTupleEdgeRawOrder_C, toCoordinateData] using
      hC.sub (contDiffAt_matrix_mul hA3 hF2)
  have hCtopTarget :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.1) z := by
    have hA1 :=
      contDiffAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)) z hz
    have hF2 :=
      contDiffAt_F2full
        (ρ := ρ) (κ' := κ') ((0 : Fin (M + 1)).succ) z
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)) z hz
    simpa [raw, topologyTupleEdgeRawOrder_Ctop, toCoordinateData] using
      hA1.add (contDiffAt_matrix_mul hF2 hA3)
  have hF3target :
      ContDiffAt ℝ 1 (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.2) z := by
    have hA3 :=
      contDiffAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (Fin.last M) z hz
    simpa [raw, topologyTupleEdgeRawOrder_F3, toCoordinateData] using hA3
  change ContDiffAt ℝ 1
    (fun y : TopologyTuple ρ κ' ℝ ↦
      ((raw y).1,
        ((raw y).2.1,
          ((raw y).2.2.1,
            ((raw y).2.2.2.1,
              ((raw y).2.2.2.2.1, (raw y).2.2.2.2.2)))))) z
  exact
    hA1passive.prodMk
      (hF2target.prodMk
        (hA3passive.prodMk
          (hCtarget.prodMk
            (hCtopTarget.prodMk hF3target))))

/-- The raw top-left edge block readout is differentiable in tuple
coordinates. -/
theorem differentiableAt_rawEdgeTupleA1
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') z p) z := by
  cases p using Fin.cases with
  | zero =>
      simpa [rawEdgeTupleA1] using
        differentiableAt_Ctop (ρ := ρ) (κ' := κ') z
  | succ p =>
      simpa [rawEdgeTupleA1] using
        differentiableAt_A1passive (ρ := ρ) (κ' := κ') p z

/-- The raw lower-left edge block readout is differentiable in tuple
coordinates. -/
theorem differentiableAt_rawEdgeTupleA3
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (p : Fin (M + 1)) (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (fun z : TopologyTuple ρ κ' ℝ ↦
        rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') z p) z := by
  induction p using Fin.lastCases with
  | last =>
      simpa [rawEdgeTupleA3] using
        differentiableAt_F3 (ρ := ρ) (κ' := κ') z
  | cast p =>
      simpa [rawEdgeTupleA3] using
        differentiableAt_A3passive (ρ := ρ) (κ' := κ') p z

/-- The full Frechet derivative of the retained-passive raw-order map has the
expected `C` component after the lower-left target shear. -/
theorem fderiv_topologyTupleEdgeRawOrder_C_unshear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).2.2.2.1 p
      + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc =
      v.2.2.2.1 p - coord.solvedA3 p * v.2.1 p := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let raw : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projC : E → Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    fun y ↦ y.2.2.2.1 p
  let projG : E → Matrix (κ' p.succ) ρ ℝ :=
    fun y ↦ rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') y p
  let LC : E →L[ℝ] Matrix (κ' p.succ) (κ' p.castSucc) ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.2.2.1 p
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  let LG : E →L[ℝ] Matrix (κ' p.succ) ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') y p
          map_add' := by
            intro x y
            induction p using Fin.lastCases with
            | last =>
                rw [rawEdgeTupleA3_last, rawEdgeTupleA3_last, rawEdgeTupleA3_last]
                change (x + y).2.2.2.2.2 = x.2.2.2.2.2 + y.2.2.2.2.2
                rfl
            | cast p =>
                rw [rawEdgeTupleA3_castSucc, rawEdgeTupleA3_castSucc, rawEdgeTupleA3_castSucc]
                change (x + y).2.2.1 p = x.2.2.1 p + y.2.2.1 p
                rfl
          map_smul' := by
            intro a y
            induction p using Fin.lastCases with
            | last =>
                rw [rawEdgeTupleA3_last, rawEdgeTupleA3_last]
                change (a • y).2.2.2.2.2 = a • y.2.2.2.2.2
                rfl
            | cast p =>
                rw [rawEdgeTupleA3_castSucc, rawEdgeTupleA3_castSucc]
                change (a • y).2.2.1 p = a • y.2.2.1 p
                rfl }
      cont := continuous_rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') p }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojCDiff : DifferentiableAt ℝ projC (raw z) := by
    change DifferentiableAt ℝ LC (raw z)
    exact LC.differentiableAt
  have hprojGDiff : DifferentiableAt ℝ projG (raw z) := by
    change DifferentiableAt ℝ LG (raw z)
    exact LG.differentiableAt
  have hCcomp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projC) hprojCDiff hrawDiff
  have hGcomp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projG) hprojGDiff hrawDiff
  have hLC : fderiv ℝ projC (raw z) = LC := by
    change fderiv ℝ LC (raw z) = LC
    exact LC.fderiv
  have hLG : fderiv ℝ projG (raw z) = LG := by
    change fderiv ℝ LG (raw z) = LG
    exact LG.fderiv
  have hCproj :
      ((fderiv ℝ raw z) v).2.2.2.1 p =
        (fderiv ℝ (fun y : E ↦ projC (raw y)) z) v := by
    calc
      ((fderiv ℝ raw z) v).2.2.2.1 p
          = LC ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projC (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLC]
            rfl
      _ = (fderiv ℝ (fun y : E ↦ projC (raw y)) z) v := by
            rw [← hCcomp]
  have hGproj :
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p =
        (fderiv ℝ (fun y : E ↦ projG (raw y)) z) v := by
    calc
      rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p
          = LG ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projG (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLG]
            rfl
      _ = (fderiv ℝ (fun y : E ↦ projG (raw y)) z) v := by
            rw [← hGcomp]
  have hcomponent :=
    fderiv_topologyTupleEdgeRawOrder_C_component_unshear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).2.2.2.1 p
      + rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.castSucc =
    v.2.2.2.1 p -
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3 p * v.2.1 p
  rw [hCproj, hGproj]
  simpa [raw, E, projC, projG] using hcomponent

/-- The full Frechet derivative of the retained-passive raw-order map has the
expected `F2` component after the top-left and next-`F2` shear corrections. -/
theorem fderiv_topologyTupleEdgeRawOrder_F2_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        coord.F2 p.castSucc
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
        coord.C p =
      -(coord.solvedA1 p + coord.F2 p.succ * coord.solvedA3 p) * v.2.1 p
        + coord.F2 p.succ * v.2.2.2.1 p := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let raw : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projF2 : E → Matrix ρ (κ' p.castSucc) ℝ :=
    fun y ↦ y.2.1 p
  let projA1 : E → Matrix ρ ρ ℝ :=
    fun y ↦ rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') y p
  let LF2 : E →L[ℝ] Matrix ρ (κ' p.castSucc) ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.1 p
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  let LA1 : E →L[ℝ] Matrix ρ ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') y p
          map_add' := by
            intro x y
            cases p using Fin.cases with
            | zero =>
                rw [rawEdgeTupleA1_zero, rawEdgeTupleA1_zero, rawEdgeTupleA1_zero]
                change (x + y).2.2.2.2.1 = x.2.2.2.2.1 + y.2.2.2.2.1
                rfl
            | succ p =>
                rw [rawEdgeTupleA1_succ, rawEdgeTupleA1_succ, rawEdgeTupleA1_succ]
                change (x + y).1 p = x.1 p + y.1 p
                rfl
          map_smul' := by
            intro a y
            cases p using Fin.cases with
            | zero =>
                rw [rawEdgeTupleA1_zero, rawEdgeTupleA1_zero]
                change (a • y).2.2.2.2.1 = a • y.2.2.2.2.1
                rfl
            | succ p =>
                rw [rawEdgeTupleA1_succ, rawEdgeTupleA1_succ]
                change (a • y).1 p = a • y.1 p
                rfl }
      cont := continuous_rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') p }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojF2Diff : DifferentiableAt ℝ projF2 (raw z) := by
    change DifferentiableAt ℝ LF2 (raw z)
    exact LF2.differentiableAt
  have hprojA1Diff : DifferentiableAt ℝ projA1 (raw z) := by
    change DifferentiableAt ℝ LA1 (raw z)
    exact LA1.differentiableAt
  have hF2comp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projF2) hprojF2Diff hrawDiff
  have hA1comp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projA1) hprojA1Diff hrawDiff
  have hLF2 : fderiv ℝ projF2 (raw z) = LF2 := by
    change fderiv ℝ LF2 (raw z) = LF2
    exact LF2.fderiv
  have hLA1 : fderiv ℝ projA1 (raw z) = LA1 := by
    change fderiv ℝ LA1 (raw z) = LA1
    exact LA1.fderiv
  have hF2proj :
      ((fderiv ℝ raw z) v).2.1 p =
        (fderiv ℝ (fun y : E ↦ projF2 (raw y)) z) v := by
    calc
      ((fderiv ℝ raw z) v).2.1 p
          = LF2 ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projF2 (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLF2]
            rfl
      _ = (fderiv ℝ (fun y : E ↦ projF2 (raw y)) z) v := by
            rw [← hF2comp]
  have hA1proj :
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p =
        (fderiv ℝ (fun y : E ↦ projA1 (raw y)) z) v := by
    calc
      rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p
          = LA1 ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projA1 (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLA1]
            rfl
      _ = (fderiv ℝ (fun y : E ↦ projA1 (raw y)) z) v := by
            rw [← hA1comp]
  have hcomponent :=
    fderiv_topologyTupleEdgeRawOrder_F2_component_shear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).2.1 p
      + rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') ((fderiv ℝ raw z) v) p *
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.castSucc
      - (fderiv ℝ
          (fun y : E ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ) z) v *
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.C p =
      -((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA1 p +
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.succ *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3 p) *
        v.2.1 p +
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2 p.succ *
        v.2.2.2.1 p
  rw [hF2proj, hA1proj]
  simpa [raw, E, projF2, projA1] using hcomponent

set_option maxRecDepth 2048 in
/-- The passive top-left component of the actual raw-order derivative becomes
the identity component after subtracting the next-`F2`/lower-left product
derivative. -/
theorem fderiv_topologyTupleEdgeRawOrder_A1passive_component_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).1 p) z) v
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      v.1 p := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let Afun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA1
      p.succ
  let Hfun : TopologyTuple ρ κ' ℝ → Matrix ρ (κ' p.succ.succ) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
      p.succ.succ
  let Gfun : TopologyTuple ρ κ' ℝ → Matrix (κ' p.succ.succ) ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
      p.succ
  let BHG : Matrix ρ (κ' p.succ.succ) ℝ →L[ℝ]
      Matrix (κ' p.succ.succ) ρ ℝ →L[ℝ]
        Matrix ρ ρ ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := κ' p.succ.succ) (n := ρ)
  have hAdiff : DifferentiableAt ℝ Afun z := by
    simpa [Afun] using
      differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
  have hHdiff : DifferentiableAt ℝ Hfun z := by
    simpa [Hfun, toCoordinateData] using
      differentiableAt_F2full (ρ := ρ) (κ' := κ') p.succ.succ z
  have hGdiff : DifferentiableAt ℝ Gfun z := by
    simpa [Gfun] using
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') p.succ z hz
  have hrawA :
      (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).1 p) =
        fun y ↦ Afun y + Hfun y * Gfun y := by
    funext y
    simp [raw, Afun, Hfun, Gfun, toCoordinateData]
  have hHGDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z =
        BHG.precompR _ (Hfun z) (fderiv ℝ Gfun z) +
          BHG.precompL _ (fderiv ℝ Hfun z) (Gfun z) := by
    simpa [BHG] using
      (BHG.hasFDerivAt_of_bilinear hHdiff.hasFDerivAt hGdiff.hasFDerivAt).fderiv
  have hAfun :
      Afun = fun y : TopologyTuple ρ κ' ℝ ↦ y.1 p := by
    funext y
    change
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
          p.succ =
        y.1 p
    rw [RetainedPassiveCoordinateData.solvedA1]
    rw [retainedPassiveSolvedA1_eq_of_ne_zero
      (K := ℝ) (ρ := ρ)
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).A1seed
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).Ctop
      (Fin.succ_ne_zero p)]
    change (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1passive p = y.1 p
    rfl
  have hA_apply : (fderiv ℝ Afun z) v = v.1 p := by
    let LA : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.1 p
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLA :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.1 p) z = LA :=
      LA.fderiv
    rw [hAfun, hLA]
    rfl
  calc
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).1 p) z) v
        - (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                p.succ.succ) z) v *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3
              p.succ
        - (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2
            p.succ.succ *
            (fderiv ℝ
              (fun y : TopologyTuple ρ κ' ℝ ↦
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                  p.succ) z) v
      =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Afun y + Hfun y * Gfun y) z) v
          - (fderiv ℝ Hfun z) v * Gfun z
          - Hfun z * (fderiv ℝ Gfun z) v := by
          rw [hrawA]
    _ =
        ((fderiv ℝ Afun z) v +
          (Hfun z * (fderiv ℝ Gfun z) v + (fderiv ℝ Hfun z) v * Gfun z))
          - (fderiv ℝ Hfun z) v * Gfun z
          - Hfun z * (fderiv ℝ Gfun z) v := by
          rw [fderiv_fun_add hAdiff (differentiableAt_matrix_mul hHdiff hGdiff)]
          rw [hHGDeriv]
          simp [BHG, matrixMulContinuousLinearMap_apply]
    _ = (fderiv ℝ Afun z) v := by
          abel
    _ = v.1 p := hA_apply

/-- The full Frechet derivative of the retained-passive raw-order map has the
expected passive top-left component after the next-`F2`/lower-left product
corrections. -/
theorem fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).1 p
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          coord.solvedA3 p.succ
      - coord.F2 p.succ.succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      v.1 p := by
  let raw : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projA1 : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ := fun y ↦ y.1 p
  let LA1 : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.1 p
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojA1Diff : DifferentiableAt ℝ projA1 (raw z) := by
    change DifferentiableAt ℝ LA1 (raw z)
    exact LA1.differentiableAt
  have hA1comp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projA1) hprojA1Diff hrawDiff
  have hLA1 : fderiv ℝ projA1 (raw z) = LA1 := by
    change fderiv ℝ LA1 (raw z) = LA1
    exact LA1.fderiv
  have hA1proj :
      ((fderiv ℝ raw z) v).1 p =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projA1 (raw y)) z) v := by
    calc
      ((fderiv ℝ raw z) v).1 p
          = LA1 ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projA1 (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLA1]
            rfl
      _ = (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projA1 (raw y)) z) v := by
            rw [← hA1comp]
  have hcomponent :=
    fderiv_topologyTupleEdgeRawOrder_A1passive_component_shear_apply
      (ρ := ρ) (κ' := κ') hz v p
  change ((fderiv ℝ raw z) v).1 p
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              p.succ.succ) z) v *
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3
            p.succ
      - (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2
          p.succ.succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                p.succ) z) v =
      v.1 p
  rw [hA1proj]
  simpa [raw, projA1] using hcomponent

set_option maxRecDepth 2048 in
/-- The first top-left raw-order component becomes the formal `Ctop`
component after subtracting the successor-`F2`/lower-left product derivative
and the passive-tail inverse correction. -/
theorem fderiv_topologyTupleEdgeRawOrder_Ctop_component_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tail := retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ) data.A1seed
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.1) z) v
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          coord.Ctop =
      Tail⁻¹ * v.2.2.2.2.1 := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
  let Tfun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed
  let Ufun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ := fun y ↦ (Tfun y)⁻¹
  let Cfun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.Ctop
  let Hfun : TopologyTuple ρ κ' ℝ → Matrix ρ (κ' (0 : Fin (M + 1)).succ) ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
      (0 : Fin (M + 1)).succ
  let Gfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (0 : Fin (M + 1)).succ) ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
      0
  let BUC : Matrix ρ ρ ℝ →L[ℝ]
      Matrix ρ ρ ℝ →L[ℝ]
        Matrix ρ ρ ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := ρ) (n := ρ)
  let BHG : Matrix ρ (κ' (0 : Fin (M + 1)).succ) ℝ →L[ℝ]
      Matrix (κ' (0 : Fin (M + 1)).succ) ρ ℝ →L[ℝ]
        Matrix ρ ρ ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := κ' (0 : Fin (M + 1)).succ) (n := ρ)
  have hTdiff : DifferentiableAt ℝ Tfun z := by
    simpa [Tfun] using
      differentiableAt_retainedPassiveA1TailAfterFirst
        (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart := by
    exact hz
  have hTailUnit : IsUnit (Tfun z).det := by
    change IsUnit
      (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ) data.A1seed).det
    exact
      retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
        (K := ℝ) (ρ := ρ) data.A1seed
        (data.toCoordinateData_passiveA1_units hdet.2)
  have hUdiff : DifferentiableAt ℝ Ufun z := by
    exact
      (differentiableAt_matrix_inv_of_isUnit_det (Tfun z) hTailUnit).comp z hTdiff
  have hCdiff : DifferentiableAt ℝ Cfun z := by
    simpa [Cfun, toCoordinateData] using
      differentiableAt_Ctop (ρ := ρ) (κ' := κ') z
  have hHdiff : DifferentiableAt ℝ Hfun z := by
    simpa [Hfun, toCoordinateData] using
      differentiableAt_F2full (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)).succ z
  have hGdiff : DifferentiableAt ℝ Gfun z := by
    simpa [Gfun] using
      differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (0 : Fin (M + 1)) z hz
  have hrawCtop :
      (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.1) =
        fun y ↦ Ufun y * Cfun y + Hfun y * Gfun y := by
    funext y
    rw [topologyTupleEdgeRawOrder_Ctop]
    simp [Ufun, Tfun, Cfun, Hfun, Gfun,
      RetainedPassiveCoordinateData.solvedA1, toCoordinateData]
  have hUCDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Ufun y * Cfun y) z =
        BUC.precompR _ (Ufun z) (fderiv ℝ Cfun z) +
          BUC.precompL _ (fderiv ℝ Ufun z) (Cfun z) := by
    simpa [BUC] using
      (BUC.hasFDerivAt_of_bilinear hUdiff.hasFDerivAt hCdiff.hasFDerivAt).fderiv
  have hHGDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z =
        BHG.precompR _ (Hfun z) (fderiv ℝ Gfun z) +
          BHG.precompL _ (fderiv ℝ Hfun z) (Gfun z) := by
    simpa [BHG] using
      (BHG.hasFDerivAt_of_bilinear hHdiff.hasFDerivAt hGdiff.hasFDerivAt).fderiv
  have hCtop_apply : (fderiv ℝ Cfun z) v = v.2.2.2.2.1 := by
    let LCtop : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.2.2.2.1
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLCtop :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.2.1) z = LCtop :=
      LCtop.fderiv
    change (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.2.1) z) v =
      v.2.2.2.2.1
    rw [hLCtop]
    rfl
  let dU : Matrix ρ ρ ℝ := (fderiv ℝ Ufun z) v
  let dCtop : Matrix ρ ρ ℝ := (fderiv ℝ Cfun z) v
  let dH : Matrix ρ (κ' (0 : Fin (M + 1)).succ) ℝ := (fderiv ℝ Hfun z) v
  let dG : Matrix (κ' (0 : Fin (M + 1)).succ) ρ ℝ := (fderiv ℝ Gfun z) v
  have hUC_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Ufun y * Cfun y) z) v =
        Ufun z * dCtop + dU * Cfun z := by
    simpa [dU, dCtop, BUC, matrixMulContinuousLinearMap_apply] using
      congrArg (fun L : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ ↦ L v) hUCDeriv
  have hHG_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z) v =
        Hfun z * dG + dH * Gfun z := by
    simpa [dH, dG, BHG, matrixMulContinuousLinearMap_apply] using
      congrArg (fun L :
          TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ ↦ L v) hHGDeriv
  calc
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.1) z) v
        - (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
                (0 : Fin (M + 1)).succ) z) v *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3
              0
        - (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2
            (0 : Fin (M + 1)).succ *
            (fderiv ℝ
              (fun y : TopologyTuple ρ κ' ℝ ↦
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                  0) z) v
        - (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.Ctop
      =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          Ufun y * Cfun y + Hfun y * Gfun y) z) v
          - (fderiv ℝ Hfun z) v * Gfun z
          - Hfun z * (fderiv ℝ Gfun z) v
          - (fderiv ℝ Ufun z) v * Cfun z := by
          rw [hrawCtop]
    _ =
        ((fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Ufun y * Cfun y) z) v +
          (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Hfun y * Gfun y) z) v)
          - (fderiv ℝ Hfun z) v * Gfun z
          - Hfun z * (fderiv ℝ Gfun z) v
          - (fderiv ℝ Ufun z) v * Cfun z := by
          rw [fderiv_fun_add (differentiableAt_matrix_mul hUdiff hCdiff)
            (differentiableAt_matrix_mul hHdiff hGdiff)]
          simp
    _ =
        (Ufun z * dCtop + dU * Cfun z + (Hfun z * dG + dH * Gfun z))
          - dH * Gfun z - Hfun z * dG - dU * Cfun z := by
          rw [hUC_apply, hHG_apply]
    _ = Ufun z * dCtop := by
          abel
    _ =
        (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹ *
          v.2.2.2.2.1 := by
          simp [Ufun, Tfun, dCtop, hCtop_apply]

/-- The full Frechet derivative of the retained-passive raw-order map has the
expected `Ctop` component after the successor-`F2`/lower-left product and
passive-tail inverse corrections. -/
theorem fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    let Tail := retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ) data.A1seed
    ((fderiv ℝ raw z) v).2.2.2.2.1
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          coord.solvedA3 0
      - coord.F2 (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          coord.Ctop =
      Tail⁻¹ * v.2.2.2.2.1 := by
  let raw : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projCtop : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ := fun y ↦ y.2.2.2.2.1
  let LCtop : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix ρ ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.2.2.2.1
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojCtopDiff : DifferentiableAt ℝ projCtop (raw z) := by
    change DifferentiableAt ℝ LCtop (raw z)
    exact LCtop.differentiableAt
  have hCtopComp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projCtop)
      hprojCtopDiff hrawDiff
  have hLCtop : fderiv ℝ projCtop (raw z) = LCtop := by
    change fderiv ℝ LCtop (raw z) = LCtop
    exact LCtop.fderiv
  have hCtopProj :
      ((fderiv ℝ raw z) v).2.2.2.2.1 =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projCtop (raw y)) z) v := by
    calc
      ((fderiv ℝ raw z) v).2.2.2.2.1
          = LCtop ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projCtop (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLCtop]
            rfl
      _ = (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projCtop (raw y)) z) v := by
            rw [← hCtopComp]
  have hcomponent :=
    fderiv_topologyTupleEdgeRawOrder_Ctop_component_shear_apply
      (ρ := ρ) (κ' := κ') hz v
  change ((fderiv ℝ raw z) v).2.2.2.2.1
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.F2
              (0 : Fin (M + 1)).succ) z) v *
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.solvedA3
            0
      - (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F2
          (0 : Fin (M + 1)).succ *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData.solvedA3
                0) z) v
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A1seed)⁻¹) z) v *
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.Ctop =
      (retainedPassiveA1TailAfterFirst (K := ℝ) (ρ := ρ)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A1seed)⁻¹ *
        v.2.2.2.2.1
  rw [hCtopProj]
  simpa [raw, projCtop] using hcomponent

/-- The passive lower-left raw-order component has identity derivative.

This is only for nonterminal passive indices `p : Fin M`; the terminal
lower-left coordinate is the solved `F3` endpoint and is not covered here. -/
theorem fderiv_topologyTupleEdgeRawOrder_A3passive_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) (p : Fin M) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    ((fderiv ℝ raw z) v).2.2.1 p = v.2.2.1 p := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let raw : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projA3 : E → Matrix (κ' p.castSucc.succ) ρ ℝ :=
    fun y ↦ y.2.2.1 p
  let LA3 : E →L[ℝ] Matrix (κ' p.castSucc.succ) ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.2.1 p
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojDiff : DifferentiableAt ℝ projA3 (raw z) := by
    change DifferentiableAt ℝ LA3 (raw z)
    exact LA3.differentiableAt
  have hcomp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projA3) hprojDiff hrawDiff
  have hLA3 : fderiv ℝ projA3 (raw z) = LA3 := by
    change fderiv ℝ LA3 (raw z) = LA3
    exact LA3.fderiv
  have hLA3_id : fderiv ℝ (fun y : E ↦ y.2.2.1 p) z = LA3 := by
    change fderiv ℝ LA3 z = LA3
    exact LA3.fderiv
  have hcomponent :
      (fun y : E ↦ projA3 (raw y)) = fun y ↦ y.2.2.1 p := by
    funext y
    change (raw y).2.2.1 p = y.2.2.1 p
    rw [topologyTupleEdgeRawOrder_A3passive]
    change
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA3
          p.castSucc =
        y.2.2.1 p
    have hsolve :=
      retainedPassiveSolvedA3_eq_of_ne_last
        (K := ℝ) (ρ := ρ) (κ' := κ')
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).F3
        (Fin.castSucc_ne_last p)
    simpa [RetainedPassiveCoordinateData.solvedA3, toCoordinateData] using hsolve
  calc
    ((fderiv ℝ raw z) v).2.2.1 p
        = LA3 ((fderiv ℝ raw z) v) := rfl
    _ = ((fderiv ℝ projA3 (raw z)).comp (fderiv ℝ raw z)) v := by
          rw [hLA3]
          rfl
    _ = (fderiv ℝ (fun y : E ↦ projA3 (raw y)) z) v := by
          rw [← hcomp]
    _ = (fderiv ℝ (fun y : E ↦ y.2.2.1 p) z) v := by
          rw [hcomponent]
    _ = LA3 v := by
          rw [hLA3_id]
    _ = v.2.2.1 p := rfl

set_option maxRecDepth 2048 in
/-- The terminal lower-left raw-order component becomes the formal `F3`
component after subtracting the earlier-tail derivative and adding the
terminal top-factor derivative correction. -/
theorem fderiv_topologyTupleEdgeRawOrder_F3_component_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let Earlyfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          0 (Nat.zero_le (M + 1))
    let Lastfun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.2) z) v
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      v.2.2.2.2.2 * (-(Lastfun z)) := by
  let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
    fun y p ↦
      ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
  let Earlyfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦
      retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
        (A1fun y)
        (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
        0 (Nat.zero_le (M + 1))
  let Lastfun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
    fun y ↦
      residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
  let F3fun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).F3
  let Dfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ F3fun y - Earlyfun y
  let BFL : Matrix (κ' (Fin.last (M + 1))) ρ ℝ →L[ℝ]
      Matrix ρ ρ ℝ →L[ℝ]
        Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    matrixMulContinuousLinearMap (l := κ' (Fin.last (M + 1))) (m := ρ) (n := ρ)
  have hF3diff : DifferentiableAt ℝ F3fun z := by
    simpa [F3fun] using
      differentiableAt_F3 (ρ := ρ) (κ' := κ') z
  have hEdiff : DifferentiableAt ℝ Earlyfun z := by
    simpa [A1fun, Earlyfun] using
      differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') 0 (Nat.zero_le (M + 1)) z hz
  have hLdiff : DifferentiableAt ℝ Lastfun z := by
    simpa [A1fun, Lastfun] using
      differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') (Fin.last M).castSucc
        (Fin.last M).castSucc.le_last z hz
  have hrawF3 :
      (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.2) =
        fun y ↦ -(Dfun y * Lastfun y) := by
    funext y
    rw [topologyTupleEdgeRawOrder_F3]
    change
      retainedPassiveSolvedA3 (K := ℝ) (ρ := ρ) (κ' := κ')
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).F3
          (Fin.last M) =
        -(Dfun y * Lastfun y)
    rw [retainedPassiveSolvedA3_last]
    have hA1eta :
        (fun p : Fin (M + 1) ↦
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p) =
          ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 := by
      funext p
      rfl
    rw [Matrix.neg_mul]
  have hDdiff : DifferentiableAt ℝ Dfun z := by
    simpa [Dfun] using hF3diff.sub hEdiff
  have hFLDeriv :
      fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Dfun y * Lastfun y) z =
        BFL.precompR _ (Dfun z) (fderiv ℝ Lastfun z) +
          BFL.precompL _ (fderiv ℝ Dfun z) (Lastfun z) := by
    simpa [BFL] using
      (BFL.hasFDerivAt_of_bilinear hDdiff.hasFDerivAt hLdiff.hasFDerivAt).fderiv
  have hF3_apply : (fderiv ℝ F3fun z) v = v.2.2.2.2.2 := by
    let LF3 : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      { toLinearMap :=
          { toFun := fun y ↦ y.2.2.2.2.2
            map_add' := by
              intro x y
              rfl
            map_smul' := by
              intro a y
              rfl }
        cont := by fun_prop }
    have hLF3 :
        fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.2.2) z = LF3 :=
      LF3.fderiv
    change (fderiv ℝ
        (fun y : TopologyTuple ρ κ' ℝ ↦ y.2.2.2.2.2) z) v =
      v.2.2.2.2.2
    rw [hLF3]
    rfl
  let dF3 : Matrix (κ' (Fin.last (M + 1))) ρ ℝ := (fderiv ℝ F3fun z) v
  let dE : Matrix (κ' (Fin.last (M + 1))) ρ ℝ := (fderiv ℝ Earlyfun z) v
  let dL : Matrix ρ ρ ℝ := (fderiv ℝ Lastfun z) v
  have hD_apply :
      (fderiv ℝ Dfun z) v =
        dF3 - dE := by
    change (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ F3fun y - Earlyfun y) z) v =
      dF3 - dE
    rw [fderiv_fun_sub hF3diff hEdiff]
    rfl
  have hFL_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ Dfun y * Lastfun y) z) v =
        Dfun z * dL + (dF3 * Lastfun z - dE * Lastfun z) := by
    simpa [dF3, dE, dL, BFL, matrixMulContinuousLinearMap_apply, hD_apply] using
      congrArg
        (fun L : TopologyTuple ρ κ' ℝ →L[ℝ]
          Matrix (κ' (Fin.last (M + 1))) ρ ℝ ↦ L v)
        hFLDeriv
  have hraw_apply :
      (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          -(Dfun y * Lastfun y)) z) v =
        -(Dfun z * dL + (dF3 * Lastfun z - dE * Lastfun z)) := by
    rw [fderiv_fun_neg]
    simp [hFL_apply]
  have hcancel :
      -(Dfun z * dL + (dF3 * Lastfun z - dE * Lastfun z))
        - dE * Lastfun z + Dfun z * dL =
      dF3 * (-(Lastfun z)) := by
    rw [Matrix.mul_neg]
    ext i j
    simp [sub_eq_add_neg, Matrix.mul_apply]
    abel_nf
  calc
    (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ (raw y).2.2.2.2.2) z) v
        - (fderiv ℝ Earlyfun z) v * Lastfun z
        + (((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).F3 -
            Earlyfun z) * (fderiv ℝ Lastfun z) v
      =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦
          -(Dfun y * Lastfun y)) z) v
          - (fderiv ℝ Earlyfun z) v * Lastfun z
          + Dfun z * (fderiv ℝ Lastfun z) v := by
          rw [hrawF3]
          rfl
    _ =
        -(Dfun z * dL + (dF3 * Lastfun z - dE * Lastfun z))
          - dE * Lastfun z + Dfun z * dL := by
          rw [hraw_apply]
    _ = dF3 * (-(Lastfun z)) := hcancel
    _ = v.2.2.2.2.2 * (-(Lastfun z)) := by
          simp [dF3, hF3_apply]

/-- The full Frechet derivative of the retained-passive raw-order map has the
expected terminal `F3` component after the earlier-tail and terminal-top-factor
corrections. -/
theorem fderiv_topologyTupleEdgeRawOrder_F3_shear_apply
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) :
    let raw := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
    let A1fun : TopologyTuple ρ κ' ℝ → Fin (M + 1) → Matrix ρ ρ ℝ :=
      fun y p ↦
        ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p
    let Earlyfun : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
      fun y ↦
        retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
          (A1fun y)
          (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
          0 (Nat.zero_le (M + 1))
    let Lastfun : TopologyTuple ρ κ' ℝ → Matrix ρ ρ ℝ :=
      fun y ↦
        residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (A1fun y) (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
    let data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z
    let coord := data.toCoordinateData
    ((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ Earlyfun z) v * Lastfun z
      + (coord.F3 - Earlyfun z) * (fderiv ℝ Lastfun z) v =
      v.2.2.2.2.2 * (-(Lastfun z)) := by
  let raw : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let projF3 : TopologyTuple ρ κ' ℝ → Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    fun y ↦ y.2.2.2.2.2
  let LF3 : TopologyTuple ρ κ' ℝ →L[ℝ] Matrix (κ' (Fin.last (M + 1))) ρ ℝ :=
    { toLinearMap :=
        { toFun := fun y ↦ y.2.2.2.2.2
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a y
            rfl }
      cont := by fun_prop }
  have hrawDiff : DifferentiableAt ℝ raw z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hprojF3Diff : DifferentiableAt ℝ projF3 (raw z) := by
    change DifferentiableAt ℝ LF3 (raw z)
    exact LF3.differentiableAt
  have hF3comp :=
    fderiv_comp' (𝕜 := ℝ) (x := z) (f := raw) (g := projF3)
      hprojF3Diff hrawDiff
  have hLF3 : fderiv ℝ projF3 (raw z) = LF3 := by
    change fderiv ℝ LF3 (raw z) = LF3
    exact LF3.fderiv
  have hF3proj :
      ((fderiv ℝ raw z) v).2.2.2.2.2 =
        (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projF3 (raw y)) z) v := by
    calc
      ((fderiv ℝ raw z) v).2.2.2.2.2
          = LF3 ((fderiv ℝ raw z) v) := rfl
      _ = ((fderiv ℝ projF3 (raw z)).comp (fderiv ℝ raw z)) v := by
            rw [hLF3]
            rfl
      _ = (fderiv ℝ (fun y : TopologyTuple ρ κ' ℝ ↦ projF3 (raw y)) z) v := by
            rw [← hF3comp]
  have hcomponent :=
    fderiv_topologyTupleEdgeRawOrder_F3_component_shear_apply
      (ρ := ρ) (κ' := κ') hz v
  change ((fderiv ℝ raw z) v).2.2.2.2.2
      - (fderiv ℝ
          (fun y : TopologyTuple ρ κ' ℝ ↦
            retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
              (fun p : Fin (M + 1) ↦
                ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p)
              (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
                (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).A3seed)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).C
              0 (Nat.zero_le (M + 1))) z) v *
          (residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (Fin.last (M + 1)) (Fin.last M).castSucc
              (Fin.last M).castSucc.le_last)
      + ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData.F3 -
          retainedPassiveLowerLeftProductTailSum (K := ℝ) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦
              ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
            (retainedPassiveA3WithoutLast (K := ℝ) (ρ := ρ)
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).A3seed)
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            0 (Nat.zero_le (M + 1))) *
          (fderiv ℝ
            (fun y : TopologyTuple ρ κ' ℝ ↦
              residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦
                  ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') y).toCoordinateData).solvedA1 p)
                (Fin.last (M + 1)) (Fin.last M).castSucc
                  (Fin.last M).castSucc.le_last) z) v =
      v.2.2.2.2.2 *
        (-(residualFactorProduct (K := ℝ) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦
            ((ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last))
  rw [hF3proj]
  simpa [raw, projF3] using hcomponent

/-- Reassembling raw-order tuple coordinates into an edge family is
differentiable. -/
theorem differentiableAt_edgeFamilyOfRawOrderTuple
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Finite ρ] [∀ j, Finite (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) :
    DifferentiableAt ℝ
      (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') :
        TopologyTuple ρ κ' ℝ → EdgeFamilyTuple ρ κ' ℝ) z := by
  let _ : Fintype ρ := Fintype.ofFinite ρ
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  rw [differentiableAt_pi]
  intro p
  have hA1 :
      DifferentiableAt ℝ
        (fun z : TopologyTuple ρ κ' ℝ ↦
          rawEdgeTupleA1 (K := ℝ) (ρ := ρ) (κ' := κ') z p) z :=
    differentiableAt_rawEdgeTupleA1 (ρ := ρ) (κ' := κ') p z
  have hF2 :
      DifferentiableAt ℝ
        (fun z : TopologyTuple ρ κ' ℝ ↦
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).F2 p) z :=
    differentiableAt_F2 (ρ := ρ) (κ' := κ') p z
  have hA3 :
      DifferentiableAt ℝ
        (fun z : TopologyTuple ρ κ' ℝ ↦
          rawEdgeTupleA3 (K := ℝ) (ρ := ρ) (κ' := κ') z p) z :=
    differentiableAt_rawEdgeTupleA3 (ρ := ρ) (κ' := κ') p z
  have hC :
      DifferentiableAt ℝ
        (fun z : TopologyTuple ρ κ' ℝ ↦
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C p) z :=
    differentiableAt_C (ρ := ρ) (κ' := κ') p z
  simpa [edgeFamilyOfRawOrderTuple] using
    differentiableAt_matrix_fromBlocks hA1 hF2 hA3 hC

/-- Source readback, followed by conversion to tuple coordinates, is
differentiable along differentiable source edge-family curves in the recursive
determinant chart. -/
theorem differentiableAt_topologyTuple_sourceReadback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {x₀ : E}
    (F : E → EdgeFamilyTuple ρ κ' ℝ)
    (hF : DifferentiableAt ℝ F x₀)
    (hchart : sourceRecursiveDetChart (K := ℝ) (ρ := ρ) (F x₀)) :
    DifferentiableAt ℝ
      (fun x : E ↦ topologyTuple (sourceReadback (K := ℝ) (ρ := ρ) (F x))) x₀ := by
  have hchartTransformed :
      ∀ p : Fin (M + 1),
        identityCornerDetChart
          (sourceReadbackTransformedEdge (K := ℝ) (ρ := ρ) (F x₀) p) :=
    (sourceRecursiveDetChart_iff (K := ℝ) (ρ := ρ) (F x₀)).1 hchart
  have hA1passive :
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadback (K := ℝ) (ρ := ρ) (F x)).A1passive) x₀ := by
    rw [differentiableAt_pi]
    intro p
    have hT :=
      differentiableAt_sourceReadbackTransformedEdge
        (ρ := ρ) (κ' := κ') F hF hchart p.succ
    simpa [sourceReadback] using differentiableAt_topLeftCorner hT
  have hF2 :
      DifferentiableAt ℝ
        (fun x : E ↦ (sourceReadback (K := ℝ) (ρ := ρ) (F x)).F2) x₀ := by
    rw [differentiableAt_pi]
    intro p
    let T : E → Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) ℝ :=
      fun x ↦ sourceReadbackTransformedEdge (K := ℝ) (ρ := ρ) (F x) p
    have hT : DifferentiableAt ℝ T x₀ :=
      differentiableAt_sourceReadbackTransformedEdge
        (ρ := ρ) (κ' := κ') F hF hchart p
    have htop : DifferentiableAt ℝ (fun x : E ↦ topLeftCorner (T x)) x₀ :=
      differentiableAt_topLeftCorner hT
    have htopUnit : IsUnit ((topLeftCorner (T x₀)).det) := by
      have hchartp := hchartTransformed p
      simpa only [identityCornerDetChart, T] using hchartp
    have htopInv :
        DifferentiableAt ℝ (fun x : E ↦ (topLeftCorner (T x))⁻¹) x₀ :=
      (differentiableAt_matrix_inv_of_isUnit_det (topLeftCorner (T x₀)) htopUnit).comp
        x₀ htop
    have hupper : DifferentiableAt ℝ (fun x : E ↦ upperRightBlock (T x)) x₀ :=
      differentiableAt_upperRightBlock hT
    have hbody :
        DifferentiableAt ℝ
          (fun x : E ↦ (topLeftCorner (T x))⁻¹ * upperRightBlock (T x)) x₀ :=
      differentiableAt_matrix_mul htopInv hupper
    simpa [sourceReadback, T] using hbody.neg
  have hA3passive :
      DifferentiableAt ℝ
        (fun x : E ↦
          (sourceReadback (K := ℝ) (ρ := ρ) (F x)).A3passive) x₀ := by
    rw [differentiableAt_pi]
    intro p
    have hT :=
      differentiableAt_sourceReadbackTransformedEdge
        (ρ := ρ) (κ' := κ') F hF hchart p.castSucc
    simpa [sourceReadback] using differentiableAt_lowerLeftBlock hT
  have hC :
      DifferentiableAt ℝ
        (fun x : E ↦ (sourceReadback (K := ℝ) (ρ := ρ) (F x)).C) x₀ := by
    rw [differentiableAt_pi]
    intro p
    let T : E → Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) ℝ :=
      fun x ↦ sourceReadbackTransformedEdge (K := ℝ) (ρ := ρ) (F x) p
    have hT : DifferentiableAt ℝ T x₀ :=
      differentiableAt_sourceReadbackTransformedEdge
        (ρ := ρ) (κ' := κ') F hF hchart p
    have htopUnit : IsUnit ((topLeftCorner (T x₀)).det) := by
      have hchartp := hchartTransformed p
      simpa only [identityCornerDetChart, T] using hchartp
    have hschur : DifferentiableAt ℝ (fun x : E ↦ schurResidualBlock (T x)) x₀ :=
      differentiableAt_schurResidualBlock hT htopUnit
    simpa [sourceReadback, T] using hschur
  have hfields0 :=
    differentiableAt_sourceReadbackSuffixState_fields
      (ρ := ρ) (κ' := κ') F hF hchart 0
      (Fin.zero_le (Fin.last (M + 1)))
  rcases hfields0 with ⟨_, hL0, _hB0, hCtop0, _hD0⟩
  have hCtop :
      DifferentiableAt ℝ
        (fun x : E ↦ (sourceReadback (K := ℝ) (ρ := ρ) (F x)).Ctop) x₀ := by
    simpa [sourceReadback, sourceReadbackSuffixState] using hCtop0
  have hF3 :
      DifferentiableAt ℝ
        (fun x : E ↦ (sourceReadback (K := ℝ) (ρ := ρ) (F x)).F3) x₀ := by
    have hLower :=
      differentiableAt_lowerLeftBlock
        (ρ := ρ) (μ := κ' (Fin.last (M + 1))) (ν := κ' (Fin.last (M + 1))) hL0
    simpa [sourceReadback, sourceReadbackSuffixState] using hLower
  change DifferentiableAt ℝ
    (fun x : E ↦
      ((sourceReadback (K := ℝ) (ρ := ρ) (F x)).A1passive,
        ((sourceReadback (K := ℝ) (ρ := ρ) (F x)).F2,
          ((sourceReadback (K := ℝ) (ρ := ρ) (F x)).A3passive,
            ((sourceReadback (K := ℝ) (ρ := ρ) (F x)).C,
              ((sourceReadback (K := ℝ) (ρ := ρ) (F x)).Ctop,
                (sourceReadback (K := ℝ) (ρ := ρ) (F x)).F3)))))) x₀
  exact
    hA1passive.prodMk
      (hF2.prodMk
        (hA3passive.prodMk
          (hC.prodMk
            (hCtop.prodMk hF3))))

/-- The raw-order source-readback inverse is differentiable at every point of
the raw-order source-recursive determinant chart. -/
theorem differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    DifferentiableAt ℝ
      (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')) z := by
  let F : TopologyTuple ρ κ' ℝ → EdgeFamilyTuple ρ κ' ℝ :=
    edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
  have hF : DifferentiableAt ℝ F z :=
    differentiableAt_edgeFamilyOfRawOrderTuple (ρ := ρ) (κ' := κ') z
  have hsource :
      F z ∈ sourceRecursiveDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    simpa [topologyTupleRawOrderSourceRecursiveDetChartSet, F] using hz
  have hchart : sourceRecursiveDetChart (K := ℝ) (ρ := ρ) (F z) :=
    (mem_sourceRecursiveDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') (F z)).1 hsource
  have hread :=
    differentiableAt_topologyTuple_sourceReadback
      (ρ := ρ) (κ' := κ') F hF hchart
  simpa [topologyTupleEdgeRawOrderInverse, F] using hread

/-- The derivative of raw-order readback composed with the derivative of the
forward raw-order map is the identity on tangent coordinates. -/
theorem fderiv_topologyTupleEdgeRawOrderInverse_comp_fderiv_topologyTupleEdgeRawOrder
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    (fderiv ℝ
        (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ'))
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)).comp
      (fderiv ℝ
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z) =
    ContinuousLinearMap.id ℝ (TopologyTuple ρ κ' ℝ) := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let f : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let g : E → E := topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
  have hf : DifferentiableAt ℝ f z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hy : f z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') :=
    mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') hz
  have hg : DifferentiableAt ℝ g (f z) :=
    differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
      (ρ := ρ) (κ' := κ') hy
  have hS : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ∈ 𝓝 z :=
    (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hz
  have hgf : (fun x : E ↦ g (f x)) =ᶠ[𝓝 z] id := by
    filter_upwards [hS] with x hx
    exact
      topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') hx
  calc
    (fderiv ℝ g (f z)).comp (fderiv ℝ f z)
        = fderiv ℝ (fun x : E ↦ g (f x)) z := by
          exact (fderiv_comp' (𝕜 := ℝ) (x := z) (f := f) (g := g) hg hf).symm
    _ = fderiv ℝ id z := hgf.fderiv_eq
    _ = ContinuousLinearMap.id ℝ E := fderiv_id

/-- The derivative of the forward raw-order map composed with the derivative
of raw-order readback is the identity on target tangent coordinates. -/
theorem fderiv_topologyTupleEdgeRawOrder_comp_fderiv_topologyTupleEdgeRawOrderInverse
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    (fderiv ℝ
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z).comp
      (fderiv ℝ
        (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ'))
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
    ContinuousLinearMap.id ℝ (TopologyTuple ρ κ' ℝ) := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let f : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let g : E → E := topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
  have hf : DifferentiableAt ℝ f z :=
    differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z hz
  have hy : f z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') :=
    mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') hz
  have hg : DifferentiableAt ℝ g (f z) :=
    differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
      (ρ := ρ) (κ' := κ') hy
  have hgz : g (f z) = z :=
    topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
      (K := ℝ) (ρ := ρ) (κ' := κ') hz
  have hT : topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') ∈ 𝓝 (f z) :=
    (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hy
  have hfg : (fun y : E ↦ f (g y)) =ᶠ[𝓝 (f z)] id := by
    filter_upwards [hT] with y hy'
    exact
      topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
        (K := ℝ) (ρ := ρ) (κ' := κ') hy'
  calc
    (fderiv ℝ f z).comp (fderiv ℝ g (f z))
        = (fderiv ℝ f (g (f z))).comp (fderiv ℝ g (f z)) := by
          rw [hgz]
    _ = fderiv ℝ (fun y : E ↦ f (g y)) (f z) := by
          have hf' : DifferentiableAt ℝ f (g (f z)) := by
            simpa [hgz] using hf
          exact (fderiv_comp' (𝕜 := ℝ) (x := f z) (f := g) (g := f) hf' hg).symm
    _ = fderiv ℝ id (f z) := hfg.fderiv_eq
    _ = ContinuousLinearMap.id ℝ E := fderiv_id

/-- The ambient Frechet derivative of the retained-passive raw-order chart map
has unit determinant on the tuple determinant chart. -/
theorem fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    IsUnit
      (LinearMap.det
        ((fderiv ℝ
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z :
            TopologyTuple ρ κ' ℝ →L[ℝ] TopologyTuple ρ κ' ℝ) :
          TopologyTuple ρ κ' ℝ →ₗ[ℝ] TopologyTuple ρ κ' ℝ)) := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let f : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let g : E → E := topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
  have hcomp :
      (fderiv ℝ g (f z)).comp (fderiv ℝ f z) = ContinuousLinearMap.id ℝ E := by
    simpa [E, f, g] using
      fderiv_topologyTupleEdgeRawOrderInverse_comp_fderiv_topologyTupleEdgeRawOrder
        (ρ := ρ) (κ' := κ') hz
  have hcompLinear :
      (((fderiv ℝ g (f z)).comp (fderiv ℝ f z) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        (LinearMap.id : E →ₗ[ℝ] E) :=
    congrArg (fun L : E →L[ℝ] E ↦ (L : E →ₗ[ℝ] E)) hcomp
  have hmul :
      LinearMap.det ((fderiv ℝ g (f z) : E →L[ℝ] E) : E →ₗ[ℝ] E) *
          LinearMap.det ((fderiv ℝ f z : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        1 := by
    rw [← LinearMap.det_comp]
    simpa [ContinuousLinearMap.coe_comp'] using congrArg LinearMap.det hcompLinear
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one hmul)

/-- The absolute determinant of the ambient derivative of the retained-passive
raw-order chart map.  This is only the forward source-side determinant factor;
it is not a pushforward theorem or an inverse-density formula. -/
def topologyTupleEdgeRawOrderFDerivAbsDet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' ℝ) : ℝ :=
  |LinearMap.det
    ((fderiv ℝ
      (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z :
        TopologyTuple ρ κ' ℝ →L[ℝ] TopologyTuple ρ κ' ℝ) :
      TopologyTuple ρ κ' ℝ →ₗ[ℝ] TopologyTuple ρ κ' ℝ)|

/-- The Frechet derivative of the retained-passive forward raw-order chart map
is continuous at determinant-chart points. -/
theorem continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (fun z : TopologyTuple ρ κ' ℝ ↦
        fderiv ℝ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z)
      z₀ := by
  exact
    (contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z₀ hz₀).continuousAt_fderiv one_ne_zero

/-- Applying the Frechet derivative of the retained-passive forward raw-order
chart map to a fixed tangent vector is continuous at determinant-chart
points. -/
theorem continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (v : TopologyTuple ρ κ' ℝ) :
    ContinuousAt
      (fun z : TopologyTuple ρ κ' ℝ ↦
        fderiv ℝ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z v)
      z₀ := by
  exact
    (continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z₀ hz₀).clm_apply continuousAt_const

/-- The retained-passive forward raw-order absolute Jacobian determinant is
continuous at determinant-chart points. -/
theorem continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ')) z₀ := by
  let E : Type _ := TopologyTuple ρ κ' ℝ
  let f : E → E := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hJ :
      ContinuousAt (fun z : E ↦ fderiv ℝ f z) z₀ :=
    continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') z₀ hz₀
  change ContinuousAt (fun z : E ↦ |(fderiv ℝ f z).det|) z₀
  exact (ContinuousLinearMap.continuous_det.continuousAt.comp hJ).abs

/-- The retained-passive forward raw-order absolute Jacobian determinant is
strictly positive at determinant-chart points. -/
theorem topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    0 < topologyTupleEdgeRawOrderFDerivAbsDet
      (ρ := ρ) (κ' := κ') z := by
  have hunit :=
    fderiv_topologyTupleEdgeRawOrder_det_isUnit_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz
  rw [topologyTupleEdgeRawOrderFDerivAbsDet]
  exact abs_pos.mpr (isUnit_iff_ne_zero.mp hunit)

/-- Near any retained-passive determinant-chart point, the forward raw-order
absolute Jacobian determinant is positive.  This uses openness of the chart,
not continuity of the Jacobian determinant function. -/
theorem eventually_topologyTupleEdgeRawOrderFDerivAbsDet_pos_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∀ᶠ z in 𝓝 z₀,
      0 < topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z := by
  filter_upwards [
    (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')).mem_nhds hz₀]
    with z hz
  exact
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz

/-- If the retained-passive forward raw-order absolute Jacobian determinant is
continuous at a determinant-chart point, then it admits a positive local lower
bound there.  The continuity hypothesis is supplied explicitly. -/
theorem exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
    (hcontinuous :
      ContinuousAt
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ')) z₀) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ z in 𝓝 z₀,
        ε ≤ topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z := by
  let density : TopologyTuple ρ κ' ℝ → ℝ :=
    topologyTupleEdgeRawOrderFDerivAbsDet
      (ρ := ρ) (κ' := κ')
  have hpos : 0 < density z₀ :=
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz₀
  refine ⟨density z₀ / 2, half_pos hpos, ?_⟩
  have htarget : ∀ᶠ y in 𝓝 (density z₀), density z₀ / 2 ≤ y := by
    exact eventually_ge_nhds (show density z₀ / 2 < density z₀ by linarith)
  exact hcontinuous.eventually htarget

/-- If the retained-passive forward raw-order absolute Jacobian determinant is
continuous at a determinant-chart point, then it admits a positive local upper
bound there.  The continuity hypothesis is supplied explicitly. -/
theorem exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hcontinuous :
      ContinuousAt
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ')) z₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ z in 𝓝 z₀,
        topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z ≤ K := by
  let density : TopologyTuple ρ κ' ℝ → ℝ :=
    topologyTupleEdgeRawOrderFDerivAbsDet
      (ρ := ρ) (κ' := κ')
  refine ⟨max (density z₀ + 1) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · have htarget : ∀ᶠ y in 𝓝 (density z₀), y ≤ density z₀ + 1 := by
      exact eventually_le_nhds (show density z₀ < density z₀ + 1 by linarith)
    exact (hcontinuous.eventually htarget).mono
      (fun _ hy ↦ le_trans hy (le_max_left _ _))

/-- Near any retained-passive determinant-chart point, the forward raw-order
absolute Jacobian determinant admits a positive local lower bound. -/
theorem exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ z in 𝓝 z₀,
        ε ≤ topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z := by
  exact
    exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt
      (ρ := ρ) (κ' := κ') z₀ hz₀
      (continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') z₀ hz₀)

/-- Near any retained-passive determinant-chart point, the forward raw-order
absolute Jacobian determinant admits a positive local upper bound. -/
theorem exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (z₀ : TopologyTuple ρ κ' ℝ)
    (hz₀ : z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ z in 𝓝 z₀,
        topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z ≤ K := by
  exact
    exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt
      (ρ := ρ) (κ' := κ') z₀
      (continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') z₀ hz₀)

/-- The retained-passive forward raw-order absolute Jacobian determinant is a
positive bounded unit after any source parametrization continuous at a point
mapping into the determinant chart. -/
theorem exists_pos_eventually_bounds_topologyTupleEdgeRawOrderFDerivAbsDet_comp
    {α : Type*} [TopologicalSpace α]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {Y : α → TopologyTuple ρ κ' ℝ} {a₀ : α}
    (hY : ContinuousAt Y a₀)
    (hY₀ : Y a₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∀ᶠ a in 𝓝 a₀,
        ε ≤ topologyTupleEdgeRawOrderFDerivAbsDet
            (ρ := ρ) (κ' := κ') (Y a) ∧
          topologyTupleEdgeRawOrderFDerivAbsDet
            (ρ := ρ) (κ' := κ') (Y a) ≤ K := by
  rcases exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨ε, hε_pos, hε⟩
  rcases exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨K, hK_pos, hK⟩
  refine ⟨ε, K, hε_pos, hK_pos, ?_⟩
  filter_upwards [hY.eventually hε, hY.eventually hK] with a ha_low ha_high
  exact ⟨ha_low, ha_high⟩

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
