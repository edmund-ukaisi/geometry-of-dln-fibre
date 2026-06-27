import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
