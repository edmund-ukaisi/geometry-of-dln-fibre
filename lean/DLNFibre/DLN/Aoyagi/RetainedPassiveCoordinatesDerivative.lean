import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology

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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
