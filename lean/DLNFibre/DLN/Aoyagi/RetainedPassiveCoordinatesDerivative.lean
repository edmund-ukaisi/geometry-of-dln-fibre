import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology

/-!
# Derivative footholds for retained-passive raw-order coordinates

This file begins the analytic derivative layer for the retained-passive
raw-order tuple endomap.  The first checkpoint records differentiability of
the endpoint-solved top-left family; later checkpoints will extend this to the
lower-left endpoint solve and the full raw-order map.

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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
