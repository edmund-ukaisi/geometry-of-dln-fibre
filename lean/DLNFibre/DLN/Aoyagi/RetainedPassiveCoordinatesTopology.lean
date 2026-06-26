import DLNFibre.DLN.Aoyagi.ChartTopology
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates

/-!
# Topology for retained-passive nonredundant coordinates

This file gives the nonredundant retained-passive coordinate record the product
topology on its finite matrix fields and proves that its determinant-domain
predicate is open.  It also records the elementary coordinate-projection
continuity facts for the stored fields and zero-filled dummy-slot embeddings.
It does not prove source-rank coverage, source/image equality, measure
transport, a Jacobian theorem, normal crossings, pole order, or RLCT
extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi
namespace ChartLocalSuffixState
namespace RetainedPassiveNonredundantCoordinateData

/-- Product coordinates used to topologize nonredundant retained-passive
coordinate data. -/
abbrev TopologyTuple
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) (K : Type*) :=
  (Fin M → Matrix ρ ρ K) ×
    ((∀ p : Fin (M + 1), Matrix ρ (κ' p.castSucc) K) ×
      ((∀ p : Fin M, Matrix (κ' p.castSucc.succ) ρ K) ×
        ((∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K) ×
          (Matrix ρ ρ K × Matrix (κ' (Fin.last (M + 1))) ρ K))))

/-- Tuple of matrix fields for nonredundant retained-passive coordinates. -/
def topologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :
    TopologyTuple ρ κ' K :=
  (data.A1passive, (data.F2, (data.A3passive, (data.C, (data.Ctop, data.F3)))))

/-- Nonredundant retained-passive coordinates carry the product topology on
their matrix fields. -/
instance instTopologicalSpace
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    TopologicalSpace
      (RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :=
  TopologicalSpace.induced topologyTuple inferInstance

theorem continuous_topologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    Continuous
      (topologyTuple :
        RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' →
          TopologyTuple ρ κ' K) := by
  exact continuous_induced_dom

@[continuity, fun_prop]
theorem continuous_A1passive
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K]
    (p : Fin M) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.A1passive p) := by
  simpa [topologyTuple] using
    (continuous_apply p).comp
      (continuous_fst.comp
        (continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K)))

@[continuity, fun_prop]
theorem continuous_F2
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K]
    (p : Fin (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.F2 p) := by
  simpa [topologyTuple] using
    (continuous_apply p).comp
      (continuous_fst.comp
        (continuous_snd.comp
          (continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K))))

@[continuity, fun_prop]
theorem continuous_A3passive
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K]
    (p : Fin M) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.A3passive p) := by
  simpa [topologyTuple] using
    (continuous_apply p).comp
      (continuous_fst.comp
        (continuous_snd.comp
          (continuous_snd.comp
            (continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K)))))

@[continuity, fun_prop]
theorem continuous_C
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K]
    (p : Fin (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.C p) := by
  simpa [topologyTuple] using
    (continuous_apply p).comp
      (continuous_fst.comp
        (continuous_snd.comp
          (continuous_snd.comp
            (continuous_snd.comp
              (continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K))))))

@[continuity, fun_prop]
theorem continuous_Ctop
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.Ctop) := by
  have htuple :
      Continuous
        (topologyTuple :
          RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' →
            TopologyTuple ρ κ' K) :=
    continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K)
  have h1 := continuous_snd.comp htuple
  have h2 := continuous_snd.comp h1
  have h3 := continuous_snd.comp h2
  have h4 := continuous_snd.comp h3
  have h5 := continuous_fst.comp h4
  simpa [topologyTuple] using h5

@[continuity, fun_prop]
theorem continuous_F3
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.F3) := by
  have htuple :
      Continuous
        (topologyTuple :
          RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' →
            TopologyTuple ρ κ' K) :=
    continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K)
  have h1 := continuous_snd.comp htuple
  have h2 := continuous_snd.comp h1
  have h3 := continuous_snd.comp h2
  have h4 := continuous_snd.comp h3
  have h5 := continuous_snd.comp h4
  simpa [topologyTuple] using h5

@[continuity, fun_prop]
theorem continuous_A1seed
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] (p : Fin (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.A1seed p) := by
  cases p using Fin.cases with
  | zero =>
      simpa [A1seed] using
        (continuous_const :
          Continuous
            (fun _data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' ↦ (0 : Matrix ρ ρ K)))
  | succ p =>
      simpa [A1seed] using
        continuous_A1passive (ρ := ρ) (κ' := κ') (K := K) p

@[continuity, fun_prop]
theorem continuous_F2full
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] (i : Fin (M + 2)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.F2full i) := by
  induction i using Fin.lastCases with
  | last =>
      simpa [F2full] using
        (continuous_const :
          Continuous
            (fun _data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' ↦
              (0 : Matrix ρ (κ' (Fin.last (M + 1))) K)))
  | cast i =>
      simpa [F2full] using
        continuous_F2 (ρ := ρ) (κ' := κ') (K := K) i

@[continuity, fun_prop]
theorem continuous_A3seed
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] (p : Fin (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦ data.A3seed p) := by
  induction p using Fin.lastCases with
  | last =>
      simpa [A3seed] using
        (continuous_const :
          Continuous
            (fun _data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' ↦
              (0 : Matrix (κ' (Fin.last M).succ) ρ K)))
  | cast p =>
      simpa [A3seed] using
        continuous_A3passive (ρ := ρ) (κ' := κ') (K := K) p

/-- The passive top-left tail product is continuous as a function of the
nonredundant retained-passive coordinates. -/
theorem continuous_retainedPassiveA1TailAfterFirst
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ] :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦
        retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) data.A1seed) := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let i₀ : Fin (M + 2) := (0 : Fin (M + 1)).succ
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    1 ≤ m →
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            data.A1seed j ⟨m, Nat.lt_succ_of_le hm⟩
              (Fin.val_fin_le.mpr hm))
  have hbase : motive (M + 1) le_rfl := by
    intro _hmpos
    change
      Continuous
        (fun _data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            _ j j le_rfl)
    simpa using
      (continuous_const :
        Continuous
          (fun _data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            (1 : Matrix ρ ρ K)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := by
      exact Fin.val_fin_le.mpr hms
    have hnext :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              data.A1seed j p.succ hpj) := by
      simpa [motive, j, p] using ih (Nat.succ_pos m)
    have hfactor :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦ data.A1seed p) :=
      continuous_A1seed (ρ := ρ) (κ' := κ') (K := K) p
    have hmul :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                data.A1seed j p.succ hpj *
              data.A1seed p) :=
      hnext.matrix_mul hfactor
    change
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            data.A1seed j p.castSucc ((Fin.castSucc_le_succ p).trans hpj))
    rw [show
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            data.A1seed j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun data ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                data.A1seed j p.succ hpj *
              data.A1seed p by
      funext data
      exact
        residualFactorProduct_castSucc
          (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ) data.A1seed p hpj]
    simpa [p] using hmul
  have htail :=
    Nat.decreasingInduction (motive := motive) hstep hbase
      (Nat.succ_le_succ (Nat.zero_le M))
  have htail' := htail le_rfl
  simpa [retainedPassiveA1TailAfterFirst, j, i₀, motive] using htail'

/-- On the determinant chart, each solved full `A1` component is continuous. -/
theorem continuous_solvedA1_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    (p : Fin (M + 1)) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        (data.1.toCoordinateData).solvedA1 p) := by
  cases p using Fin.cases with
  | zero =>
      have htail :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
                data.1.A1seed) :=
        continuous_retainedPassiveA1TailAfterFirst
          (ρ := ρ) (κ' := κ') (K := K) |>.comp continuous_subtype_val
      have hunit :
          ∀ data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart},
            IsUnit
              (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
                data.1.A1seed).det := by
        intro data
        exact
          retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
            (K := K) (ρ := ρ) data.1.A1seed
            (data.1.toCoordinateData_passiveA1_units data.2.2)
      have htailInv :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
                data.1.A1seed)⁻¹) :=
        continuous_matrix_inv_of_forall_isUnit_det htail hunit
      have hCtop :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              data.1.Ctop) :=
        (continuous_Ctop (ρ := ρ) (κ' := κ') (K := K)).comp
          continuous_subtype_val
      have hmul :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
                  data.1.A1seed)⁻¹ *
                data.1.Ctop) :=
        htailInv.matrix_mul hCtop
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData] using hmul
  | succ p =>
      have hseed :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              data.1.A1seed p.succ) :=
        (continuous_A1seed (ρ := ρ) (κ' := κ') (K := K) p.succ).comp
          continuous_subtype_val
      simpa [RetainedPassiveCoordinateData.solvedA1, retainedPassiveSolvedA1,
        toCoordinateData, Fin.succ_ne_zero] using hseed

/-- The zeroed-final lower-left family is continuous componentwise. -/
theorem continuous_retainedPassiveA3WithoutLast
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] (p : Fin (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦
        retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.A3seed p) := by
  by_cases hp : p = Fin.last M
  · subst p
    simpa [retainedPassiveA3WithoutLast] using
      (continuous_const :
        Continuous
          (fun _data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            (0 : Matrix (κ' (Fin.last M).succ) ρ K)))
  · simpa [retainedPassiveA3WithoutLast, hp] using
      continuous_A3seed (ρ := ρ) (κ' := κ') (K := K) p

/-- Residual products of the stored `C` blocks are continuous. -/
theorem continuous_residualFactorProduct_C
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1)) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦
        residualFactorProduct (K := K) (κ := κ')
          data.C (Fin.last (M + 1)) i hi) := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' ↦
        residualFactorProduct (K := K) (κ := κ')
          data.C j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm))
  have hbase : motive (M + 1) le_rfl := by
    change
      Continuous
        (fun _data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := κ') _ j j le_rfl)
    simpa using
      (continuous_const :
        Continuous
          (fun _data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            (1 : Matrix (κ' j) (κ' j) K)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            residualFactorProduct (K := K) (κ := κ')
              data.C j p.succ hpj) := by
      simpa [motive, j, p] using ih
    have hfactor :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦ data.C p) :=
      continuous_C (ρ := ρ) (κ' := κ') (K := K) p
    have hmul :
        Continuous
          (fun data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' ↦
            residualFactorProduct (K := K) (κ := κ') data.C j p.succ hpj *
              data.C p) :=
      hnext.matrix_mul hfactor
    change
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := κ') data.C j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj))
    rw [show
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ' ↦
          residualFactorProduct (K := K) (κ := κ') data.C j p.castSucc
            ((Fin.castSucc_le_succ p).trans hpj)) =
          fun data ↦
            residualFactorProduct (K := K) (κ := κ') data.C j p.succ hpj *
              data.C p by
      funext data
      exact
        residualFactorProduct_castSucc
          (K := K) (κ := κ') data.C p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- A determinant-chart point has determinant-unit solved full `A1` blocks. -/
theorem solvedA1_det_isUnit_of_detChart
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ]
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ')
    (hdet : data.detChart) :
    ∀ p : Fin (M + 1), IsUnit ((data.toCoordinateData).solvedA1 p).det := by
  change ∀ p : Fin (M + 1),
    IsUnit
      (retainedPassiveSolvedA1 (K := K) (ρ := ρ)
        data.A1seed data.Ctop p).det
  exact
    retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
      (K := K) (ρ := ρ)
      (retainedPassiveSolvedA1 (K := K) (ρ := ρ) data.A1seed data.Ctop)
      data.Ctop
      (retainedPassiveSolvedA1_passive_det_isUnit
        (K := K) (ρ := ρ) data.A1seed data.Ctop
        (data.toCoordinateData_passiveA1_units hdet.2))
      hdet.1
      (retainedPassiveSolvedA1_zero_eq_tail_inv_mul
        (K := K) (ρ := ρ) data.A1seed data.Ctop)

/-- Residual products of the solved full `A1` family are continuous on the
determinant-chart subtype. -/
theorem continuous_residualFactorProduct_solvedA1_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1)) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          (Fin.last (M + 1)) i hi) := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm))
  have hbase : motive (M + 1) le_rfl := by
    change
      Continuous
        (fun _data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            _ j j le_rfl)
    simpa using
      (continuous_const :
        Continuous
          (fun _data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            (1 : Matrix ρ ρ K)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hnext :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
              j p.succ hpj) := by
      simpa [motive, j, p] using ih
    have hfactor :=
      continuous_solvedA1_detChart_subtype
        (ρ := ρ) (κ' := κ') (K := K) p
    have hmul :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                j p.succ hpj *
              (data.1.toCoordinateData).solvedA1 p) :=
      hnext.matrix_mul hfactor
    change
      Continuous
        (fun data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj))
    rw [show
        (fun data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
            j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)) =
          fun data ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                j p.succ hpj *
              (data.1.toCoordinateData).solvedA1 p by
      funext data
      exact
        residualFactorProduct_castSucc
          (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          p hpj]
    simpa [p] using hmul
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j] using hcanon

/-- Residual products of the solved full `A1` family are determinant-units on
the determinant chart. -/
theorem residualFactorProduct_solvedA1_det_isUnit_of_detChart
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ]
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ')
    (hdet : data.detChart)
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1)) :
    IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        (fun p : Fin (M + 1) ↦ (data.toCoordinateData).solvedA1 p)
        (Fin.last (M + 1)) i hi).det := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let A1 : Fin (M + 1) → Matrix ρ ρ K :=
    fun p ↦ (data.toCoordinateData).solvedA1 p
  have hA1 : ∀ p : Fin (M + 1), IsUnit (A1 p).det := by
    intro p
    exact solvedA1_det_isUnit_of_detChart (K := K) (ρ := ρ) data hdet p
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)).det
  have hbase : motive (M + 1) le_rfl := by
    change IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 j j le_rfl).det
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have hprod :
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1 j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              A1 j p.succ hpj * A1 p := by
      exact
        residualFactorProduct_castSucc
          (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ) A1 p hpj
    change IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)).det
    rw [hprod]
    simpa [Matrix.det_mul] using ih.mul (hA1 p)
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, j, A1] using hcanon

/-- The explicit lower-left product-tail sum built from solved `A1`, zeroed
early `A3`, and stored `C` blocks is continuous on the determinant-chart
subtype. -/
theorem continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (m : ℕ) (hm : m ≤ M + 1) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
          data.1.C m hm) := by
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
          data.1.C m hm)
  have hbase : motive (M + 1) le_rfl := by
    change
      Continuous
        (fun _data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            _ _ _ (M + 1) le_rfl)
    simpa using
      (continuous_const :
        Continuous
          (fun _data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            (0 : Matrix (κ' (Fin.last (M + 1))) ρ K)))
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hpj : p.succ ≤ Fin.last (M + 1) := Fin.val_fin_le.mpr hms
    have hCprod :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            residualFactorProduct (K := K) (κ := κ') data.1.C
              (Fin.last (M + 1)) p.succ hpj) :=
      (continuous_residualFactorProduct_C
        (ρ := ρ) (κ' := κ') (K := K) p.succ hpj).comp
          continuous_subtype_val
    have hA3early :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            retainedPassiveA3WithoutLast (K := K) (ρ := ρ)
              data.1.A3seed p) :=
      (continuous_retainedPassiveA3WithoutLast
        (ρ := ρ) (κ' := κ') (K := K) p).comp continuous_subtype_val
    have hA1prod :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj)) :=
      continuous_residualFactorProduct_solvedA1_detChart_subtype
        (ρ := ρ) (κ' := κ') (K := K) p.castSucc
        ((Fin.castSucc_le_succ p).trans hpj)
    have hA1prodInv :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
              (Fin.last (M + 1)) p.castSucc
                ((Fin.castSucc_le_succ p).trans hpj))⁻¹) :=
      continuous_matrix_inv_of_forall_isUnit_det hA1prod (fun data ↦
        residualFactorProduct_solvedA1_det_isUnit_of_detChart
          (K := K) (ρ := ρ) data.1 data.2 p.castSucc
          ((Fin.castSucc_le_succ p).trans hpj))
    have hsummand :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            -(residualFactorProduct (K := K) (κ := κ') data.1.C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := K) (ρ := ρ)
                  data.1.A3seed p *
                (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹)) := by
      exact ((hCprod.matrix_mul hA3early).matrix_mul hA1prodInv).neg
    have htail : motive (m + 1) hms := ih
    have hsum :
        Continuous
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            -(residualFactorProduct (K := K) (κ := κ') data.1.C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := K) (ρ := ρ)
                  data.1.A3seed p *
                (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
                data.1.C (m + 1) hms) :=
      hsummand.add htail
    change
      Continuous
        (fun data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
            (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
            data.1.C p.val (Nat.le_of_lt p.isLt))
    rw [show
        (fun data :
            {data : RetainedPassiveNonredundantCoordinateData
                (K := K) (ρ := ρ) κ' // data.detChart} ↦
          retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
            (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
            data.1.C p.val (Nat.le_of_lt p.isLt)) =
          fun data ↦
            -(residualFactorProduct (K := K) (κ := κ') data.1.C
                  (Fin.last (M + 1)) p.succ hpj *
                retainedPassiveA3WithoutLast (K := K) (ρ := ρ)
                  data.1.A3seed p *
                (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) p.castSucc
                    ((Fin.castSucc_le_succ p).trans hpj))⁻¹) +
              retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
                data.1.C (m + 1) hms by
      funext data
      simpa [p] using
        retainedPassiveLowerLeftProductTailSum_castSucc
          (K := K) (ρ := ρ) (κ := κ')
          (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
          (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
          data.1.C p]
    simpa [p] using hsum
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase hm
  simpa [motive] using hcanon

/-- On the determinant chart, each solved full `A3` component is continuous. -/
theorem continuous_solvedA3_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (p : Fin (M + 1)) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        (data.1.toCoordinateData).solvedA3 p) := by
  induction p using Fin.lastCases with
  | last =>
      have hF3 :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              data.1.F3) :=
        (continuous_F3 (ρ := ρ) (κ' := κ') (K := K)).comp
          continuous_subtype_val
      have hEarlyTail :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) data.1.A3seed)
                data.1.C 0 (Nat.zero_le (M + 1))) :=
        continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
          (ρ := ρ) (κ' := κ') (K := K) 0 (Nat.zero_le (M + 1))
      have hCtopLast :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                (fun p : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 p)
                (Fin.last (M + 1)) (Fin.last M).castSucc
                  (Fin.last M).castSucc.le_last) :=
        continuous_residualFactorProduct_solvedA1_detChart_subtype
          (ρ := ρ) (κ' := κ') (K := K) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
      have hlast :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              -(data.1.F3 -
                  retainedPassiveLowerLeftProductTailSum
                    (K := K) (ρ := ρ) (κ := κ')
                    (fun p : Fin (M + 1) ↦
                      (data.1.toCoordinateData).solvedA1 p)
                    (retainedPassiveA3WithoutLast
                      (K := K) (ρ := ρ) data.1.A3seed)
                    data.1.C 0 (Nat.zero_le (M + 1))) *
                residualFactorProduct (K := K)
                  (κ := fun _ : Fin (M + 2) ↦ ρ)
                  (fun p : Fin (M + 1) ↦
                    (data.1.toCoordinateData).solvedA1 p)
                  (Fin.last (M + 1)) (Fin.last M).castSucc
                    (Fin.last M).castSucc.le_last) :=
        (hF3.sub hEarlyTail).neg.matrix_mul hCtopLast
      simpa [RetainedPassiveCoordinateData.solvedA3,
        RetainedPassiveCoordinateData.solvedA1, toCoordinateData] using hlast
  | cast p =>
      have hseed :
          Continuous
            (fun data :
                {data : RetainedPassiveNonredundantCoordinateData
                    (K := K) (ρ := ρ) κ' // data.detChart} ↦
              data.1.A3seed p.castSucc) :=
        (continuous_A3seed (ρ := ρ) (κ' := κ') (K := K) p.castSucc).comp
          continuous_subtype_val
      have hfun :
          (fun data :
              {data : RetainedPassiveNonredundantCoordinateData
                  (K := K) (ρ := ρ) κ' // data.detChart} ↦
            (data.1.toCoordinateData).solvedA3 p.castSucc) =
            fun data ↦ data.1.A3seed p.castSucc := by
        funext data
        exact
          retainedPassiveSolvedA3_eq_of_ne_last
            (K := K) (ρ := ρ) (κ' := κ')
            (data.1.toCoordinateData).solvedA1
            data.1.A3seed data.1.C data.1.F3
            (Fin.castSucc_ne_last p)
      rw [hfun]
      exact hseed

/-- On the determinant chart, each retained-passive fixed-base source edge is
continuous. -/
theorem continuous_edgeMatrix_detChart_subtype_apply
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (p : Fin (M + 1)) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        data.1.edgeMatrix p) := by
  let X :=
    {data : RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := ρ) κ' // data.detChart}
  have hA1 :
      Continuous
        (fun data : X ↦
          (data.1.toCoordinateData).solvedA1 p) :=
    continuous_solvedA1_detChart_subtype
      (ρ := ρ) (κ' := κ') (K := K) p
  have hA3 :
      Continuous
        (fun data : X ↦
          (data.1.toCoordinateData).solvedA3 p) :=
    continuous_solvedA3_detChart_subtype
      (ρ := ρ) (κ' := κ') (K := K) p
  have hF2current :
      Continuous
        (fun data : X ↦ data.1.F2full p.castSucc) :=
    (continuous_F2full (ρ := ρ) (κ' := κ') (K := K) p.castSucc).comp
      continuous_subtype_val
  have hF2next :
      Continuous
        (fun data : X ↦ data.1.F2full p.succ) :=
    (continuous_F2full (ρ := ρ) (κ' := κ') (K := K) p.succ).comp
      continuous_subtype_val
  have hC :
      Continuous
        (fun data : X ↦ data.1.C p) :=
    (continuous_C (ρ := ρ) (κ' := κ') (K := K) p).comp
      continuous_subtype_val
  have hA1F2 :
      Continuous
        (fun data : X ↦
          (data.1.toCoordinateData).solvedA1 p * data.1.F2full p.castSucc) :=
    hA1.matrix_mul hF2current
  have hA3F2 :
      Continuous
        (fun data : X ↦
          (data.1.toCoordinateData).solvedA3 p * data.1.F2full p.castSucc) :=
    hA3.matrix_mul hF2current
  have hTransformed :
      Continuous
        (fun data : X ↦
          retainedPassiveTransformedEdge (K := K) (ρ := ρ) (κ := κ')
            (fun q : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 q)
            data.1.F2full
            (fun q : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA3 q)
            data.1.C p) := by
    simpa [retainedPassiveTransformedEdge] using
      hA1.matrix_fromBlocks hA1F2.neg hA3 (hC.sub hA3F2)
  have hLeft :
      Continuous
        (fun data : X ↦
          fromBlocks (1 : Matrix ρ ρ K) (data.1.F2full p.succ)
            (0 : Matrix (κ' p.succ) ρ K)
            (1 : Matrix (κ' p.succ) (κ' p.succ) K)) := by
    simpa using
      (continuous_const.matrix_fromBlocks hF2next
        (continuous_const : Continuous
          (fun _data : X ↦ (0 : Matrix (κ' p.succ) ρ K)))
        (continuous_const : Continuous
          (fun _data : X ↦
            (1 : Matrix (κ' p.succ) (κ' p.succ) K))))
  have hEdge :
      Continuous
        (fun data : X ↦
          fromBlocks (1 : Matrix ρ ρ K) (data.1.F2full p.succ)
              (0 : Matrix (κ' p.succ) ρ K)
              (1 : Matrix (κ' p.succ) (κ' p.succ) K) *
            retainedPassiveTransformedEdge (K := K) (ρ := ρ) (κ := κ')
              (fun q : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA1 q)
              data.1.F2full
              (fun q : Fin (M + 1) ↦ (data.1.toCoordinateData).solvedA3 q)
              data.1.C p) :=
    hLeft.matrix_mul hTransformed
  simpa [X, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix,
    retainedPassiveFixedBaseEdgeMatrix, toCoordinateData] using hEdge

/-- On the determinant chart, the retained-passive fixed-base source edge
family is continuous. -/
theorem continuous_edgeMatrix_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        data.1.edgeMatrix) := by
  refine continuous_pi ?_
  intro p
  exact continuous_edgeMatrix_detChart_subtype_apply
    (ρ := ρ) (κ' := κ') (K := K) p

/-- The nonredundant retained-passive determinant-domain set is open. -/
theorem isOpen_detChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
    [Fintype ρ] [DecidableEq ρ] :
    IsOpen (detChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  have hA1 : IsOpen
      ({data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' |
        ∀ p : Fin M, IsUnit (data.A1passive p).det}) := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun p ↦
      ((continuous_A1passive (ρ := ρ) (κ' := κ') (K := K) p).matrix_det).isOpen_preimage
        ({a : K | IsUnit a}) isOpen_setOf_isUnit
  have hCtop : IsOpen
      ({data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ' |
        IsUnit data.Ctop.det}) := by
    exact
      ((continuous_Ctop (ρ := ρ) (κ' := κ') (K := K)).matrix_det).isOpen_preimage
        ({a : K | IsUnit a}) isOpen_setOf_isUnit
  simpa [detChartSet, detChart, Set.setOf_and] using hCtop.inter hA1

/-- A determinant-domain point has the determinant-domain set as a
neighborhood. -/
theorem detChartSet_mem_nhds
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
    [Fintype ρ] [DecidableEq ρ]
    {data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ'}
    (hdet : data.detChart) :
    detChartSet (K := K) (ρ := ρ) (κ' := κ') ∈ nhds data :=
  IsOpen.mem_nhds isOpen_detChartSet hdet

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
