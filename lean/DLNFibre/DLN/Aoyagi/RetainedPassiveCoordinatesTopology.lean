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
