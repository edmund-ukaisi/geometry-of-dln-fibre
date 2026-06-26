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
