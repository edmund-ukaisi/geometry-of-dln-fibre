import DLNFibre.DLN.Aoyagi.ChartTopology
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

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

/-- Rebuild retained-passive nonredundant coordinate data from its product
tuple of fields. -/
def ofTopologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' where
  A1passive := z.1
  F2 := z.2.1
  A3passive := z.2.2.1
  C := z.2.2.2.1
  Ctop := z.2.2.2.2.1
  F3 := z.2.2.2.2.2

@[simp]
theorem topologyTuple_ofTopologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    topologyTuple (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z) = z := by
  rcases z with ⟨A1passive, F2, A3passive, C, Ctop, F3⟩
  rfl

@[simp]
theorem ofTopologyTuple_topologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :
    ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') (topologyTuple data) = data := by
  cases data
  rfl

/-- The product tuple representation is injective. -/
theorem topologyTuple_injective
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} :
    Function.Injective
      (topologyTuple :
        RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' →
          TopologyTuple ρ κ' K) := by
  intro data data' h
  calc
    data = ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') (topologyTuple data) := by
      rw [ofTopologyTuple_topologyTuple]
    _ = ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') (topologyTuple data') := by
      rw [h]
    _ = data' := by
      rw [ofTopologyTuple_topologyTuple]

/-- The retained-passive determinant chart as a set in product-tuple
coordinates. -/
def topologyTupleDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] :
    Set (TopologyTuple ρ κ' K) :=
  {z | (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).detChart}

@[simp]
theorem mem_topologyTupleDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ]
    (z : TopologyTuple ρ κ' K) :
    z ∈ topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') ↔
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).detChart := by
  rfl

@[simp]
theorem topologyTuple_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ]
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :
    topologyTuple data ∈ topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') ↔
      data.detChart := by
  simp [topologyTupleDetChartSet]

/-- The retained-passive fixed-base source map written as a map out of the
product tuple space. -/
def topologyTupleEdgeMatrix
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    ∀ p : Fin (M + 1), Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K :=
  (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).edgeMatrix

@[simp]
theorem topologyTupleEdgeMatrix_topologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :
    topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') (topologyTuple data) =
      data.edgeMatrix := by
  simp [topologyTupleEdgeMatrix]

/-- The tuple-level retained-passive source map sends the tuple determinant
chart into the source-recursive determinant chart. -/
theorem mapsTo_topologyTupleEdgeMatrix_detChartSet_sourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    Set.MapsTo
      (topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ'))
      (topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ'))
      (sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  intro z hz
  exact
    (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')
      (topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z)).2
      (sourceRecursiveDetChart_edgeMatrix_of_detChart
        (K := K) (ρ := ρ)
        (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z)
        ((mem_topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') z).1 hz))

/-- The tuple-level retained-passive source map is injective on the tuple
determinant chart. -/
theorem injOn_topologyTupleEdgeMatrix_detChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    Set.InjOn
      (topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ'))
      (topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  intro z hz w hw hE
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  let data' := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') w
  have hEdata : data.edgeMatrix = data'.edgeMatrix := by
    simpa [topologyTupleEdgeMatrix, data, data'] using hE
  have hdata : data = data' := by
    exact
      edgeMatrix_ext_of_detChart (K := K) (ρ := ρ) data data'
        ((mem_topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') z).1 hz)
        ((mem_topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') w).1 hw)
        hEdata
  calc
    z = topologyTuple data := by
      simp [data]
    _ = topologyTuple data' := by
      rw [hdata]
    _ = w := by
      simp [data']

/-- The tuple-level retained-passive source map has image exactly the
source-recursive determinant chart. -/
theorem image_topologyTupleEdgeMatrix_detChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') ''
        topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') =
      sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
  ext E
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact
      mapsTo_topologyTupleEdgeMatrix_detChartSet_sourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') hz
  · intro hE
    let data := sourceReadback (K := K) (ρ := ρ) E
    have hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) E :=
      (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E).1 hE
    refine ⟨topologyTuple data, ?_, ?_⟩
    · simpa [data] using
        (sourceReadback_detChart_of_sourceRecursiveDetChart
          (K := K) (ρ := ρ) E hchart)
    · simpa [data, topologyTupleEdgeMatrix] using
        (edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
          (K := K) (ρ := ρ) E hchart)

/-- Fixed-base source edge families in the retained-passive shape. -/
abbrev EdgeFamilyTuple
    {M : ℕ} (ρ : Type*) (κ' : Fin (M + 2) → Type*) (K : Type*) :=
  ∀ p : Fin (M + 1), Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K

/-- The raw top-left edge blocks packed in the endpoint order used by
`TopologyTuple`: edge `0` becomes the endpoint slot and later edges become the
passive family. -/
def rawEdgeTupleA1
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    Fin (M + 1) → Matrix ρ ρ K :=
  Fin.cases
    (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).Ctop
    (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).A1passive

/-- The raw lower-left edge blocks packed in the endpoint order used by
`TopologyTuple`: nonterminal edges become the passive family and the last edge
becomes the endpoint slot. -/
def rawEdgeTupleA3
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K :=
  Fin.snoc
    (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).A3passive
    (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).F3

@[simp]
theorem rawEdgeTupleA1_zero
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') z 0 =
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).Ctop := by
  simp [rawEdgeTupleA1]

@[simp]
theorem rawEdgeTupleA1_succ
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) (p : Fin M) :
    rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') z p.succ =
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).A1passive p := by
  simp [rawEdgeTupleA1]

@[simp]
theorem rawEdgeTupleA3_castSucc
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) (p : Fin M) :
    rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') z p.castSucc =
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).A3passive p := by
  simp [rawEdgeTupleA3]

@[simp]
theorem rawEdgeTupleA3_last
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') z (Fin.last M) =
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).F3 := by
  simp [rawEdgeTupleA3]

/-- Reconstruct an edge family from raw edge blocks packed in the
`TopologyTuple` product order. -/
def edgeFamilyOfRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    EdgeFamilyTuple ρ κ' K :=
  fun p ↦
    Matrix.fromBlocks
      (rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') z p)
      ((ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).F2 p)
      (rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') z p)
      ((ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).C p)

/-- Read an edge family into raw block coordinates packed in the
`TopologyTuple` product order.  This is a target-coordinate readout, not a
retained-passive coordinate inverse. -/
def edgeFamilyRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (E : EdgeFamilyTuple ρ κ' K) :
    TopologyTuple ρ κ' K :=
  (fun p : Fin M ↦ (E p.succ).toBlocks₁₁,
    (fun p : Fin (M + 1) ↦ (E p).toBlocks₁₂,
      (fun p : Fin M ↦ (E p.castSucc).toBlocks₂₁,
        (fun p : Fin (M + 1) ↦ (E p).toBlocks₂₂,
          ((E 0).toBlocks₁₁, (E (Fin.last M)).toBlocks₂₁)))))

@[simp]
theorem edgeFamilyRawOrderTuple_edgeFamilyOfRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (z : TopologyTuple ρ κ' K) :
    edgeFamilyRawOrderTuple
        (K := K) (ρ := ρ) (κ' := κ')
        (edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z) = z := by
  rcases z with ⟨A1passive, F2, A3passive, C, Ctop, F3⟩
  ext p <;>
    simp [edgeFamilyRawOrderTuple, edgeFamilyOfRawOrderTuple, ofTopologyTuple,
      rawEdgeTupleA1,
      rawEdgeTupleA3]

@[simp]
theorem edgeFamilyOfRawOrderTuple_edgeFamilyRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    (E : EdgeFamilyTuple ρ κ' K) :
    edgeFamilyOfRawOrderTuple
        (K := K) (ρ := ρ) (κ' := κ')
        (edgeFamilyRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') E) = E := by
  funext p
  let A : Matrix ρ ρ K :=
    Fin.cases
      (motive := fun _ : Fin (M + 1) ↦ Matrix ρ ρ K)
      (E 0).toBlocks₁₁ (fun q : Fin M ↦ (E q.succ).toBlocks₁₁) p
  let L : Matrix (κ' p.succ) ρ K :=
    Fin.snoc
      (n := M)
      (α := fun q : Fin (M + 1) ↦ Matrix (κ' q.succ) ρ K)
      (fun q : Fin M ↦ (E q.castSucc).toBlocks₂₁)
      (E (Fin.last M)).toBlocks₂₁ p
  have hA1 : A = (E p).toBlocks₁₁ := by
    dsimp [A]
    cases p using Fin.cases <;> simp
  have hA3 : L = (E p).toBlocks₂₁ := by
    dsimp [L]
    cases p using Fin.lastCases <;> simp
  dsimp [edgeFamilyOfRawOrderTuple, edgeFamilyRawOrderTuple, ofTopologyTuple,
    rawEdgeTupleA1, rawEdgeTupleA3]
  change Matrix.fromBlocks A (E p).toBlocks₁₂ L (E p).toBlocks₂₂ = E p
  rw [hA1, hA3]
  exact Matrix.fromBlocks_toBlocks (E p)

/-- Block extraction gives a linear equivalence between edge families and raw
edge blocks packed in the `TopologyTuple` product order. -/
def edgeFamilyRawOrderLinearEquiv
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [Semiring K] :
    EdgeFamilyTuple ρ κ' K ≃ₗ[K] TopologyTuple ρ κ' K where
  toFun := edgeFamilyRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')
  invFun := edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')
  map_add' E E' := by
    rcases M with _ | M
    · ext <;> rfl
    · ext <;> rfl
  map_smul' a E := by
    rcases M with _ | M
    · ext <;> rfl
    · ext <;> rfl
  left_inv := edgeFamilyOfRawOrderTuple_edgeFamilyRawOrderTuple
    (K := K) (ρ := ρ) (κ' := κ')
  right_inv := edgeFamilyRawOrderTuple_edgeFamilyOfRawOrderTuple
    (K := K) (ρ := ρ) (κ' := κ')

/-- The retained-passive source map with its edge-family output read in raw
block coordinates.  This is an endomap of the ambient tuple space, intended as
the target-coordinate map for a future Jacobian theorem. -/
def topologyTupleEdgeRawOrder
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    TopologyTuple ρ κ' K :=
  edgeFamilyRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')
    (topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z)

@[simp]
theorem topologyTupleEdgeRawOrder_A1passive
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) (p : Fin M) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).1 p =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      let A1 := data.toCoordinateData.solvedA1
      let A3 := data.toCoordinateData.solvedA3
      A1 p.succ + data.toCoordinateData.F2 p.succ.succ * A3 p.succ := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks11_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) p.succ

@[simp]
theorem topologyTupleEdgeRawOrder_F2
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) (p : Fin (M + 1)) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.1 p =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      let A1 := data.toCoordinateData.solvedA1
      let A3 := data.toCoordinateData.solvedA3
      (-(A1 p * data.toCoordinateData.F2 p.castSucc) +
        data.toCoordinateData.F2 p.succ *
          (data.toCoordinateData.C p - A3 p * data.toCoordinateData.F2 p.castSucc)) := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks12_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) p

@[simp]
theorem topologyTupleEdgeRawOrder_A3passive
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) (p : Fin M) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.1 p =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      data.toCoordinateData.solvedA3 p.castSucc := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks21_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) p.castSucc

@[simp]
theorem topologyTupleEdgeRawOrder_C
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) (p : Fin (M + 1)) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.2.1 p =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      let A3 := data.toCoordinateData.solvedA3
      data.toCoordinateData.C p - A3 p * data.toCoordinateData.F2 p.castSucc := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks22_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) p

@[simp]
theorem topologyTupleEdgeRawOrder_Ctop
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.2.2.1 =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      let A1 := data.toCoordinateData.solvedA1
      let A3 := data.toCoordinateData.solvedA3
      A1 0 + data.toCoordinateData.F2 (0 : Fin (M + 1)).succ * A3 0 := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks11_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) 0

@[simp]
theorem topologyTupleEdgeRawOrder_F3
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.2.2.2 =
      let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
      data.toCoordinateData.solvedA3 (Fin.last M) := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  dsimp [topologyTupleEdgeRawOrder, edgeFamilyRawOrderTuple,
    topologyTupleEdgeMatrix, edgeMatrix, RetainedPassiveCoordinateData.edgeMatrix, data]
  exact toBlocks21_retainedPassiveFixedBaseEdgeMatrix
    (K := K) (A1 := data.toCoordinateData.solvedA1)
    (F2 := data.toCoordinateData.F2) (A3 := data.toCoordinateData.solvedA3)
    (C := data.toCoordinateData.C) (Fin.last M)

@[simp]
theorem rawEdgeTupleA3_topologyTupleEdgeRawOrder
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) (p : Fin (M + 1)) :
    rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z) p =
      ((ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA3 p := by
  induction p using Fin.lastCases with
  | last =>
      rw [rawEdgeTupleA3_last]
      change (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.2.2.2 =
        ((ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA3
          (Fin.last M)
      rw [topologyTupleEdgeRawOrder_F3]
  | cast p =>
      rw [rawEdgeTupleA3_castSucc]
      change (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z).2.2.1 p =
        ((ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).toCoordinateData).solvedA3
          p.castSucc
      rw [topologyTupleEdgeRawOrder_A3passive]

@[simp]
theorem edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    edgeFamilyOfRawOrderTuple
        (K := K) (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z) =
      topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z := by
  simp [topologyTupleEdgeRawOrder]

/-- The raw-order tuple representative of the retained-passive source map is
injective on the tuple determinant chart. -/
theorem injOn_topologyTupleEdgeRawOrder_detChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    Set.InjOn
      (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ'))
      (topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  intro z hz w hw hraw
  apply injOn_topologyTupleEdgeMatrix_detChartSet
      (K := K) (ρ := ρ) (κ' := κ') hz hw
  have hE := congrArg
    (edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')) hraw
  simpa using hE

/-- The source-recursive determinant chart read in raw-order tuple
coordinates. -/
def topologyTupleRawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    Set (TopologyTuple ρ κ' K) :=
  {z | edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z ∈
    sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')}

@[simp]
theorem mem_topologyTupleRawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] (z : TopologyTuple ρ κ' K) :
    z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') ↔
      edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z ∈
        sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
  rfl

/-- Source readback after rebuilding the edge family from a raw-order target
tuple. -/
def topologyTupleEdgeRawOrderInverse
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    (z : TopologyTuple ρ κ' K) :
    TopologyTuple ρ κ' K :=
  topologyTuple
    (sourceReadback (K := K) (ρ := ρ)
      (edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z))

/-- The retained-passive raw-order source map sends the tuple determinant chart
into the raw-order source-recursive determinant chart. -/
theorem mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    Set.MapsTo
      (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ'))
      (topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ'))
      (topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) := by
  intro z hz
  have hsource :
      topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z ∈
        sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') :=
    mapsTo_topologyTupleEdgeMatrix_detChartSet_sourceRecursiveDetChartSet
      (K := K) (ρ := ρ) (κ' := κ') hz
  simpa [topologyTupleRawOrderSourceRecursiveDetChartSet] using hsource

/-- Raw-order source readback lands back in the tuple determinant chart on the
raw-order source-recursive determinant chart. -/
theorem topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' K}
    (hz : z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) :
    topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') z ∈
      topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
  let E := edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z
  have hsource :
      E ∈ sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
    simpa [topologyTupleRawOrderSourceRecursiveDetChartSet, E] using hz
  have hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) E :=
    (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E).1 hsource
  simpa [topologyTupleEdgeRawOrderInverse, E] using
    (sourceReadback_detChart_of_sourceRecursiveDetChart
      (K := K) (ρ := ρ) E hchart)

/-- On the tuple determinant chart, raw-order readback is a left inverse to the
retained-passive raw-order source map. -/
theorem topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' K}
    (hz : z ∈ topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')) :
    topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z) =
      z := by
  let data := ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z
  have hdet : data.detChart :=
    (mem_topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') z).1 hz
  have hread :
      sourceReadback (K := K) (ρ := ρ)
          (topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z) =
        data := by
    simpa [topologyTupleEdgeMatrix, data] using
      (sourceReadback_edgeMatrix_eq (K := K) (ρ := ρ) (data := data) hdet)
  dsimp [topologyTupleEdgeRawOrderInverse]
  rw [edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder]
  rw [hread]
  simp [data]

/-- On the raw-order source-recursive determinant chart, the retained-passive
raw-order source map is a right inverse to raw-order readback. -/
theorem topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' K}
    (hz : z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) :
    topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') z) =
      z := by
  let E := edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') z
  have hsource :
      E ∈ sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
    simpa [topologyTupleRawOrderSourceRecursiveDetChartSet, E] using hz
  have hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) E :=
    (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E).1 hsource
  have hedge :
      (sourceReadback (K := K) (ρ := ρ) E).edgeMatrix = E :=
    edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
      (K := K) (ρ := ρ) E hchart
  dsimp [topologyTupleEdgeRawOrderInverse, topologyTupleEdgeRawOrder]
  rw [topologyTupleEdgeMatrix_topologyTuple]
  rw [hedge]
  exact edgeFamilyRawOrderTuple_edgeFamilyOfRawOrderTuple
    (K := K) (ρ := ρ) (κ' := κ') z

/-- The image of the tuple determinant chart under the retained-passive
raw-order source map is exactly the raw-order source-recursive determinant
chart. -/
theorem image_topologyTupleEdgeRawOrder_detChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)]
    [∀ j, DecidableEq (κ' j)] :
    topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') ''
        topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') =
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact
      mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') hw
  · intro hz
    refine ⟨topologyTupleEdgeRawOrderInverse
        (K := K) (ρ := ρ) (κ' := κ') z, ?_, ?_⟩
    · exact
        topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') hz
    · exact
        topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
          (K := K) (ρ := ρ) (κ' := κ') hz

/-- Nonredundant retained-passive coordinates carry the product topology on
their matrix fields. -/
instance instTopologicalSpace
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    TopologicalSpace
      (RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :=
  TopologicalSpace.induced topologyTuple inferInstance

/-- Rebuilding retained-passive data from product tuples is continuous for the
induced product topology. -/
theorem continuous_ofTopologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    Continuous
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') :
        TopologyTuple ρ κ' K →
          RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') := by
  apply continuous_induced_rng.2
  change Continuous (fun z : TopologyTuple ρ κ' K ↦ z)
  exact continuous_id

theorem continuous_topologyTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*} [TopologicalSpace K] :
    Continuous
      (topologyTuple :
        RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' →
          TopologyTuple ρ κ' K) := by
  exact continuous_induced_dom

/-- Determinant-chart retained-passive data and determinant-chart topology
tuples are homeomorphic presentations of the same product coordinates. -/
def detChart_topologyTupleDetChartSet_homeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] [CommRing K] [Fintype ρ] [DecidableEq ρ] :
    {data : RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' //
        data.detChart} ≃ₜ
      topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') where
  toFun data :=
    ⟨topologyTuple data.1, by
      simpa using data.2⟩
  invFun z :=
    ⟨ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z.1, z.2⟩
  left_inv data := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  continuous_toFun :=
    ((continuous_topologyTuple (ρ := ρ) (κ' := κ') (K := K)).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K)).comp
      continuous_subtype_val).subtype_mk _

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
theorem continuous_endpointTransport
    {M : ℕ} {ρ K : Type*} {κ κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] (e : ∀ j, κ j ≃ κ' j) :
    Continuous
      (fun data : RetainedPassiveNonredundantCoordinateData
          (K := K) (ρ := ρ) κ ↦ data.endpointTransport e) := by
  have hA1 :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          data.A1passive) := by
    refine continuous_pi ?_
    intro p
    exact continuous_A1passive (K := K) (ρ := ρ) (κ' := κ) p
  have hF2 :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          fun p : Fin (M + 1) ↦
            (data.F2 p).submatrix id (e p.castSucc).symm) := by
    refine continuous_pi ?_
    intro p
    exact
      (continuous_F2 (K := K) (ρ := ρ) (κ' := κ) p).matrix_submatrix
        id (e p.castSucc).symm
  have hA3 :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          fun p : Fin M ↦
            (data.A3passive p).submatrix (e p.castSucc.succ).symm id) := by
    refine continuous_pi ?_
    intro p
    exact
      (continuous_A3passive (K := K) (ρ := ρ) (κ' := κ) p).matrix_submatrix
        (e p.castSucc.succ).symm id
  have hC :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          fun p : Fin (M + 1) ↦
            (data.C p).submatrix (e p.succ).symm (e p.castSucc).symm) := by
    refine continuous_pi ?_
    intro p
    exact
      (continuous_C (K := K) (ρ := ρ) (κ' := κ) p).matrix_submatrix
        (e p.succ).symm (e p.castSucc).symm
  have hCtop :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          data.Ctop) :=
    continuous_Ctop (K := K) (ρ := ρ) (κ' := κ)
  have hF3 :
      Continuous
        (fun data : RetainedPassiveNonredundantCoordinateData
            (K := K) (ρ := ρ) κ ↦
          data.F3.submatrix (e (Fin.last (M + 1))).symm id) :=
    (continuous_F3 (K := K) (ρ := ρ) (κ' := κ)).matrix_submatrix
      (e (Fin.last (M + 1))).symm id
  apply continuous_induced_rng.2
  change Continuous
    (fun data : RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := ρ) κ ↦
      ((data.A1passive),
        ((fun p : Fin (M + 1) ↦
            (data.F2 p).submatrix id (e p.castSucc).symm),
          ((fun p : Fin M ↦
              (data.A3passive p).submatrix (e p.castSucc.succ).symm id),
            ((fun p : Fin (M + 1) ↦
                (data.C p).submatrix (e p.succ).symm (e p.castSucc).symm),
              (data.Ctop,
                data.F3.submatrix (e (Fin.last (M + 1))).symm id))))))
  exact hA1.prodMk (hF2.prodMk (hA3.prodMk (hC.prodMk (hCtop.prodMk hF3))))

theorem continuous_endpointTransport_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] [Fintype ρ] [DecidableEq ρ]
    (e : ∀ j, κ j ≃ κ' j) :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ // data.detChart} ↦
        (⟨data.1.endpointTransport e,
          (endpointTransport_detChart (K := K) (ρ := ρ) e data.1).2 data.2⟩ :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart})) :=
  ((continuous_endpointTransport (K := K) (ρ := ρ) e).comp
    continuous_subtype_val).subtype_mk _

/-- The raw top-left edge block readout is continuous in tuple coordinates. -/
theorem continuous_rawEdgeTupleA1
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] (p : Fin (M + 1)) :
    Continuous
      (fun z : TopologyTuple ρ κ' K ↦
        rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') z p) := by
  cases p using Fin.cases with
  | zero =>
      simpa [rawEdgeTupleA1] using
        (continuous_Ctop (ρ := ρ) (κ' := κ') (K := K)).comp
          (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))
  | succ p =>
      simpa [rawEdgeTupleA1] using
        (continuous_A1passive (ρ := ρ) (κ' := κ') (K := K) p).comp
          (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))

/-- The raw lower-left edge block readout is continuous in tuple coordinates. -/
theorem continuous_rawEdgeTupleA3
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] (p : Fin (M + 1)) :
    Continuous
      (fun z : TopologyTuple ρ κ' K ↦
        rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') z p) := by
  induction p using Fin.lastCases with
  | last =>
      simpa [rawEdgeTupleA3] using
        (continuous_F3 (ρ := ρ) (κ' := κ') (K := K)).comp
          (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))
  | cast p =>
      simpa [rawEdgeTupleA3] using
        (continuous_A3passive (ρ := ρ) (κ' := κ') (K := K) p).comp
          (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))

/-- Reassembling raw-order tuple coordinates into an edge family is
continuous. -/
theorem continuous_edgeFamilyOfRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] :
    Continuous
      (edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') :
        TopologyTuple ρ κ' K → EdgeFamilyTuple ρ κ' K) := by
  refine continuous_pi ?_
  intro p
  have hA1 :
      Continuous
        (fun z : TopologyTuple ρ κ' K ↦
          rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') z p) :=
    continuous_rawEdgeTupleA1 (K := K) (ρ := ρ) (κ' := κ') p
  have hF2 :
      Continuous
        (fun z : TopologyTuple ρ κ' K ↦
          (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).F2 p) :=
    (continuous_F2 (ρ := ρ) (κ' := κ') (K := K) p).comp
      (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))
  have hA3 :
      Continuous
        (fun z : TopologyTuple ρ κ' K ↦
          rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') z p) :=
    continuous_rawEdgeTupleA3 (K := K) (ρ := ρ) (κ' := κ') p
  have hC :
      Continuous
        (fun z : TopologyTuple ρ κ' K ↦
          (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z).C p) :=
    (continuous_C (ρ := ρ) (κ' := κ') (K := K) p).comp
      (continuous_ofTopologyTuple (ρ := ρ) (κ' := κ') (K := K))
  simpa [edgeFamilyOfRawOrderTuple] using hA1.matrix_fromBlocks hF2 hA3 hC

/-- Reading an edge family into raw-order tuple coordinates is continuous. -/
theorem continuous_edgeFamilyRawOrderTuple
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [TopologicalSpace K] :
    Continuous
      (edgeFamilyRawOrderTuple (K := K) (ρ := ρ) (κ' := κ') :
        EdgeFamilyTuple ρ κ' K → TopologyTuple ρ κ' K) := by
  have hA1passive :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦
          fun p : Fin M ↦ (E p.succ).toBlocks₁₁) := by
    refine continuous_pi ?_
    intro p
    have hproj : Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E p.succ) :=
      continuous_apply p.succ
    have hblock :
        Continuous
          (fun A :
              Matrix (ρ ⊕ κ' p.succ.succ) (ρ ⊕ κ' p.succ.castSucc) K ↦
            A.toBlocks₁₁) := by
      simpa [Matrix.toBlocks₁₁] using
        (continuous_id.matrix_submatrix Sum.inl Sum.inl :
          Continuous
            (fun A :
                Matrix (ρ ⊕ κ' p.succ.succ) (ρ ⊕ κ' p.succ.castSucc) K ↦
              A.submatrix Sum.inl Sum.inl))
    exact hblock.comp hproj
  have hF2 :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦
          fun p : Fin (M + 1) ↦ (E p).toBlocks₁₂) := by
    refine continuous_pi ?_
    intro p
    have hproj : Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E p) :=
      continuous_apply p
    have hblock :
        Continuous
          (fun A : Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
            A.toBlocks₁₂) := by
      simpa [Matrix.toBlocks₁₂] using
        (continuous_id.matrix_submatrix Sum.inl Sum.inr :
          Continuous
            (fun A : Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
              A.submatrix Sum.inl Sum.inr))
    exact hblock.comp hproj
  have hA3passive :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦
          fun p : Fin M ↦ (E p.castSucc).toBlocks₂₁) := by
    refine continuous_pi ?_
    intro p
    have hproj : Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E p.castSucc) :=
      continuous_apply p.castSucc
    have hblock :
        Continuous
          (fun A :
              Matrix (ρ ⊕ κ' p.castSucc.succ) (ρ ⊕ κ' p.castSucc.castSucc) K ↦
            A.toBlocks₂₁) := by
      simpa [Matrix.toBlocks₂₁] using
        (continuous_id.matrix_submatrix Sum.inr Sum.inl :
          Continuous
            (fun A :
                Matrix (ρ ⊕ κ' p.castSucc.succ) (ρ ⊕ κ' p.castSucc.castSucc) K ↦
              A.submatrix Sum.inr Sum.inl))
    exact hblock.comp hproj
  have hC :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦
          fun p : Fin (M + 1) ↦ (E p).toBlocks₂₂) := by
    refine continuous_pi ?_
    intro p
    have hproj : Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E p) :=
      continuous_apply p
    have hblock :
        Continuous
          (fun A : Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
            A.toBlocks₂₂) := by
      simpa [Matrix.toBlocks₂₂] using
        (continuous_id.matrix_submatrix Sum.inr Sum.inr :
          Continuous
            (fun A : Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
              A.submatrix Sum.inr Sum.inr))
    exact hblock.comp hproj
  have hCtop :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦ (E 0).toBlocks₁₁) := by
    have hproj : Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E 0) :=
      continuous_apply 0
    have hblock :
        Continuous
          (fun A : Matrix (ρ ⊕ κ' (0 : Fin (M + 1)).succ)
              (ρ ⊕ κ' (0 : Fin (M + 1)).castSucc) K ↦
            A.toBlocks₁₁) := by
      simpa [Matrix.toBlocks₁₁] using
        (continuous_id.matrix_submatrix Sum.inl Sum.inl :
          Continuous
            (fun A : Matrix (ρ ⊕ κ' (0 : Fin (M + 1)).succ)
                (ρ ⊕ κ' (0 : Fin (M + 1)).castSucc) K ↦
              A.submatrix Sum.inl Sum.inl))
    exact hblock.comp hproj
  have hF3 :
      Continuous
        (fun E : EdgeFamilyTuple ρ κ' K ↦ (E (Fin.last M)).toBlocks₂₁) := by
    have hproj :
        Continuous (fun E : EdgeFamilyTuple ρ κ' K ↦ E (Fin.last M)) :=
      continuous_apply (Fin.last M)
    have hblock :
        Continuous
          (fun A : Matrix (ρ ⊕ κ' (Fin.last M).succ)
              (ρ ⊕ κ' (Fin.last M).castSucc) K ↦
            A.toBlocks₂₁) := by
      simpa [Matrix.toBlocks₂₁] using
        (continuous_id.matrix_submatrix Sum.inr Sum.inl :
          Continuous
            (fun A : Matrix (ρ ⊕ κ' (Fin.last M).succ)
                (ρ ⊕ κ' (Fin.last M).castSucc) K ↦
              A.submatrix Sum.inr Sum.inl))
    exact hblock.comp hproj
  change Continuous
    (fun E : EdgeFamilyTuple ρ κ' K ↦
      ((fun p : Fin M ↦ (E p.succ).toBlocks₁₁),
        ((fun p : Fin (M + 1) ↦ (E p).toBlocks₁₂),
          ((fun p : Fin M ↦ (E p.castSucc).toBlocks₂₁),
            ((fun p : Fin (M + 1) ↦ (E p).toBlocks₂₂),
              ((E 0).toBlocks₁₁, (E (Fin.last M)).toBlocks₂₁))))))
  simpa [edgeFamilyRawOrderTuple] using
    hA1passive.prodMk
      (hF2.prodMk
        (hA3passive.prodMk
          (hC.prodMk
            (hCtop.prodMk hF3))))

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

/-- The deterministic source-readback suffix-state fields are continuous at a
base edge family satisfying the recursive determinant-chart predicate. -/
theorem continuousAt_sourceReadbackSuffixState_fields
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (E : α → ∀ p : Fin (M + 1),
      Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K)
    (hE : ContinuousAt E x₀)
    (hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) (E x₀))
    (i : Fin (M + 2)) (hi : i ≤ Fin.last (M + 1)) :
    IsUnit ((sourceReadbackSuffixState (K := K) (ρ := ρ) (E x₀) i hi).Ctop.det) ∧
      ContinuousAt
        (fun x : α ↦
          (sourceReadbackSuffixState (K := K) (ρ := ρ) (E x) i hi).L) x₀ ∧
      ContinuousAt
        (fun x : α ↦
          (sourceReadbackSuffixState (K := K) (ρ := ρ) (E x) i hi).B) x₀ ∧
      ContinuousAt
        (fun x : α ↦
          (sourceReadbackSuffixState (K := K) (ρ := ρ) (E x) i hi).Ctop) x₀ ∧
      ContinuousAt
        (fun x : α ↦
          (sourceReadbackSuffixState (K := K) (ρ := ρ) (E x) i hi).D) x₀ := by
  have hchart' :
      ∀ (p : Fin (M + 1)) (hp : p.succ ≤ Fin.last (M + 1)),
        identityCornerDetChart
          (transformedEdge (E x₀) p
            (suffixState (E x₀) (Fin.last (M + 1)) p.succ hp)) := by
    simpa [sourceRecursiveDetChart] using hchart
  simpa [sourceReadbackSuffixState] using
    (continuousAt_chartLocalSuffixState_suffixState_fields
      (K := K) (ρ := ρ) (κ := κ') E hE
      (j := Fin.last (M + 1)) hchart' i hi)

/-- The transformed edge used by source readback is continuous at a base edge
family satisfying the recursive determinant-chart predicate. -/
theorem continuousAt_sourceReadbackTransformedEdge
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (E : α → ∀ p : Fin (M + 1),
      Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K)
    (hE : ContinuousAt E x₀)
    (hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) (E x₀))
    (p : Fin (M + 1)) :
    ContinuousAt
      (fun x : α ↦
        sourceReadbackTransformedEdge (K := K) (ρ := ρ) (E x) p) x₀ := by
  let S : α → ChartLocalSuffixState ρ κ' K (Fin.last (M + 1)) p.succ :=
    fun x ↦ sourceReadbackSuffixState (K := K) (ρ := ρ) (E x)
      p.succ p.succ.le_last
  have hfields :=
    continuousAt_sourceReadbackSuffixState_fields
      (K := K) (ρ := ρ) (κ' := κ') E hE hchart p.succ p.succ.le_last
  rcases hfields with ⟨_, _hL, hB, _hCtop, _hD⟩
  have hE_p : ContinuousAt (fun x : α ↦ E x p) x₀ :=
    (continuous_apply p).continuousAt.comp hE
  have hleft : ContinuousAt
      (fun x : α ↦
        fromBlocks (1 : Matrix ρ ρ K) (S x).B 0
          (1 : Matrix (κ' p.succ) (κ' p.succ) K)) x₀ := by
    have hfrom : Continuous
        (fun B : Matrix ρ (κ' p.succ) K ↦
          fromBlocks (1 : Matrix ρ ρ K) B 0
            (1 : Matrix (κ' p.succ) (κ' p.succ) K)) :=
      continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
    exact hfrom.continuousAt.comp hB
  have hmul : Continuous
      (fun q :
          Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.succ) K ×
            Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
        q.1 * q.2) :=
    continuous_fst.matrix_mul continuous_snd
  simpa [sourceReadbackTransformedEdge, sourceReadbackSuffixState, S,
    transformedEdge] using
    ContinuousAt.comp₂ hmul.continuousAt hleft hE_p

/-- The source-side readback map is continuous at a base edge family satisfying
the recursive determinant-chart predicate. -/
theorem continuousAt_sourceReadback
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (E : α → ∀ p : Fin (M + 1),
      Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K)
    (hE : ContinuousAt E x₀)
    (hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) (E x₀)) :
    ContinuousAt
      (fun x : α ↦ sourceReadback (K := K) (ρ := ρ) (E x)) x₀ := by
  have hchart' :
      ∀ (p : Fin (M + 1)) (hp : p.succ ≤ Fin.last (M + 1)),
        identityCornerDetChart
          (transformedEdge (E x₀) p
            (suffixState (E x₀) (Fin.last (M + 1)) p.succ hp)) := by
    simpa [sourceRecursiveDetChart] using hchart
  have hA1passive :
      ContinuousAt
        (fun x : α ↦
          (sourceReadback (K := K) (ρ := ρ) (E x)).A1passive) x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    exact continuous_topLeftCorner.continuousAt.comp
      (continuousAt_sourceReadbackTransformedEdge
        (K := K) (ρ := ρ) (κ' := κ') E hE hchart p.succ)
  have hF2 :
      ContinuousAt
        (fun x : α ↦ (sourceReadback (K := K) (ρ := ρ) (E x)).F2) x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    let T : α → Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K :=
      fun x ↦ sourceReadbackTransformedEdge (K := K) (ρ := ρ) (E x) p
    have hT : ContinuousAt T x₀ :=
      continuousAt_sourceReadbackTransformedEdge
        (K := K) (ρ := ρ) (κ' := κ') E hE hchart p
    have htop : ContinuousAt (fun x : α ↦ topLeftCorner (T x)) x₀ :=
      continuous_topLeftCorner.continuousAt.comp hT
    have htopUnit :
        IsUnit ((topLeftCorner (T x₀)).det) := by
      have hchartp := hchart' p p.succ.le_last
      change IsUnit
        ((topLeftCorner
          (transformedEdge (E x₀) p
            (suffixState (E x₀) (Fin.last (M + 1)) p.succ p.succ.le_last))).det) at hchartp
      simpa [T, sourceReadbackTransformedEdge, sourceReadbackSuffixState] using hchartp
    have htopInvBase :
        ContinuousAt (Inv.inv : Matrix ρ ρ K → Matrix ρ ρ K)
          (topLeftCorner (T x₀)) :=
      continuousAt_matrix_inv_of_isUnit_det (A := topLeftCorner (T x₀)) htopUnit
    have htopInv :
        ContinuousAt (fun x : α ↦ (topLeftCorner (T x))⁻¹) x₀ := by
      change ContinuousAt
        ((Inv.inv : Matrix ρ ρ K → Matrix ρ ρ K) ∘
          (fun x : α ↦ topLeftCorner (T x))) x₀
      exact ContinuousAt.comp
        (x := x₀) (f := fun x : α ↦ topLeftCorner (T x))
        (g := Inv.inv) htopInvBase htop
    have hupper : ContinuousAt (fun x : α ↦ upperRightBlock (T x)) x₀ := by
      have hupper' : Continuous
          (fun M : Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
            upperRightBlock M) :=
        continuous_id.matrix_submatrix Sum.inl Sum.inr
      exact hupper'.continuousAt.comp hT
    have hmul : Continuous
        (fun q : Matrix ρ ρ K × Matrix ρ (κ' p.castSucc) K ↦ q.1 * q.2) :=
      continuous_fst.matrix_mul continuous_snd
    have hbody : ContinuousAt
        (fun x : α ↦ (topLeftCorner (T x))⁻¹ * upperRightBlock (T x)) x₀ :=
      ContinuousAt.comp₂ hmul.continuousAt htopInv hupper
    simpa [sourceReadback, T] using hbody.neg
  have hA3passive :
      ContinuousAt
        (fun x : α ↦
          (sourceReadback (K := K) (ρ := ρ) (E x)).A3passive) x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    have hlower : Continuous
        (fun M : Matrix (ρ ⊕ κ' p.castSucc.succ) (ρ ⊕ κ' p.castSucc.castSucc) K ↦
          lowerLeftBlock M) :=
      continuous_id.matrix_submatrix Sum.inr Sum.inl
    exact hlower.continuousAt.comp
      (continuousAt_sourceReadbackTransformedEdge
        (K := K) (ρ := ρ) (κ' := κ') E hE hchart p.castSucc)
  have hC :
      ContinuousAt
        (fun x : α ↦ (sourceReadback (K := K) (ρ := ρ) (E x)).C) x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    have hres :=
      continuousAt_chartLocalSuffixState_residualBlock
        (K := K) (ρ := ρ) (κ := κ') E hE
        (j := Fin.last (M + 1)) hchart' p p.succ.le_last
    simpa [sourceReadback, sourceReadbackTransformedEdge, sourceReadbackSuffixState,
      residualBlock] using hres
  have hfields0 :=
    continuousAt_sourceReadbackSuffixState_fields
      (K := K) (ρ := ρ) (κ' := κ') E hE hchart 0
      (Fin.zero_le (Fin.last (M + 1)))
  rcases hfields0 with ⟨_, hL0, _hB0, hCtop0, _hD0⟩
  have hCtop :
      ContinuousAt
        (fun x : α ↦ (sourceReadback (K := K) (ρ := ρ) (E x)).Ctop) x₀ := by
    simpa [sourceReadback, sourceReadbackSuffixState] using hCtop0
  have hF3 :
      ContinuousAt
        (fun x : α ↦ (sourceReadback (K := K) (ρ := ρ) (E x)).F3) x₀ := by
    have hlower : Continuous
        (fun L :
            Matrix (ρ ⊕ κ' (Fin.last (M + 1)))
              (ρ ⊕ κ' (Fin.last (M + 1))) K ↦
          lowerLeftBlock L) :=
      continuous_id.matrix_submatrix Sum.inr Sum.inl
    simpa [sourceReadback, sourceReadbackSuffixState] using
      hlower.continuousAt.comp hL0
  have htuple :
      ContinuousAt
        (fun x : α ↦
          topologyTuple
            (sourceReadback (K := K) (ρ := ρ) (E x))) x₀ := by
    change ContinuousAt
      (fun x : α ↦
        ((sourceReadback (K := K) (ρ := ρ) (E x)).A1passive,
          ((sourceReadback (K := K) (ρ := ρ) (E x)).F2,
            ((sourceReadback (K := K) (ρ := ρ) (E x)).A3passive,
              ((sourceReadback (K := K) (ρ := ρ) (E x)).C,
                ((sourceReadback (K := K) (ρ := ρ) (E x)).Ctop,
                  (sourceReadback (K := K) (ρ := ρ) (E x)).F3)))))) x₀
    exact hA1passive.prodMk
      (hF2.prodMk
        (hA3passive.prodMk
          (hC.prodMk
            (hCtop.prodMk hF3))))
  rw [ContinuousAt, nhds_induced, Filter.tendsto_comap_iff]
  simpa [Function.comp_def] using htuple

/-- The source-side readback map is continuous on the recursive
determinant-chart subtype. -/
theorem continuous_sourceReadback_sourceRecursiveDetChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun E :
          {E : ∀ p : Fin (M + 1),
              Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K //
            sourceRecursiveDetChart (K := K) (ρ := ρ) E} ↦
        sourceReadback (K := K) (ρ := ρ) E.1) := by
  rw [continuous_iff_continuousAt]
  intro E
  exact
    continuousAt_sourceReadback
      (K := K) (ρ := ρ) (κ' := κ')
      (E := fun E' :
          {E : ∀ p : Fin (M + 1),
              Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K //
            sourceRecursiveDetChart (K := K) (ρ := ρ) E} ↦
        E'.1)
      (x₀ := E) continuous_subtype_val.continuousAt E.2

/-- The retained-passive source map is continuous from the determinant-chart
coordinate subtype to the source-recursive determinant-chart edge subtype. -/
theorem continuous_edgeMatrix_sourceRecursiveDetChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun data :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart} ↦
        (⟨data.1.edgeMatrix,
          sourceRecursiveDetChart_edgeMatrix_of_detChart
            (K := K) (ρ := ρ) data.1 data.2⟩ :
          {E : ∀ p : Fin (M + 1),
              Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K //
            sourceRecursiveDetChart (K := K) (ρ := ρ) E})) := by
  exact
    continuous_edgeMatrix_detChart_subtype
      (ρ := ρ) (κ' := κ') (K := K) |>.subtype_mk _

/-- The source-side readback map is continuous from the source-recursive
determinant-chart edge subtype to the retained-passive determinant-chart
coordinate subtype. -/
theorem continuous_sourceReadback_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun E :
          {E : ∀ p : Fin (M + 1),
              Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K //
            sourceRecursiveDetChart (K := K) (ρ := ρ) E} ↦
        (⟨sourceReadback (K := K) (ρ := ρ) E.1,
          sourceReadback_detChart_of_sourceRecursiveDetChart
            (K := K) (ρ := ρ) E.1 E.2⟩ :
          {data : RetainedPassiveNonredundantCoordinateData
              (K := K) (ρ := ρ) κ' // data.detChart})) := by
  exact
    continuous_sourceReadback_sourceRecursiveDetChart_subtype
      (ρ := ρ) (κ' := κ') (K := K) |>.subtype_mk _

/-- The retained-passive determinant coordinate chart is homeomorphic to its
explicit source-recursive determinant edge chart.

This is a finite topological coordinate statement for the named recursive
source chart.  It does not assert that this chart is the whole source image,
that the source image is open, a rank-coverage theorem, measure transport,
normal crossings, pole order, or RLCT extraction. -/
def detChart_sourceRecursiveDetChart_homeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    {data : RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := ρ) κ' // data.detChart} ≃ₜ
      {E : ∀ p : Fin (M + 1),
          Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K //
        sourceRecursiveDetChart (K := K) (ρ := ρ) E} where
  toFun data :=
    ⟨data.1.edgeMatrix,
      sourceRecursiveDetChart_edgeMatrix_of_detChart
        (K := K) (ρ := ρ) data.1 data.2⟩
  invFun E :=
    ⟨sourceReadback (K := K) (ρ := ρ) E.1,
      sourceReadback_detChart_of_sourceRecursiveDetChart
        (K := K) (ρ := ρ) E.1 E.2⟩
  left_inv data := by
    apply Subtype.ext
    exact sourceReadback_edgeMatrix_eq (K := K) (ρ := ρ) data.1 data.2
  right_inv E := by
    apply Subtype.ext
    exact edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
      (K := K) (ρ := ρ) E.1 E.2
  continuous_toFun :=
    continuous_edgeMatrix_sourceRecursiveDetChart_subtype
      (ρ := ρ) (κ' := κ') (K := K)
  continuous_invFun :=
    continuous_sourceReadback_detChart_subtype
      (ρ := ρ) (κ' := κ') (K := K)

/-- A source-recursive determinant-chart edge family has the source-recursive
chart set as an ambient neighborhood. -/
theorem sourceRecursiveDetChartSet_mem_nhds
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {E : ∀ p : Fin (M + 1),
      Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K}
    (hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) E) :
    sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') ∈ nhds E := by
  let X := ∀ p : Fin (M + 1),
    Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K
  have hlocal :
      {E' : X |
        ∀ p : Fin (M + 1),
          identityCornerDetChart
            (sourceReadbackTransformedEdge (K := K) (ρ := ρ) E' p)} ∈
        nhds E := by
    simpa [Set.setOf_forall] using
      (Filter.iInter_mem.2 fun p : Fin (M + 1) ↦ by
        have hT :
            ContinuousAt
              (fun E' : X ↦
                sourceReadbackTransformedEdge (K := K) (ρ := ρ) E' p) E :=
          continuousAt_sourceReadbackTransformedEdge
            (K := K) (ρ := ρ) (κ' := κ')
            (E := fun E' : X ↦ E') (x₀ := E)
            continuous_id.continuousAt hchart p
        have hdet :
            identityCornerDetChart
              (sourceReadbackTransformedEdge (K := K) (ρ := ρ) E p) :=
          (sourceRecursiveDetChart_iff (K := K) (ρ := ρ) E).1 hchart p
        exact hT.preimage_mem_nhds (identityCornerDetChart_mem_nhds hdet))
  have hset :
      sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') =
        {E' : X |
          ∀ p : Fin (M + 1),
            identityCornerDetChart
              (sourceReadbackTransformedEdge (K := K) (ρ := ρ) E' p)} := by
    ext E'
    exact sourceRecursiveDetChart_iff (K := K) (ρ := ρ) E'
  simpa [hset] using hlocal

/-- The source-recursive determinant-chart set is open in the ambient
edge-family space. -/
theorem isOpen_sourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    IsOpen (sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  rw [isOpen_iff_mem_nhds]
  intro E hchart
  exact sourceRecursiveDetChartSet_mem_nhds (K := K) (ρ := ρ) (κ' := κ') hchart

/-- The raw-order source-recursive determinant chart is open in tuple
coordinates. -/
theorem isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    IsOpen
      (topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) := by
  have hpre :
      (edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')) ⁻¹'
          sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') =
        topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') := by
    rfl
  rw [← hpre]
  exact
    (continuous_edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')).isOpen_preimage
      (sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ'))
      (isOpen_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ'))

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

/-- The retained-passive determinant chart is open in product-tuple
coordinates. -/
theorem isOpen_topologyTupleDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
    [Fintype ρ] [DecidableEq ρ] :
    IsOpen (topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')) := by
  have hpre :
      (ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')) ⁻¹'
          detChartSet (K := K) (ρ := ρ) (κ' := κ') =
        topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
    rfl
  rw [← hpre]
  exact
    (continuous_ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')).isOpen_preimage
      (detChartSet (K := K) (ρ := ρ) (κ' := κ'))
      (isOpen_detChartSet (K := K) (ρ := ρ) (κ' := κ'))

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

/-- The raw-order tuple source map is continuous on the tuple determinant
chart subtype. -/
theorem continuous_topologyTupleEdgeRawOrder_detChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun z :
          topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') ↦
        topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z.1) := by
  let X :=
    topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')
  let Y :=
    {data : RetainedPassiveNonredundantCoordinateData
        (K := K) (ρ := ρ) κ' // data.detChart}
  have hToData :
      Continuous
        (fun z : X ↦
          (⟨ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z.1,
            ((mem_topologyTupleDetChartSet
              (K := K) (ρ := ρ) (κ' := κ') z.1).1 z.2)⟩ : Y)) := by
    have hamb :
        Continuous
          (fun z : X ↦ ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ') z.1) :=
      (continuous_ofTopologyTuple (K := K) (ρ := ρ) (κ' := κ')).comp
        continuous_subtype_val
    exact hamb.subtype_mk _
  have hEdge :
      Continuous
        (fun z : X ↦
          topologyTupleEdgeMatrix (K := K) (ρ := ρ) (κ' := κ') z.1) := by
    have hEdgeData :
        Continuous (fun data : Y ↦ data.1.edgeMatrix) :=
      continuous_edgeMatrix_detChart_subtype (ρ := ρ) (κ' := κ') (K := K)
    simpa [X, Y, topologyTupleEdgeMatrix] using hEdgeData.comp hToData
  exact
    (continuous_edgeFamilyRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')).comp
      hEdge

/-- Raw-order source readback is continuous at every point of the raw-order
source-recursive determinant chart. -/
theorem continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' K}
    (hz : z ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ')) z := by
  let E : TopologyTuple ρ κ' K → EdgeFamilyTuple ρ κ' K :=
    edgeFamilyOfRawOrderTuple (K := K) (ρ := ρ) (κ' := κ')
  have hE : ContinuousAt E z :=
    (continuous_edgeFamilyOfRawOrderTuple
      (K := K) (ρ := ρ) (κ' := κ')).continuousAt
  have hsource : E z ∈
      sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') := by
    simpa [topologyTupleRawOrderSourceRecursiveDetChartSet, E] using hz
  have hchart : sourceRecursiveDetChart (K := K) (ρ := ρ) (E z) :=
    (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') (E z)).1 hsource
  have hread :
      ContinuousAt
        (fun y : TopologyTuple ρ κ' K ↦
          sourceReadback (K := K) (ρ := ρ) (E y)) z :=
    continuousAt_sourceReadback
      (K := K) (ρ := ρ) (κ' := κ') E hE hchart
  exact
    continuous_topologyTuple.continuousAt.comp hread

/-- Raw-order source readback is continuous on the raw-order
source-recursive determinant-chart subtype. -/
theorem continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    Continuous
      (fun z :
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := K) (ρ := ρ) (κ' := κ') ↦
        topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') z.1) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact
    (continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
      (K := K) (ρ := ρ) (κ' := κ') z.2).comp continuous_subtype_val.continuousAt

/-- The tuple determinant chart is homeomorphic to the raw-order encoding of
the source-recursive determinant chart. -/
def topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') ≃ₜ
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') where
  toFun z :=
    ⟨topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z.1,
      mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') z.2⟩
  invFun z :=
    ⟨topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ') z.1,
      topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
        (K := K) (ρ := ρ) (κ' := κ') z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact
      topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
        (K := K) (ρ := ρ) (κ' := κ') z.2
  right_inv z := by
    apply Subtype.ext
    exact
      topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
        (K := K) (ρ := ρ) (κ' := κ') z.2
  continuous_toFun :=
    (continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := K) (ρ := ρ) (κ' := κ')).subtype_mk _
  continuous_invFun :=
    (continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
      (K := K) (ρ := ρ) (κ' := κ')).subtype_mk _

/-- The retained-passive raw-order map as an ambient open partial
homeomorphism from tuple determinant coordinates to the raw-order
source-recursive determinant chart.

This is a topological chart object only; it carries no derivative, Jacobian,
measure, normal-crossing, pole-order, or RLCT assertion. -/
def topologyTupleEdgeRawOrder_openPartialHomeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    OpenPartialHomeomorph (TopologyTuple ρ κ' K) (TopologyTuple ρ κ' K) :=
  let S : Set (TopologyTuple ρ κ' K) :=
    topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' K) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := K) (ρ := ρ) (κ' := κ')
  { toFun := topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ')
    invFun := topologyTupleEdgeRawOrderInverse (K := K) (ρ := ρ) (κ' := κ')
    source := S
    target := T
    map_source' := by
      intro z hz
      exact
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') hz
    map_target' := by
      intro z hz
      exact
        topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') hz
    left_inv' := by
      intro z hz
      exact
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := K) (ρ := ρ) (κ' := κ') hz
    right_inv' := by
      intro z hz
      exact
        topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
          (K := K) (ρ := ρ) (κ' := κ') hz
    open_source := isOpen_topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ')
    open_target :=
      isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := K) (ρ := ρ) (κ' := κ')
    continuousOn_toFun := by
      rw [continuousOn_iff_continuous_restrict]
      change Continuous
        (fun z :
            topologyTupleDetChartSet (K := K) (ρ := ρ) (κ' := κ') ↦
          topologyTupleEdgeRawOrder (K := K) (ρ := ρ) (κ' := κ') z.1)
      exact
        continuous_topologyTupleEdgeRawOrder_detChart_subtype
          (K := K) (ρ := ρ) (κ' := κ')
    continuousOn_invFun := by
      intro z hz
      exact
        (continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
          (K := K) (ρ := ρ) (κ' := κ') hz).continuousWithinAt }

/-- The subtype homeomorphism rewritten with the named ambient chart sets as
its source and target subtypes. -/
def detChartSet_sourceRecursiveDetChartSet_homeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    detChartSet (K := K) (ρ := ρ) (κ' := κ') ≃ₜ
      sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') :=
  let hdet :
      (fun data :
        RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' ↦
          data ∈ detChartSet (K := K) (ρ := ρ) (κ' := κ')) =
        fun data ↦ data.detChart := by
    funext data
    exact propext (mem_detChartSet (K := K) (ρ := ρ) (κ' := κ') data)
  let hsource :
      (fun E : ∀ p : Fin (M + 1),
        Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K ↦
          E ∈ sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')) =
        fun E ↦ sourceRecursiveDetChart (K := K) (ρ := ρ) E := by
    funext E
    exact propext (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E)
  (Homeomorph.ofEqSubtypes hdet).trans
    ((detChart_sourceRecursiveDetChart_homeomorph
      (ρ := ρ) (κ' := κ') (K := K)).trans
        (Homeomorph.ofEqSubtypes hsource).symm)

/-- The retained-passive determinant chart as an ambient open partial
homeomorphism from nonredundant coordinates to source edge families.

The source is exactly `detChartSet`; the target is exactly
`sourceRecursiveDetChartSet`.  This is an explicit local chart object, not a
global source-image or rank-coverage theorem, and it carries no measure,
Jacobian, normal-crossing, pole-order, or RLCT assertion. -/
def detChart_sourceRecursiveDetChart_openPartialHomeomorph
    {M : ℕ} {ρ K : Type*} {κ' : Fin (M + 2) → Type*}
    [NontriviallyNormedField K] [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)] :
    OpenPartialHomeomorph
      (RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ')
      (∀ p : Fin (M + 1),
        Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K) :=
  let S : Set (RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ') :=
    detChartSet (K := K) (ρ := ρ) (κ' := κ')
  let T : Set (∀ p : Fin (M + 1),
      Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K) :=
    sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')
  { toFun := fun data ↦ data.edgeMatrix
    invFun := fun E ↦ sourceReadback (K := K) (ρ := ρ) E
    source := S
    target := T
    map_source' := by
      intro data hdata
      exact
        (mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') data.edgeMatrix).2
          (sourceRecursiveDetChart_edgeMatrix_of_detChart
            (K := K) (ρ := ρ) data
            ((mem_detChartSet (K := K) (ρ := ρ) (κ' := κ') data).1 hdata))
    map_target' := by
      intro E hE
      exact
        (mem_detChartSet (K := K) (ρ := ρ) (κ' := κ')
          (sourceReadback (K := K) (ρ := ρ) E)).2
          (sourceReadback_detChart_of_sourceRecursiveDetChart
            (K := K) (ρ := ρ) E
            ((mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E).1 hE))
    left_inv' := by
      intro data hdata
      exact
        sourceReadback_edgeMatrix_eq (K := K) (ρ := ρ) data
          ((mem_detChartSet (K := K) (ρ := ρ) (κ' := κ') data).1 hdata)
    right_inv' := by
      intro E hE
      exact
        edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
          (K := K) (ρ := ρ) E
          ((mem_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ') E).1 hE)
    open_source := isOpen_detChartSet (K := K) (ρ := ρ) (κ' := κ')
    open_target := isOpen_sourceRecursiveDetChartSet (K := K) (ρ := ρ) (κ' := κ')
    continuousOn_toFun := by
      have hdet :
          (fun data :
            RetainedPassiveNonredundantCoordinateData (K := K) (ρ := ρ) κ' ↦
              data ∈ S) =
            fun data ↦ data.detChart := by
        funext data
        exact propext (mem_detChartSet (K := K) (ρ := ρ) (κ' := κ') data)
      rw [continuousOn_iff_continuous_restrict]
      simpa [S, Set.restrict] using
        (continuous_edgeMatrix_detChart_subtype
          (ρ := ρ) (κ' := κ') (K := K)).comp
          (Homeomorph.ofEqSubtypes hdet).continuous
    continuousOn_invFun := by
      intro E hE
      exact
        (continuousAt_sourceReadback
          (K := K) (ρ := ρ) (κ' := κ')
          (E := fun E' ↦ E') (x₀ := E)
          continuous_id.continuousAt
          ((mem_sourceRecursiveDetChartSet
            (K := K) (ρ := ρ) (κ' := κ') E).1 hE)).continuousWithinAt }

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
