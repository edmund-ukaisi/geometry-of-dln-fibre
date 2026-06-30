import DLNFibre.DLN.Aoyagi.OriginalPrior
import DLNFibre.DLN.Aoyagi.ChainMapTupleBridge
import DLNFibre.DLN.Aoyagi.ChartTopology

/-!
# Original DLN prior on fixed-basis continuous edge families

This file transports the original tuple-coordinate volume/prior from
`Tuple (k := ℝ) d` to a continuous edge-family space
`∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ`, after fixed bases identify each
edge with its matrix.

The construction is independent of Aoyagi source charts.  It does not identify
this measure with a chart-produced source-image measure, prove chart-image
coverage, compare Jacobians, prove normal crossings, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core

variable {N : ℕ}
variable {V : Fin (N + 1) → Type*}
variable [∀ j, AddCommGroup (V j)]
variable [∀ j, TopologicalSpace (V j)]
variable [∀ j, IsTopologicalAddGroup (V j)]
variable [∀ j, T2Space (V j)]
variable [∀ j, Module ℝ (V j)]
variable [∀ j, ContinuousSMul ℝ (V j)]
variable {d : Fin (N + 1) → ℕ}

/-- The core matrix tuple obtained from a continuous edge family by taking
fixed-basis matrices edgewise. -/
def edgeFamilyMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (E : ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :
    Tuple (k := ℝ) d :=
  chainMapMatrixTuple b
    (fun p ↦ (E p : V p.castSucc →ₗ[ℝ] V p.succ))

/-- Fixed-basis matrix coordinates of continuous edge families are
continuous. -/
theorem continuous_edgeFamilyMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Continuous
      (edgeFamilyMatrixTuple (V := V) b :
        (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) → Tuple (k := ℝ) d) := by
  refine continuous_pi ?_
  intro p
  change Continuous
    (fun E : ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ ↦
      LinearMap.toMatrix (b p.castSucc) (b p.succ)
        ((E p : V p.castSucc →L[ℝ] V p.succ) :
          V p.castSucc →ₗ[ℝ] V p.succ))
  exact (continuous_linearMap_toMatrix (b p.castSucc) (b p.succ)).comp
    (continuous_apply p)

/-- Fixed-basis matrix coordinates of continuous edge families are
measurable. -/
theorem measurable_edgeFamilyMatrixTuple
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Measurable
      (edgeFamilyMatrixTuple (V := V) b :
        (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) → Tuple (k := ℝ) d) :=
  (continuous_edgeFamilyMatrixTuple (V := V) b).measurable

variable [∀ j, FiniteDimensional ℝ (V j)]

/-- The continuous edge family represented by a core matrix tuple in fixed
bases. -/
def tupleToEdgeFamily
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (A : Tuple (k := ℝ) d) :
    ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ :=
  fun p ↦
    LinearMap.toContinuousLinearMap
      (Matrix.toLin (b p.castSucc) (b p.succ) (A p))

/-- Matrix coordinates followed by reconstruction are the identity on core
tuples. -/
@[simp] theorem edgeFamilyMatrixTuple_tupleToEdgeFamily
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (A : Tuple (k := ℝ) d) :
    edgeFamilyMatrixTuple (V := V) b (tupleToEdgeFamily (V := V) b A) = A := by
  funext p r c
  simp [edgeFamilyMatrixTuple, tupleToEdgeFamily, chainMapMatrixTuple]

/-- Reconstruction followed by matrix coordinates is the identity on
continuous edge families. -/
@[simp] theorem tupleToEdgeFamily_edgeFamilyMatrixTuple
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (E : ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :
    tupleToEdgeFamily (V := V) b (edgeFamilyMatrixTuple (V := V) b E) = E := by
  funext p
  ext x
  simp [edgeFamilyMatrixTuple, tupleToEdgeFamily, chainMapMatrixTuple]

/-- Reconstructing continuous edge families from fixed-basis matrix tuples is
continuous. -/
theorem continuous_tupleToEdgeFamily
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Continuous
      (tupleToEdgeFamily (V := V) b :
        Tuple (k := ℝ) d → ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) := by
  refine continuous_pi ?_
  intro p
  change Continuous
    (fun A : Tuple (k := ℝ) d ↦
      LinearMap.toContinuousLinearMap
        (Matrix.toLin (b p.castSucc) (b p.succ) (A p)))
  exact (continuous_matrix_toContinuousLinearMap (b p.castSucc) (b p.succ)).comp
    (continuous_apply p)

/-- Reconstructing continuous edge families from fixed-basis matrix tuples is
measurable. -/
theorem measurable_tupleToEdgeFamily
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Measurable
      (tupleToEdgeFamily (V := V) b :
        Tuple (k := ℝ) d → ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :=
  (continuous_tupleToEdgeFamily (V := V) b).measurable

/-- Original coordinate volume on continuous edge families, obtained by
transporting tuple-side original coordinate volume through the fixed-basis
reconstruction map. -/
noncomputable def originalEdgeFamilyVolume
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Measure (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :=
  Measure.map (tupleToEdgeFamily (V := V) b) (originalTupleVolume d)

/-- Pushing edge-family original volume back to fixed-basis matrix coordinates
recovers tuple-side original coordinate volume. -/
theorem originalEdgeFamilyVolume_map_edgeFamilyMatrixTuple
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Measure.map (edgeFamilyMatrixTuple (V := V) b)
        (originalEdgeFamilyVolume (V := V) b) =
      originalTupleVolume d := by
  calc
    Measure.map (edgeFamilyMatrixTuple (V := V) b)
        (originalEdgeFamilyVolume (V := V) b) =
      Measure.map
        ((edgeFamilyMatrixTuple (V := V) b) ∘
          (tupleToEdgeFamily (V := V) b))
        (originalTupleVolume d) := by
        rw [originalEdgeFamilyVolume]
        rw [Measure.map_map
          (measurable_edgeFamilyMatrixTuple (V := V) b)
          (measurable_tupleToEdgeFamily (V := V) b)]
    _ = Measure.map id (originalTupleVolume d) := by
        exact Measure.map_congr
          (Filter.Eventually.of_forall fun A ↦
            edgeFamilyMatrixTuple_tupleToEdgeFamily (V := V) b A)
    _ = originalTupleVolume d := by
        rw [Measure.map_id]

/-- Original prior measure on continuous edge families, with density written
against fixed-basis edge-family original volume. -/
noncomputable def originalEdgeFamilyPrior
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (density : (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) → ℝ) :
    Measure (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :=
  (originalEdgeFamilyVolume (V := V) b).withDensity
    (fun E ↦ ENNReal.ofReal (density E))

/-- A local upper bound on the edge-family prior density gives local
domination by restricted fixed-basis edge-family original volume.  This is
only bounded-density bookkeeping on the original source space; it does not
transport the measure through an Aoyagi source chart. -/
theorem originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) → ℝ}
    {s : Set (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)} {K : ℝ}
    (hs : MeasurableSet s)
    (hdensity :
      ∀ᵐ E ∂(originalEdgeFamilyVolume (V := V) b).restrict s, density E ≤ K) :
    (originalEdgeFamilyPrior (V := V) b density).restrict s ≤
      ENNReal.ofReal K • (originalEdgeFamilyVolume (V := V) b).restrict s :=
  restrict_withDensity_le_smul_restrict_of_ae_le hs
    (hdensity.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

end Aoyagi
end DLN
end DLNFibre

end
