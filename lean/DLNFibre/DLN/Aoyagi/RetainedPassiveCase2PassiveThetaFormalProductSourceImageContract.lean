import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage

/-!
# Case 2 formal-product/source-image contract

This file packages the A2 bounded-density socket for comparing Aoyagi's p.13
formal-product chart measure with the concrete Case 2 source-image reference.
It deliberately stores the density identity and density bound as fields.  The
file proves only the measure-theoretic consequences of those fields; it does
not prove the Jacobian calculation, source-image coverage, Haar transport,
normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open MeasureTheory
open scoped ENNReal

/-- A local A2 p.13 formal-product/source-image bounded-density contract.

The intended `sourceChart` is the concrete Case 2 passive-theta endpoint
source chart, and `formalProductMeasure` is the p.13 formal-product chart
measure on edge families.  The record only packages the local chart facts and
the supplied density identity/bound.  It does not assert that the density is
already computed from Aoyagi's Jacobian formula. -/
structure A2Case2FormalProductSourceImagePieceContract
    (Theta E : Type*) [MeasurableSpace Theta] [TopologicalSpace Theta]
    [MeasurableSpace E] [TopologicalSpace E] where
  sourceChart : Theta → E
  readback : E → Theta
  thetaReference : Measure Theta
  V : Set Theta
  chartPiece : Set E
  formalProductMeasure : Measure E
  density : E → ℝ≥0∞
  bound : ℝ≥0∞
  measurable_V : MeasurableSet V
  measurable_chartPiece : MeasurableSet chartPiece
  measurable_image : MeasurableSet (sourceChart '' V)
  chartPiece_subset_image : chartPiece ⊆ sourceChart '' V
  source_contOn : ContinuousOn sourceChart V
  source_injOn : Set.InjOn sourceChart V
  left_inv : ∀ theta ∈ V, readback (sourceChart theta) = theta
  formalProduct_eq_withDensity :
    formalProductMeasure.restrict chartPiece =
      ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
        chartPiece
  density_le_bound :
    ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
      density E ≤ bound

namespace A2Case2FormalProductSourceImagePieceContract

variable {Theta E : Type*} [MeasurableSpace Theta] [TopologicalSpace Theta]
  [MeasurableSpace E] [TopologicalSpace E]

/-- The chart-produced source-image reference attached to the contract. -/
def sourceRef
    (C : A2Case2FormalProductSourceImagePieceContract Theta E) : Measure E :=
  Measure.map C.sourceChart (C.thetaReference.restrict C.V)

/-- The bounded-density contract gives the formal-product/source-image
domination required by the same-shrink original-volume bridge. -/
theorem formalProductMeasure_restrict_le_smul_sourceRef
    (C : A2Case2FormalProductSourceImagePieceContract Theta E) :
    C.formalProductMeasure.restrict C.chartPiece ≤ C.bound • C.sourceRef := by
  calc
    C.formalProductMeasure.restrict C.chartPiece =
        (C.sourceRef.withDensity C.density).restrict C.chartPiece := by
          simpa [sourceRef] using C.formalProduct_eq_withDensity
    _ ≤ C.bound • C.sourceRef := by
          exact restrict_withDensity_le_smul_of_ae_le (μ := C.sourceRef)
            (s := C.chartPiece) (f := C.density) (c := C.bound)
            C.measurable_chartPiece
            (by simpa [sourceRef] using C.density_le_bound)

set_option linter.style.longLine false in
/-- The same contract gives the readback domination used by p.13 readback
finite-integral sockets, after enlarging the theta restriction from `V` to any
containing set `W`. -/
theorem aemeasurable_readback_and_map_readback_restrict_le_smul_thetaReference_restrict
    [BorelSpace Theta] [PolishSpace Theta] [BorelSpace E] [T2Space E]
    (C : A2Case2FormalProductSourceImagePieceContract Theta E)
    {W : Set Theta} (hVW : C.V ⊆ W) :
    AEMeasurable C.readback (C.formalProductMeasure.restrict C.chartPiece) ∧
      Measure.map C.readback (C.formalProductMeasure.restrict C.chartPiece) ≤
        C.bound • C.thetaReference.restrict W := by
  exact
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
      C.sourceChart C.readback C.formalProductMeasure C.thetaReference C.V W
      C.chartPiece C.density C.bound C.measurable_V C.measurable_chartPiece
      hVW C.source_contOn C.source_injOn C.left_inv
      C.formalProduct_eq_withDensity C.density_le_bound

end A2Case2FormalProductSourceImagePieceContract

end Aoyagi
end DLN
end DLNFibre
