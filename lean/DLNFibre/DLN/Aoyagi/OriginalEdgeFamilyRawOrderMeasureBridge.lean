import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderBridge
import DLNFibre.DLN.Aoyagi.OriginalPriorHaar
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure

/-!
# Raw-order source restrictions in original tuple volume coordinates

This file transports restricted raw-order retained-passive coordinate measures
through the finite raw-order-to-original tuple coordinate equivalence.  The
comparison is by the Haar scalar between the full pushed raw-coordinate Haar
measure and `originalTupleVolume`.

The restriction is not itself asserted to be Haar.  The proof first compares
full ambient Haar measures, then restricts the resulting equality to the image
of the raw source set.

This file also composes the comparison with the existing retained-passive
formal-product Jacobian change-of-variables theorem.  It does not prove an
exact normalization scalar, identify chart-produced source-image measures
with original edge-family volume, prove source-rank coverage, construct normal
crossings, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core
open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

section RawOrderMeasureBridge

variable {M : ℕ}
variable {ρ : Type*}
variable {κ' : Fin (M + 2) → Type*}
variable {d : Fin (M + 2) → ℕ}

/-- Pushing a restricted raw-coordinate Haar measure through the raw-order to
original tuple coordinate equivalence gives the corresponding restriction of
`originalTupleVolume`, up to the full-space Haar scalar.

This is a restriction of a full-space Haar comparison.  It is not a claim that
the restricted raw-source measure is Haar. -/
theorem map_rawOrderMatrixTuple_restrict_eq_smul_originalTupleVolume_restrict_image
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (S : Set (TopologyTuple ρ κ' ℝ)) :
    Measure.map
        (rawOrderMatrixTupleContinuousLinearEquiv
          (ρ := ρ) (κ' := κ') (d := d) e)
        (m.restrict S) =
      ((Measure.map
          (rawOrderMatrixTupleContinuousLinearEquiv
            (ρ := ρ) (κ' := κ') (d := d) e)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalTupleVolume d).restrict
          ((rawOrderMatrixTupleContinuousLinearEquiv
            (ρ := ρ) (κ' := κ') (d := d) e) '' S) := by
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    rawOrderMatrixTupleContinuousLinearEquiv
      (ρ := ρ) (κ' := κ') (d := d) e
  haveI : Measure.IsAddHaarMeasure (Measure.map L m) :=
    L.isAddHaarMeasure_map m
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  haveI :
      ∀ i : Fin (M + 1),
        LocallyCompactSpace
          (Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ) := by
    intro i
    change LocallyCompactSpace
      (Fin (d i.succ) → Fin (d i.castSucc) → ℝ)
    infer_instance
  haveI : LocallyCompactSpace (Tuple (k := ℝ) d) := by
    change LocallyCompactSpace
      (∀ i : Fin (M + 1), Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ)
    infer_instance
  haveI : SecondCountableTopology (Tuple (k := ℝ) d) := by
    change SecondCountableTopology
      (∀ i : Fin (M + 1), Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ)
    infer_instance
  have hfull :
      Measure.map L m =
        (Measure.map L m).addHaarScalarFactor (originalTupleVolume d) •
          originalTupleVolume d :=
    MeasureTheory.Measure.isAddLeftInvariant_eq_smul
      (Measure.map L m) (originalTupleVolume d)
  have hmap_restrict :
      Measure.map L (m.restrict S) =
        (Measure.map L m).restrict (L '' S) := by
    have hrestrict :=
      (L.toHomeomorph.toMeasurableEquiv.restrict_map m (L '' S)).symm
    have hpre : L ⁻¹' (L '' S) = S :=
      Set.preimage_image_eq S L.injective
    simpa [hpre] using hrestrict
  calc
    Measure.map L (m.restrict S) =
        (Measure.map L m).restrict (L '' S) := hmap_restrict
    _ =
        (((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
          originalTupleVolume d).restrict (L '' S) :=
          congrArg (fun μ : Measure (Tuple (k := ℝ) d) ↦ μ.restrict (L '' S)) hfull
    _ =
      ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalTupleVolume d).restrict (L '' S) := by
          rw [Measure.restrict_smul]

set_option linter.style.longLine false in
/-- The retained-passive formal-product Jacobian change of variables,
composed with the raw-order-to-original tuple coordinate readout, lands in
`originalTupleVolume` restricted to the raw source image, up to the full-space
Haar scalar.

This is the honest measure bridge after the raw-order coordinate equivalence:
the scalar is not asserted to be `1`, and no restricted chart measure is
asserted to be Haar. -/
theorem map_formalProduct_rawOrderMatrixTuple_eq_smul_originalTupleVolume_restrict_image
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict
          (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := ρ) (κ' := κ') z))) =
      ((Measure.map
          (rawOrderMatrixTupleContinuousLinearEquiv
            (ρ := ρ) (κ' := κ') (d := d) e)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalTupleVolume d).restrict
          ((rawOrderMatrixTupleContinuousLinearEquiv
            (ρ := ρ) (κ' := κ') (d := d) e) ''
            topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    rawOrderMatrixTupleContinuousLinearEquiv
      (ρ := ρ) (κ' := κ') (d := d) e
  have hψ :
      AEMeasurable
        (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e)
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) :=
    (L.continuous.measurable).aemeasurable
  have hcov :=
    map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart
      (M := M) (ρ := ρ) (κ' := κ') (β := Tuple (k := ℝ) d)
      m (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e) hs hψ
  have hrestrict :=
    map_rawOrderMatrixTuple_restrict_eq_smul_originalTupleVolume_restrict_image
      (ρ := ρ) (κ' := κ') (d := d) m e
      (topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ'))
  simpa [L, rawOrderMatrixTupleContinuousLinearEquiv] using hcov.trans hrestrict

end RawOrderMeasureBridge

end Aoyagi
end DLN
end DLNFibre

end
