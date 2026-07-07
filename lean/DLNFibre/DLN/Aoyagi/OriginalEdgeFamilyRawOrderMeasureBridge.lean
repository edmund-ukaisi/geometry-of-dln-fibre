import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderBridge
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPriorHaar
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

section RawOrderEdgeFamilyMeasureBridge

variable {M : ℕ}
variable {ρ : Type*}
variable {κ' : Fin (M + 2) → Type*}
variable {d : Fin (M + 2) → ℕ}
variable {V : Fin (M + 2) → Type*}
variable [∀ j, AddCommGroup (V j)]
variable [∀ j, TopologicalSpace (V j)]
variable [∀ j, IsTopologicalAddGroup (V j)]
variable [∀ j, T2Space (V j)]
variable [∀ j, Module ℝ (V j)]
variable [∀ j, ContinuousSMul ℝ (V j)]
variable [∀ j, FiniteDimensional ℝ (V j)]

set_option linter.style.longLine false in
/-- Transporting a restricted original tuple volume through fixed-basis edge
family reconstruction gives the corresponding restriction of
`originalEdgeFamilyVolume` to the image.

This is only restriction compatibility for the full-space coordinate
equivalence between tuple coordinates and fixed-basis continuous edge
families. -/
theorem map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (S : Set (Tuple (k := ℝ) d)) :
    Measure.map (tupleToEdgeFamily (V := V) b)
        ((originalTupleVolume d).restrict S) =
      (originalEdgeFamilyVolume (V := V) b).restrict
        ((tupleToEdgeFamily (V := V) b) '' S) := by
  let T : Tuple (k := ℝ) d ≃L[ℝ]
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    (edgeFamilyMatrixTupleContinuousLinearEquiv (V := V) b).symm
  have hrestrict :=
    (T.toHomeomorph.toMeasurableEquiv.restrict_map
      (originalTupleVolume d) (T '' S)).symm
  have hpre : T ⁻¹' (T '' S) = S :=
    Set.preimage_image_eq S T.injective
  have hrestrict' :
      Measure.map T ((originalTupleVolume d).restrict (T ⁻¹' (T '' S))) =
        (Measure.map T (originalTupleVolume d)).restrict (T '' S) := by
    simpa using hrestrict
  rw [hpre] at hrestrict'
  simpa [T, originalEdgeFamilyVolume,
    edgeFamilyMatrixTupleContinuousLinearEquiv, edgeFamilyMatrixTupleLinearEquiv]
    using hrestrict'

set_option linter.style.longLine false in
/-- Transporting a restricted original tuple prior through fixed-basis edge
family reconstruction gives the corresponding restricted edge-family prior.

This is only finite-dimensional fixed-basis prior transport.  It does not
identify an Aoyagi source-chart image measure, compute a retained-passive
Jacobian, normalize Haar scalars, prove source-rank coverage, construct normal
crossings, compute a pole order, or extract an RLCT. -/
theorem map_tupleToEdgeFamily_originalTuplePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : Tuple (k := ℝ) d → ℝ}
    {S : Set (Tuple (k := ℝ) d)}
    (hS : MeasurableSet S)
    (hdensity :
      AEMeasurable (fun A : Tuple (k := ℝ) d ↦ ENNReal.ofReal (density A))
        ((originalTupleVolume d).restrict S)) :
    Measure.map (tupleToEdgeFamily (V := V) b)
        ((originalTuplePrior d density).restrict S) =
      (originalEdgeFamilyPrior (V := V) b
        (fun E ↦ density (edgeFamilyMatrixTuple (V := V) b E))).restrict
        ((tupleToEdgeFamily (V := V) b) '' S) := by
  let T : Tuple (k := ℝ) d ≃L[ℝ]
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    (edgeFamilyMatrixTupleContinuousLinearEquiv (V := V) b).symm
  let edgeDensity :
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) → ℝ≥0∞ :=
    fun E ↦ ENNReal.ofReal (density (edgeFamilyMatrixTuple (V := V) b E))
  have hS_image : MeasurableSet (T '' S) := by
    exact (T.toHomeomorph.toMeasurableEquiv.measurableSet_image).2 hS
  have hcomp_density :
      (fun A : Tuple (k := ℝ) d ↦ edgeDensity (T A)) =
        fun A ↦ ENNReal.ofReal (density A) := by
    funext A
    dsimp [edgeDensity]
    rw [show T A = tupleToEdgeFamily (V := V) b A by
      rfl]
    rw [edgeFamilyMatrixTuple_tupleToEdgeFamily]
  have hleft :
      (originalTuplePrior d density).restrict S =
        ((originalTupleVolume d).restrict S).withDensity
          (fun A ↦ edgeDensity (T A)) := by
    rw [originalTuplePrior, restrict_withDensity hS]
    rw [hcomp_density]
  have hright :
      (originalEdgeFamilyPrior (V := V) b
          (fun E ↦ density (edgeFamilyMatrixTuple (V := V) b E))).restrict
          (T '' S) =
        ((originalEdgeFamilyVolume (V := V) b).restrict (T '' S)).withDensity
          edgeDensity := by
    rw [originalEdgeFamilyPrior, restrict_withDensity hS_image]
  have hT_meas :
      AEMeasurable T ((originalTupleVolume d).restrict S) :=
    T.continuous.measurable.aemeasurable
  have hedgeDensity :
      AEMeasurable edgeDensity
        (Measure.map T ((originalTupleVolume d).restrict S)) := by
    change AEMeasurable edgeDensity
      (Measure.map T.toHomeomorph.toMeasurableEquiv
        ((originalTupleVolume d).restrict S))
    rw [T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.aemeasurable_map_iff]
    change AEMeasurable (fun A : Tuple (k := ℝ) d ↦ edgeDensity (T A))
      ((originalTupleVolume d).restrict S)
    rw [hcomp_density]
    exact hdensity
  have hweighted :
      Measure.map T
          (((originalTupleVolume d).restrict S).withDensity
            (fun A ↦ edgeDensity (T A))) =
        (Measure.map T ((originalTupleVolume d).restrict S)).withDensity
          edgeDensity := by
    exact
      measure_map_withDensity_comp_of_aemeasurable
        (η := (originalTupleVolume d).restrict S)
        (f := T) (g := edgeDensity) hT_meas hedgeDensity
  have hvolume :
      Measure.map T ((originalTupleVolume d).restrict S) =
        (originalEdgeFamilyVolume (V := V) b).restrict (T '' S) := by
    simpa [T, edgeFamilyMatrixTupleContinuousLinearEquiv,
      edgeFamilyMatrixTupleLinearEquiv] using
      map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
        (V := V) b S
  calc
    Measure.map (tupleToEdgeFamily (V := V) b)
        ((originalTuplePrior d density).restrict S) =
        Measure.map T
          (((originalTupleVolume d).restrict S).withDensity
            (fun A ↦ edgeDensity (T A))) := by
          rw [hleft]
          rfl
    _ = (Measure.map T ((originalTupleVolume d).restrict S)).withDensity
          edgeDensity := hweighted
    _ = ((originalEdgeFamilyVolume (V := V) b).restrict (T '' S)).withDensity
          edgeDensity := by rw [hvolume]
    _ = (originalEdgeFamilyPrior (V := V) b
          (fun E ↦ density (edgeFamilyMatrixTuple (V := V) b E))).restrict
          ((tupleToEdgeFamily (V := V) b) '' S) := by
          simpa [T, edgeFamilyMatrixTupleContinuousLinearEquiv,
            edgeFamilyMatrixTupleLinearEquiv] using hright.symm

set_option linter.style.longLine false in
/-- Transporting a restricted original coordinate prior through canonical
entry unflattening and fixed-basis edge-family reconstruction gives the
corresponding restricted edge-family prior.

This is only finite-dimensional coordinate/tuple/edge-family prior transport.
It does not identify an Aoyagi source-chart image measure, compute a
retained-passive Jacobian, normalize Haar scalars, prove source-rank coverage,
construct normal crossings, compute a pole order, or extract an RLCT. -/
theorem map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : (RepCoord d → ℝ) → ℝ}
    {S : Set (RepCoord d → ℝ)}
    (hS : MeasurableSet S)
    (hdensity :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        (Measure.map (canonicalCoord d).symm
          ((originalCoordinateVolume d).restrict S))) :
    Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict S) =
      (originalEdgeFamilyPrior (V := V) b
        (fun E ↦ density
          (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E)))).restrict
        ((fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) '' S) := by
  let C : (RepCoord d → ℝ) ≃ᵐ Tuple (k := ℝ) d :=
    { toEquiv := (canonicalCoord d).symm
      measurable_toFun := measurable_canonicalCoord_symm d
      measurable_invFun := measurable_canonicalCoord d }
  let T : Tuple (k := ℝ) d →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    tupleToEdgeFamily (V := V) b
  let tupleDensity : Tuple (k := ℝ) d → ℝ :=
    fun A ↦ density (canonicalCoord d A)
  have hcoord :
      Measure.map C ((originalCoordinatePrior d density).restrict S) =
        (originalTuplePrior d tupleDensity).restrict (C '' S) := by
    simpa [C, tupleDensity] using
      map_canonicalCoord_symm_originalCoordinatePrior_restrict_eq_originalTuplePrior_restrict_image
        (d := d) (density := density) hS hdensity
  have hS_tuple : MeasurableSet (C '' S) :=
    (C.measurableSet_image).2 hS
  have hcoord_volume :
      Measure.map C ((originalCoordinateVolume d).restrict S) =
        (originalTupleVolume d).restrict (C '' S) := by
    have hrestrict :=
      (C.restrict_map (originalCoordinateVolume d) (C '' S)).symm
    have hpre : C ⁻¹' (C '' S) = S :=
      Set.preimage_image_eq S C.injective
    simpa [hpre, originalTupleVolume, C] using hrestrict
  have hcoord_volume_explicit :
      Measure.map (canonicalCoord d).symm
          ((originalCoordinateVolume d).restrict S) =
        (originalTupleVolume d).restrict (C '' S) := by
    simpa [C] using hcoord_volume
  have htuple_density :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦ ENNReal.ofReal (tupleDensity A))
        ((originalTupleVolume d).restrict (C '' S)) := by
    simpa [hcoord_volume_explicit, tupleDensity] using hdensity
  have hedge :
      Measure.map T ((originalTuplePrior d tupleDensity).restrict (C '' S)) =
        (originalEdgeFamilyPrior (V := V) b
          (fun E ↦ tupleDensity (edgeFamilyMatrixTuple (V := V) b E))).restrict
          (T '' (C '' S)) := by
    simpa [T, tupleDensity] using
      map_tupleToEdgeFamily_originalTuplePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
        (V := V) (d := d) b hS_tuple htuple_density
  calc
    Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict S) =
        Measure.map T (Measure.map C
          ((originalCoordinatePrior d density).restrict S)) := by
          rw [Measure.map_map]
          · rfl
          · exact measurable_tupleToEdgeFamily (V := V) b
          · exact C.measurable
    _ = Measure.map T ((originalTuplePrior d tupleDensity).restrict (C '' S)) := by
          rw [hcoord]
    _ =
        (originalEdgeFamilyPrior (V := V) b
          (fun E ↦ tupleDensity (edgeFamilyMatrixTuple (V := V) b E))).restrict
          (T '' (C '' S)) := hedge
    _ =
      (originalEdgeFamilyPrior (V := V) b
        (fun E ↦ density
          (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E)))).restrict
        ((fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) '' S) := by
          rw [Set.image_image]
          rfl

set_option linter.style.longLine false in
/-- Preimage-restriction form of coordinate-prior transport to fixed-basis
edge families.

The restricted coordinate-side set is the preimage of the target edge-family
set under coordinate unflattening followed by fixed-basis reconstruction, so
the pushed prior is restricted exactly to the target set.  This is still only
finite-dimensional prior transport, not an Aoyagi source-chart prior
identification or a Jacobian/Haar theorem. -/
theorem map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : (RepCoord d → ℝ) → ℝ}
    {Cset : Set (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)}
    (hCset : MeasurableSet Cset)
    (hdensity :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        ((originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' Cset))) :
    Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              Cset)) =
      (originalEdgeFamilyPrior (V := V) b
        (fun E ↦ density
          (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E)))).restrict Cset := by
  let Ccoord : (RepCoord d → ℝ) ≃ᵐ Tuple (k := ℝ) d :=
    { toEquiv := (canonicalCoord d).symm
      measurable_toFun := measurable_canonicalCoord_symm d
      measurable_invFun := measurable_canonicalCoord d }
  let T : Tuple (k := ℝ) d →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    tupleToEdgeFamily (V := V) b
  let F : (RepCoord d → ℝ) →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    fun x ↦ T (Ccoord x)
  have hF_meas : Measurable F :=
    (measurable_tupleToEdgeFamily (V := V) b).comp Ccoord.measurable
  have hScoord : MeasurableSet (F ⁻¹' Cset) :=
    hCset.preimage hF_meas
  have hCcoord_image :
      Ccoord '' (F ⁻¹' Cset) = T ⁻¹' Cset := by
    ext A
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hA
      refine ⟨canonicalCoord d A, ?_, ?_⟩
      · simpa [F, Ccoord] using hA
      · simp [Ccoord]
  have hCcoord_image_explicit :
      ((fun x : RepCoord d → ℝ ↦ (canonicalCoord d).symm x) ''
          (F ⁻¹' Cset)) = T ⁻¹' Cset := by
    simpa [Ccoord] using hCcoord_image
  have hcoord_volume_explicit :
      Measure.map (canonicalCoord d).symm
          ((originalCoordinateVolume d).restrict (F ⁻¹' Cset)) =
        (originalTupleVolume d).restrict (T ⁻¹' Cset) := by
    have hrestrict :=
      (Ccoord.restrict_map (originalCoordinateVolume d)
        (Ccoord '' (F ⁻¹' Cset))).symm
    have hpre : Ccoord ⁻¹' (Ccoord '' (F ⁻¹' Cset)) = F ⁻¹' Cset :=
      Set.preimage_image_eq (F ⁻¹' Cset) Ccoord.injective
    simpa [hpre, hCcoord_image_explicit, originalTupleVolume, Ccoord, T] using hrestrict
  have hdensity_direct :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        (Measure.map (canonicalCoord d).symm
          ((originalCoordinateVolume d).restrict (F ⁻¹' Cset))) := by
    simpa [hcoord_volume_explicit, T] using hdensity
  have hmain :=
    map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
      (V := V) (d := d) b (S := F ⁻¹' Cset) hScoord hdensity_direct
  have hF_image : F '' (F ⁻¹' Cset) = Cset := by
    ext E
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hE
      refine ⟨canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E), ?_, ?_⟩
      · simpa [F, Ccoord, T] using hE
      · simp [F, Ccoord, T]
  calc
    Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              Cset)) =
        (originalEdgeFamilyPrior (V := V) b
          (fun E ↦ density
            (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E)))).restrict
          (F '' (F ⁻¹' Cset)) := by
          simpa [F, Ccoord, T] using hmain
    _ =
      (originalEdgeFamilyPrior (V := V) b
        (fun E ↦ density
          (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E)))).restrict Cset := by
          rw [hF_image]

set_option linter.style.longLine false in
/-- Restricting a pushed coordinate prior to a smaller edge-family chart
piece is the same as pushing the coordinate prior restricted to the preimage of
that chart piece.

This is finite-dimensional transport bookkeeping over the established
coordinate-to-edge-family equivalence.  It does not identify an Aoyagi source
chart measure, construct source-image densities, prove Haar transport, normal
crossings, pole order, or RLCT. -/
theorem map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_restrict_eq_restrict_preimage_of_subset
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : (RepCoord d → ℝ) → ℝ}
    {Cset chartPiece : Set
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)}
    (hCset : MeasurableSet Cset)
    (hchartPiece : MeasurableSet chartPiece)
    (hsubset : chartPiece ⊆ Cset)
    (hdensity :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        ((originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' Cset))) :
    (Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              Cset))).restrict chartPiece =
      Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              chartPiece)) := by
  let edgeDensity :
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) → ℝ :=
    fun E ↦ density
      (canonicalCoord d (edgeFamilyMatrixTuple (V := V) b E))
  let toEdge : (RepCoord d → ℝ) →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    fun x ↦ tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)
  have hpre_subset :
      (tupleToEdgeFamily (V := V) b) ⁻¹' chartPiece ⊆
        (tupleToEdgeFamily (V := V) b) ⁻¹' Cset := by
    intro A hA
    exact hsubset hA
  have hrestrict_le :
      (originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' chartPiece) ≤
        (originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' Cset) :=
    Measure.restrict_mono hpre_subset le_rfl
  have hdensity_piece :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        ((originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' chartPiece)) :=
    hdensity.mono_ac (Measure.absolutelyContinuous_of_le hrestrict_le)
  have hbig :
      Measure.map toEdge
          ((originalCoordinatePrior d density).restrict (toEdge ⁻¹' Cset)) =
        (originalEdgeFamilyPrior (V := V) b edgeDensity).restrict Cset := by
    simpa [toEdge, edgeDensity] using
      map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict
        (V := V) (d := d) b (density := density) (Cset := Cset)
        hCset hdensity
  have hsmall :
      Measure.map toEdge
          ((originalCoordinatePrior d density).restrict
            (toEdge ⁻¹' chartPiece)) =
        (originalEdgeFamilyPrior (V := V) b edgeDensity).restrict
          chartPiece := by
    simpa [toEdge, edgeDensity] using
      map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict
        (V := V) (d := d) b (density := density) (Cset := chartPiece)
        hchartPiece hdensity_piece
  calc
    (Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              Cset))).restrict chartPiece =
        ((originalEdgeFamilyPrior (V := V) b edgeDensity).restrict Cset).restrict
          chartPiece := by
          simpa [toEdge] using congrArg (fun μ ↦ μ.restrict chartPiece) hbig
    _ =
        (originalEdgeFamilyPrior (V := V) b edgeDensity).restrict chartPiece := by
          exact Measure.restrict_restrict_of_subset hsubset
    _ =
        Measure.map
          (fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
          ((originalCoordinatePrior d density).restrict
            ((fun x : RepCoord d → ℝ ↦
              tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
                chartPiece)) := by
          simpa [toEdge] using hsmall.symm

set_option linter.style.longLine false in
/-- A finite product integral over a pushed coordinate prior restricted after
mapping transfers to the directly restricted coordinate prior on the chart
piece.

This is the integral form of
`map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_restrict_eq_restrict_preimage_of_subset`.
It is finite-dimensional measure bookkeeping and carries no analytic
normal-crossing or RLCT content. -/
theorem lintegral_prod_map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_chartPiece_lt_top_of_lintegral_prod_restrict_preimage_superset_restrict_chartPiece_lt_top
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    {density : (RepCoord d → ℝ) → ℝ}
    {Cset chartPiece : Set
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)}
    (hCset : MeasurableSet Cset)
    (hchartPiece : MeasurableSet chartPiece)
    (hsubset : chartPiece ⊆ Cset)
    (hdensity :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        ((originalTupleVolume d).restrict
          ((tupleToEdgeFamily (V := V) b) ⁻¹' Cset)))
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {F :
      ((∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) × β) →
        ℝ≥0∞}
    (hfinite :
      (∫⁻ z, F z ∂
        (((Measure.map
          (fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
          ((originalCoordinatePrior d density).restrict
            ((fun x : RepCoord d → ℝ ↦
              tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
                Cset))).restrict chartPiece).prod ν)) < ∞) :
    (∫⁻ z, F z ∂
      ((Measure.map
        (fun x : RepCoord d → ℝ ↦
          tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x))
        ((originalCoordinatePrior d density).restrict
          ((fun x : RepCoord d → ℝ ↦
            tupleToEdgeFamily (V := V) b ((canonicalCoord d).symm x)) ⁻¹'
              chartPiece))).prod ν)) < ∞ := by
  have hmeasure :=
    map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_restrict_eq_restrict_preimage_of_subset
      (V := V) (d := d) b (density := density) (Cset := Cset)
      (chartPiece := chartPiece) hCset hchartPiece hsubset hdensity
  simpa [hmeasure] using hfinite

set_option linter.style.longLine false in
/-- Pushing a restricted raw-coordinate Haar measure through the raw-order
readout and then reconstructing fixed-basis continuous edge families gives the
corresponding restriction of `originalEdgeFamilyVolume`, up to the same
full-space Haar scalar as the tuple-coordinate comparison.

The scalar is not asserted to be `1`, and no restricted source/image measure
is asserted to be Haar. -/
theorem map_rawOrderMatrixTuple_tupleToEdgeFamily_restrict_eq_smul_originalEdgeFamilyVolume_restrict_image
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (S : Set (TopologyTuple ρ κ' ℝ)) :
    Measure.map
        (fun y : TopologyTuple ρ κ' ℝ =>
          tupleToEdgeFamily (V := V) b
            (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y))
        (m.restrict S) =
      ((Measure.map
          (rawOrderMatrixTupleContinuousLinearEquiv
            (ρ := ρ) (κ' := κ') (d := d) e)
          m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := V) b).restrict
          ((fun y : TopologyTuple ρ κ' ℝ =>
            tupleToEdgeFamily (V := V) b
              (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y)) '' S) := by
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    rawOrderMatrixTupleContinuousLinearEquiv
      (ρ := ρ) (κ' := κ') (d := d) e
  let T : Tuple (k := ℝ) d →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    tupleToEdgeFamily (V := V) b
  have hraw :=
    map_rawOrderMatrixTuple_restrict_eq_smul_originalTupleVolume_restrict_image
      (ρ := ρ) (κ' := κ') (d := d) m e S
  have htuple :=
    map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
      (V := V) (d := d) b (L '' S)
  calc
    Measure.map
        (fun y : TopologyTuple ρ κ' ℝ =>
          tupleToEdgeFamily (V := V) b
            (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y))
        (m.restrict S) =
        Measure.map T (Measure.map L (m.restrict S)) := by
          rw [Measure.map_map]
          · rfl
          · exact measurable_tupleToEdgeFamily (V := V) b
          · exact L.continuous.measurable
    _ =
        Measure.map T
          (((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
            (originalTupleVolume d).restrict (L '' S)) := by
          rw [hraw]
    _ =
        ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
          Measure.map T ((originalTupleVolume d).restrict (L '' S)) := by
          rw [Measure.map_smul]
    _ =
        ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
          (originalEdgeFamilyVolume (V := V) b).restrict (T '' (L '' S)) := by
          rw [htuple]
    _ =
      ((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
        (originalEdgeFamilyVolume (V := V) b).restrict
          ((fun y : TopologyTuple ρ κ' ℝ =>
            tupleToEdgeFamily (V := V) b
              (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y)) '' S) := by
          rw [Set.image_image]
          rfl

set_option linter.style.longLine false in
/-- The retained-passive formal-product Jacobian change of variables,
composed with the raw-order-to-original tuple readout and fixed-basis
edge-family reconstruction, lands in `originalEdgeFamilyVolume` restricted to
the raw source image, up to the full-space Haar scalar.

This is still a restricted-pushforward scalar comparison, not a restricted
Haar theorem and not a scalar normalization theorem. -/
theorem map_formalProduct_rawOrderMatrixTuple_tupleToEdgeFamily_eq_smul_originalEdgeFamilyVolume_restrict_image
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [OpensMeasurableSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          tupleToEdgeFamily (V := V) b
            (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)))
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
        (originalEdgeFamilyVolume (V := V) b).restrict
          ((fun y : TopologyTuple ρ κ' ℝ =>
            tupleToEdgeFamily (V := V) b
              (rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y)) ''
            topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  let L : TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d :=
    rawOrderMatrixTupleContinuousLinearEquiv
      (ρ := ρ) (κ' := κ') (d := d) e
  let ψ : TopologyTuple ρ κ' ℝ →
      (∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ) :=
    fun y ↦ tupleToEdgeFamily (V := V) b (rawOrderMatrixTuple e y)
  have hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) :=
    ((continuous_tupleToEdgeFamily (V := V) b).comp L.continuous).aemeasurable
  have hcov :=
    map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart
      (M := M) (ρ := ρ) (κ' := κ')
      (β := ∀ p : Fin (M + 1), V p.castSucc →L[ℝ] V p.succ)
      m ψ hs hψ
  have hrestrict :=
    map_rawOrderMatrixTuple_tupleToEdgeFamily_restrict_eq_smul_originalEdgeFamilyVolume_restrict_image
      (ρ := ρ) (κ' := κ') (d := d) (V := V) m e b
      (topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ'))
  simpa [L, ψ, rawOrderMatrixTupleContinuousLinearEquiv] using
    hcov.trans hrestrict

end RawOrderEdgeFamilyMeasureBridge

end Aoyagi
end DLN
end DLNFibre

end
