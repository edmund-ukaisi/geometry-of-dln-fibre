import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage

/-!
# Fixed-base product-coordinate source-side measure handoff

This file plugs the reduced p.13 fixed-base product-coordinate chart package
into the generic source-side `withDensity` readback-domination bridge.

The theorem here still assumes the weighted source-side measure identity and
the density bound. It does not prove source/prior measure transport,
determinant/raw Haar transport, normal crossings, pole order, or RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open MeasureTheory
open scoped ENNReal

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Product-coordinate source-side `withDensity` handoff for the reduced p.13
chart.

After shrinking the regular-coordinate radius, the reduced p.13 chart supplies
the continuity, injectivity, measurable-image, and explicit readback hypotheses
needed by the generic source-side `withDensity` readback bridge. The weighted
source-side identity and density bound remain explicit hypotheses. -/
theorem exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readback_le_smul_of_sourceChart_withDensity_of_residualReadback
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α]
    [MeasurableSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [T2Space
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {source : Set α} {Rmax : ℝ}
    (hsource : MeasurableSet source)
    (hRmax : 0 < Rmax)
    (hCedgeBase : ∀ x ∈ source, ContinuousAt CedgeBase x)
    (hchart : ∀ x ∈ source, ∀ (p : Fin (M + 2))
        (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
            (fun q : Fin (M + 2) ↦
              (CedgeBase x q :
                reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ))) p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun q : Fin (M + 2) ↦
                (CedgeBase x q :
                  reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ)))
            (Fin.last (M + 2)) p.succ hpj)))
    (baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) → ℝ) → α)
    (hbaseReadback :
      ∀ x ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) = x) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      let productReadback : EdgeFamily → α × EuclideanSpace ℝ Coord :=
        fun E ↦
          (baseReadback
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E),
            (EuclideanSpace.equiv Coord ℝ).symm
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E))
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure (α × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                (∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E) ∧
                  ∀ (thetaReference : Measure (α × EuclideanSpace ℝ Coord))
                      (externalMeasure : Measure EdgeFamily)
                      (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞)
                      (c : ℝ≥0∞),
                    MeasurableSet chartPiece →
                      AEMeasurable density
                        (Measure.map CedgeProd (thetaReference.restrict domain)) →
                        externalMeasure.restrict chartPiece =
                          (Measure.map CedgeProd
                            ((thetaReference.withDensity
                              (fun z ↦ density (CedgeProd z))).restrict
                              domain)).restrict chartPiece →
                          (∀ᵐ E ∂(Measure.map CedgeProd
                              (thetaReference.restrict domain)).restrict chartPiece,
                            density E ≤ c) →
                            AEMeasurable productReadback
                                (externalMeasure.restrict chartPiece) ∧
                              Measure.map productReadback
                                  (externalMeasure.restrict chartPiece) ≤
                                c • thetaReference.restrict domain := by
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := M) V Bv U₀ hU₀ CedgeBase (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily CedgeProd productReadback domain
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure (α × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [ρ, κ, Coord, EdgeFamily, CedgeProd, productReadback, domain] using hpackage
  rcases hpackage' with ⟨hleft, hinj, hcont, haemeas, himage, hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [ρ, κ, Coord, domain] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  refine ⟨hleft, hinj, hcont, haemeas, himage, hright, ?_⟩
  intro thetaReference externalMeasure chartPiece density c hchartPiece
    hdensity heq hdensity_le
  exact
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_map_sourceChart_withDensity_of_continuousOn_injOn
      CedgeProd productReadback externalMeasure thetaReference domain domain
      chartPiece density c hdomain hchartPiece (fun z hz ↦ hz)
      hcont hinj hleft hdensity heq hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Product-coordinate source-side `withDensity` handoff with a source-domain
density bound.

This variant replaces the image-side a.e. density bound by the pointwise
source-domain bound `density (CedgeProd z) ≤ c` on the returned product
domain.  The weighted source-side identity remains an explicit hypothesis. -/
theorem exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readback_le_smul_of_sourceChart_withDensity_of_forall_density_comp_le_of_residualReadback
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α]
    [MeasurableSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [T2Space
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {source : Set α} {Rmax : ℝ}
    (hsource : MeasurableSet source)
    (hRmax : 0 < Rmax)
    (hCedgeBase : ∀ x ∈ source, ContinuousAt CedgeBase x)
    (hchart : ∀ x ∈ source, ∀ (p : Fin (M + 2))
        (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
            (fun q : Fin (M + 2) ↦
              (CedgeBase x q :
                reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ))) p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun q : Fin (M + 2) ↦
                (CedgeBase x q :
                  reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ)))
            (Fin.last (M + 2)) p.succ hpj)))
    (baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) → ℝ) → α)
    (hbaseReadback :
      ∀ x ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) = x) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      let productReadback : EdgeFamily → α × EuclideanSpace ℝ Coord :=
        fun E ↦
          (baseReadback
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E),
            (EuclideanSpace.equiv Coord ℝ).symm
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := M + 2) V Bv U₀ hU₀
                (fun E' : EdgeFamily ↦ E') E))
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure (α × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                (∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E) ∧
                  ∀ (thetaReference : Measure (α × EuclideanSpace ℝ Coord))
                      (externalMeasure : Measure EdgeFamily)
                      (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞)
                      (c : ℝ≥0∞),
                    MeasurableSet chartPiece →
                      AEMeasurable density
                        (Measure.map CedgeProd (thetaReference.restrict domain)) →
                        externalMeasure.restrict chartPiece =
                          (Measure.map CedgeProd
                            ((thetaReference.withDensity
                              (fun z ↦ density (CedgeProd z))).restrict
                              domain)).restrict chartPiece →
                          (∀ z ∈ domain, density (CedgeProd z) ≤ c) →
                            AEMeasurable productReadback
                                (externalMeasure.restrict chartPiece) ∧
                              Measure.map productReadback
                                  (externalMeasure.restrict chartPiece) ≤
                                c • thetaReference.restrict domain := by
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readback_le_smul_of_sourceChart_withDensity_of_residualReadback
        (M := M) V Bv U₀ hU₀ CedgeBase (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily CedgeProd productReadback domain
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure (α × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                (∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E) ∧
                  ∀ (thetaReference : Measure (α × EuclideanSpace ℝ Coord))
                      (externalMeasure : Measure EdgeFamily)
                      (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞)
                      (c : ℝ≥0∞),
                    MeasurableSet chartPiece →
                      AEMeasurable density
                        (Measure.map CedgeProd (thetaReference.restrict domain)) →
                        externalMeasure.restrict chartPiece =
                          (Measure.map CedgeProd
                            ((thetaReference.withDensity
                              (fun z ↦ density (CedgeProd z))).restrict
                              domain)).restrict chartPiece →
                          (∀ᵐ E ∂(Measure.map CedgeProd
                              (thetaReference.restrict domain)).restrict chartPiece,
                            density E ≤ c) →
                            AEMeasurable productReadback
                                (externalMeasure.restrict chartPiece) ∧
                              Measure.map productReadback
                                  (externalMeasure.restrict chartPiece) ≤
                                c • thetaReference.restrict domain := by
    simpa [ρ, κ, Coord, EdgeFamily, CedgeProd, productReadback, domain] using hpackage
  rcases hpackage' with ⟨hleft, hinj, hcont, haemeas, himage, hright, hbridge⟩
  have hdomain : MeasurableSet domain := by
    simpa [ρ, κ, Coord, domain] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  refine ⟨hleft, hinj, hcont, haemeas, himage, hright, ?_⟩
  intro thetaReference externalMeasure chartPiece density c hchartPiece
    hdensity heq hbound
  have hmap_mem :
      ∀ᵐ E ∂Measure.map CedgeProd (thetaReference.restrict domain),
        E ∈ CedgeProd '' domain := by
    have hpre :
        ∀ᵐ z ∂thetaReference.restrict domain, CedgeProd z ∈ CedgeProd '' domain :=
      (ae_restrict_mem hdomain).mono fun z hz ↦ ⟨z, hz, rfl⟩
    exact (ae_map_iff (haemeas thetaReference) himage).2 hpre
  have hdensity_le :
      ∀ᵐ E ∂(Measure.map CedgeProd (thetaReference.restrict domain)).restrict chartPiece,
        density E ≤ c := by
    filter_upwards [ae_restrict_of_ae hmap_mem] with E hEimage
    rcases hright E hEimage with ⟨hread_domain, hread_eq⟩
    simpa [hread_eq] using hbound (productReadback E) hread_domain
  exact hbridge thetaReference externalMeasure chartPiece density c
    hchartPiece hdensity heq hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Product-coordinate formal-product/source-reference domination for the
reduced p.13 chart.

After shrinking the regular-coordinate radius, a supplied weighted source-side
identity for the actual product-coordinate chart and an image-side local
density bound imply domination by the product-chart source reference
`Measure.map CedgeProd (thetaReference.restrict domain)`.  This proves only
the bounded-density comparison; the weighted identity remains an explicit
hypothesis. -/
theorem exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_formalProductMeasure_restrict_le_smul_sourceReference_of_sourceChart_withDensity_of_residualReadback
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [PolishSpace α]
    [MeasurableSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    [T2Space
      (∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {source : Set α} {Rmax : ℝ}
    (hsource : MeasurableSet source)
    (hRmax : 0 < Rmax)
    (hCedgeBase : ∀ x ∈ source, ContinuousAt CedgeBase x)
    (hchart : ∀ x ∈ source, ∀ (p : Fin (M + 2))
        (hpj : p.succ ≤ (Fin.last (M + 2) : Fin (M + 3))),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
            (fun q : Fin (M + 2) ↦
              (CedgeBase x q :
                reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ))) p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun q : Fin (M + 2) ↦
                (CedgeBase x q :
                  reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ)))
            (Fin.last (M + 2)) p.succ hpj)))
    (baseReadback :
      (AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) → ℝ) → α)
    (hbaseReadback :
      ∀ x ∈ source,
        baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) = x) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin (M + 2), reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      let domain := source ×ˢ Metric.ball (0 : EuclideanSpace ℝ Coord) R
      ∀ (thetaReference : Measure (α × EuclideanSpace ℝ Coord))
          (formalProductMeasure : Measure EdgeFamily)
          (chartPiece : Set EdgeFamily) (density : EdgeFamily → ℝ≥0∞)
          (c : ℝ≥0∞),
        MeasurableSet chartPiece →
          AEMeasurable density
            (Measure.map CedgeProd (thetaReference.restrict domain)) →
          formalProductMeasure.restrict chartPiece =
            (Measure.map CedgeProd
              ((thetaReference.withDensity
                (fun z ↦ density (CedgeProd z))).restrict
                domain)).restrict chartPiece →
          (∀ᵐ E ∂(Measure.map CedgeProd
              (thetaReference.restrict domain)).restrict chartPiece,
            density E ≤ c) →
          formalProductMeasure.restrict chartPiece ≤
            c • Measure.map CedgeProd (thetaReference.restrict domain) := by
  rcases
      exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
        (M := M) V Bv U₀ hU₀ CedgeBase (source := source) (Rmax := Rmax)
        hsource hRmax hCedgeBase hchart baseReadback hbaseReadback with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily CedgeProd domain
  let productReadback : EdgeFamily → α × EuclideanSpace ℝ Coord :=
    fun E ↦
      (baseReadback
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E),
        (EuclideanSpace.equiv Coord ℝ).symm
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀
            (fun E' : EdgeFamily ↦ E') E))
  have hpackage' :
      (∀ z ∈ domain, productReadback (CedgeProd z) = z) ∧
        Set.InjOn CedgeProd domain ∧
          ContinuousOn CedgeProd domain ∧
            (∀ thetaMeasure : Measure (α × EuclideanSpace ℝ Coord),
              AEMeasurable CedgeProd (thetaMeasure.restrict domain)) ∧
              MeasurableSet (CedgeProd '' domain) ∧
                ∀ E ∈ CedgeProd '' domain,
                  productReadback E ∈ domain ∧ CedgeProd (productReadback E) = E := by
    simpa [ρ, κ, Coord, EdgeFamily, CedgeProd, productReadback, domain] using hpackage
  rcases hpackage' with ⟨_hleft, _hinj, _hcont, haemeas, _himage, _hright⟩
  have hdomain : MeasurableSet domain := by
    simpa [ρ, κ, Coord, domain] using
      hsource.prod
        (Metric.isOpen_ball.measurableSet :
          MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ Coord) R))
  intro thetaReference formalProductMeasure chartPiece density c
    hchartPiece hdensity heq hdensity_le
  have hpush :
      Measure.map CedgeProd
          ((thetaReference.withDensity
            (fun z ↦ density (CedgeProd z))).restrict domain) =
        (Measure.map CedgeProd (thetaReference.restrict domain)).withDensity
          density := by
    exact
      measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
        (thetaMeasure := thetaReference) (V := domain)
        (rawMap := CedgeProd)
        (thetaDensity := fun z ↦ density (CedgeProd z))
        (rawDensity := density)
        hdomain (haemeas thetaReference) hdensity
        (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hformal :
      formalProductMeasure.restrict chartPiece =
        ((Measure.map CedgeProd (thetaReference.restrict domain)).withDensity
          density).restrict chartPiece := by
    calc
      formalProductMeasure.restrict chartPiece =
          (Measure.map CedgeProd
            ((thetaReference.withDensity
              (fun z ↦ density (CedgeProd z))).restrict domain)).restrict
            chartPiece := heq
      _ =
          ((Measure.map CedgeProd (thetaReference.restrict domain)).withDensity
            density).restrict chartPiece := by
            rw [hpush]
  calc
    formalProductMeasure.restrict chartPiece =
        ((Measure.map CedgeProd (thetaReference.restrict domain)).withDensity
          density).restrict chartPiece := hformal
    _ ≤ c • Measure.map CedgeProd (thetaReference.restrict domain) := by
        exact
          restrict_withDensity_le_smul_of_ae_le
            (μ := Measure.map CedgeProd (thetaReference.restrict domain))
            (s := chartPiece) (f := density) (c := c)
            hchartPiece hdensity_le

end Aoyagi
end DLN
end DLNFibre

end
