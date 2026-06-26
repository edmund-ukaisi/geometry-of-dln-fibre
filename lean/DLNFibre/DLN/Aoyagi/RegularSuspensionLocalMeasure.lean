import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.MonomialChartIntegrability
import DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Local a.e. handoffs for p. 13 regular-suspension source comparisons

This file packages source-neighborhood p. 13 square-sum comparisons as
restricted-measure a.e. facts.  It also composes supplied local product
loss/density and residual integrability hypotheses with the finite-side p. 13
regular-coordinate adapter.  It does not construct Aoyagi's p. 13 product
chart, identify the auxiliary product fiber with regular coordinates, compare
an original DLN loss, transport density/Jacobian factors, prove the residual
base hypotheses, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

section FixedBaseRealLocalMeasure

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Source-data-level extraction of a measurable local source from the fixed-base
regular-coordinate certificate.

The returned `source` is an open-neighborhood shrink intersected with Aoyagi's
source-rank stratum.  The final filter equality records that source-stratum
local statements may be reused on this local source.  This is source packaging
only: it does not construct a chart, pushforward identity, Jacobian density, or
normal-crossing data. -/
theorem exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) :
    ∃ source U : Set α,
      U ∈ nhds x₀ ∧ IsOpen U ∧ x₀ ∈ U ∧
      source =
        U ∩ paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge ∧
      MeasurableSet source ∧
      x₀ ∈ source ∧
      source ⊆ paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge ∧
      (∀ x, x ∈ source →
        PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
          (K := ℝ) W B U₀ hU₀ Cedge r rEdge x) ∧
      nhdsWithin x₀ source =
        nhdsWithin x₀
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge) := by
  classical
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hsource_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_measurable_edgeMatrix
        (W := W) (B := B) U₀ hU₀
        (Cedge := Cedge) (r := r) (rEdge := rEdge) hEdgeMatrix
  rcases
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (r := r) (rEdge := rEdge)
      sourceData.localSourceCertificate
      (by simpa [sourceStratum] using hsource_meas) with
    ⟨source, U, hUnhds, hUopen, hxU, hsource_eq,
      hsource_meas', hxsource, hsubset, hsourceRanks⟩
  refine ⟨source, U, hUnhds, hUopen, hxU, hsource_eq,
    hsource_meas', hxsource, hsubset, hsourceRanks, ?_⟩
  rw [hsource_eq]
  simpa [sourceStratum] using
    nhdsWithin_inter_of_mem (a := x₀) (s := U) (t := sourceStratum)
      (mem_nhdsWithin_of_mem_nhds hUnhds)

set_option linter.unusedSectionVars false in
/-- Local-source version of the explicit self-base multi-edge product-family
adapted lower bound.

This packages the source-data measurable local source with the existing p.13
product-coordinate lower bound.  The lower bound is transported from the full
source-rank stratum to the returned local source using the `nhdsWithin`
equality.  No chart image, pushforward, Jacobian/source-density identity, or
monomial-unit data is constructed here. -/
theorem exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let Coord :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    ∃ source sourceU : Set α, ∃ R c : ℝ,
      sourceU ∈ nhds x₀ ∧ IsOpen sourceU ∧ x₀ ∈ sourceU ∧
      source = sourceU ∩ sourceStratum ∧
      MeasurableSet source ∧ x₀ ∈ source ∧ source ⊆ sourceStratum ∧
      (∀ x, x ∈ source →
        PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase r rEdge x) ∧
      nhdsWithin x₀ source = nhdsWithin x₀ sourceStratum ∧
      0 < R ∧ R ≤ Rmax ∧ 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
  classical
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let Coord :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  rcases
      exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix
        (W := V) (B := Bv) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeBase) (H := H) (r := r) (rEdge := rEdge)
        sourceData hEdgeMatrix with
    ⟨source, sourceU, hsourceU_nhds, hsourceU_open, hxsourceU, hsource_eq,
      hsource_meas, hxsource, hsource_subset, hsourceRanks, hnhds_source⟩
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ CedgeBase
        hCedgeBase hbase (r := r) (rEdge := rEdge) (Rmax := Rmax) hRmax with
    ⟨R, c, hR, hR_le_Rmax, hc, hlower⟩
  have hlower_source :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) := by
    simpa [Coord, CedgeProd, sourceStratum, hnhds_source] using hlower
  exact
    ⟨source, sourceU, R, c, hsourceU_nhds, hsourceU_open, hxsourceU,
      by simpa [sourceStratum] using hsource_eq,
      hsource_meas, hxsource, by simpa [sourceStratum] using hsource_subset,
      by simpa [sourceStratum] using hsourceRanks,
      by simpa [sourceStratum] using hnhds_source,
      hR, hR_le_Rmax, hc, by simpa [Coord, CedgeProd] using hlower_source⟩

set_option linter.unusedSectionVars false in
/-- The source-stratum half lower bound becomes an a.e. lower bound after
restricting any base measure to a sufficiently small measurable source
neighborhood. -/
theorem exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict
          (U ∩ paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        (1 / 2 : ℝ) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    exists_open_ae_restrict_inter_of_eventually_nhdsWithin
      (μ := μ) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of
`exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le`.
The asserted comparison is still only a property of the base/source coordinate
`z.1`. -/
theorem exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {ν : Measure β}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ z : α × β ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        (1 / 2 : ℝ) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) := by
  exact
    exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- A supplied local lower bound of a base loss by the literal p. 13 square-sum
becomes an a.e. lower bound by the regular-plus-residual cleaned square-sum
after restricting to a small measurable source neighborhood. -/
theorem exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {loss : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤ loss x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict
          (U ∩ paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤ loss x := by
  exact
    exists_open_ae_restrict_inter_of_eventually_nhdsWithin
      (μ := μ) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
        (W := W) (B := B) sourceData hc hloss)

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of the supplied base-loss handoff.
The loss here is still a base function `loss z.1`; this does not identify an
auxiliary product fiber with p. 13 regular coordinates. -/
theorem exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {ν : Measure β} {loss : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤ loss x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ z : α × β ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤ loss z.1 := by
  exact
    exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
        (W := W) (B := B) sourceData hc hloss)

set_option linter.unusedSectionVars false in
/-- At a continuous fixed-base paper chain, the adapted fixed-base
product-difference comparison becomes an a.e. lower bound after restricting to
a small measurable source neighborhood.

The right-hand side is the adapted fixed-base product-difference square-sum,
not the original DLN/statistical loss. -/
theorem exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ c : ℝ, 0 < c ∧
      ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
        ∀ᵐ x ∂ μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge),
          (c / 2) *
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseRegularBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ Cedge x := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
        (W := W) (B := B) sourceData hCedge hbase with
    ⟨c, hc_pos, hbound⟩
  rcases
      exists_open_ae_restrict_inter_of_eventually_nhdsWithin
        (μ := μ) (x₀ := x₀)
        (s := paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge)
        hsource_meas hbound with
    ⟨U, hUopen, hx₀U, hUbound⟩
  exact ⟨c, hc_pos, U, hUopen, hx₀U, hUbound⟩

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of the self-base adapted
product-difference local-measure handoff.  The asserted comparison is only a
property of the base/source coordinate `z.1`. -/
theorem exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α} {ν : Measure β}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ c : ℝ, 0 < c ∧
      ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
        ∀ᵐ z : α × β ∂
            (μ.restrict
              (U ∩ paperEndpointFixedBaseSourceRankStratum
                (K := ℝ) W B Cedge r rEdge)).prod ν,
          (c / 2) *
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseRegularBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge z.1) +
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ Cedge z.1 := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
        (W := W) (B := B) sourceData hCedge hbase with
    ⟨c, hc_pos, hbound⟩
  rcases
      exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
        (μ := μ) (ν := ν) (x₀ := x₀)
        (s := paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge)
        hsource_meas hbound with
    ⟨U, hUopen, hx₀U, hUbound⟩
  exact ⟨c, hc_pos, U, hUopen, hx₀U, hUbound⟩

set_option linter.unusedSectionVars false in
/-- Uniform-in-fiber source-filter bounds become product-measure a.e. bounds
after restricting the base to a sufficiently small measurable source
neighborhood.

This is the handoff shape expected by the finite-side p.13 regular-coordinate
integrability adapter for its loss and density hypotheses.  It does not prove
those source-filter bounds, residual positivity, residual negative-power
integrability, or any product chart/density transport theorem. -/
theorem exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {R c C : ℝ}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum (fun i => z.2 i)) ≤ loss z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          0 ≤ density z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          density z ≤ C) := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hbounds :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            0 ≤ density (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            density (x, u) ≤ C) := by
    filter_upwards [hloss, hdensity_nonneg, hdensity_le] with x hxloss hxdensity_nonneg
      hxdensity_le
    exact ⟨by simpa [ρ, sourceStratum] using hxloss,
      by simpa [ρ, sourceStratum] using hxdensity_nonneg,
      by simpa [ρ, sourceStratum] using hxdensity_le⟩
  rcases exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀) (s := sourceStratum)
      (by simpa [sourceStratum] using hsource_meas) hbounds with
    ⟨U, hUopen, hxU, hbounds_ae⟩
  refine ⟨U, hUopen, hxU, ?_, ?_, ?_⟩
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.2 z.2 hzball

set_option linter.unusedSectionVars false in
/-- Source-local version of
`exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds`.

The source set is supplied explicitly, rather than fixed to the full
source-rank stratum.  This is the handoff needed by genuinely local source
charts: a bound holding in `nhdsWithin x₀ source` becomes an a.e. product-measure
bound after restricting to `U ∩ source`. -/
theorem exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α}
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {R c C : ℝ}
    (hsource_meas : MeasurableSet source)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict (U ∩ source)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum (fun i => z.2 i)) ≤ loss z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict (U ∩ source)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          0 ≤ density z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict (U ∩ source)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          density z ≤ C) := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hbounds :
      ∀ᶠ x in nhdsWithin x₀ source,
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            0 ≤ density (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            density (x, u) ≤ C) := by
    filter_upwards [hloss, hdensity_nonneg, hdensity_le] with x hxloss hxdensity_nonneg
      hxdensity_le
    exact ⟨by simpa [ρ] using hxloss,
      by simpa [ρ] using hxdensity_nonneg,
      by simpa [ρ] using hxdensity_le⟩
  rcases exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀) (s := source) hsource_meas hbounds with
    ⟨U, hUopen, hxU, hbounds_ae⟩
  refine ⟨U, hUopen, hxU, ?_, ?_, ?_⟩
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.2 z.2 hzball

set_option linter.unusedSectionVars false in
/-- Finite residual negative-power integral over a supplied base set.  This is
only a notation wrapper for the base-side integrability hypothesis consumed by
the p. 13 regular-coordinate finite-side adapter. -/
def residualNegPowerIntegrableOn
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (source : Set α) (μ : Measure α) (t : ℝ) : Prop :=
  (∫⁻ x : α, ENNReal.ofReal
    ((aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))
      ∂ (μ.restrict source)) < ∞

set_option linter.unusedSectionVars false in
/-- The residual square-sum is positive a.e. once its zero locus is null for
the restricted source measure. -/
theorem residualSquareSum_pos_ae_of_zero_set_null
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    (hzero :
      (μ.restrict source)
        {x | aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) = 0} = 0) :
    ∀ᵐ x ∂ μ.restrict source,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
      (μ := μ.restrict source)
      (f := fun x =>
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
      (fun x =>
        aoyagiCoordinateSquareSum_nonneg
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
      hzero

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability restrict to smaller
source sets. -/
theorem residualSourceHypotheses_mono
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source source' : Set α} {μ : Measure α} {t : ℝ}
    (hsubset : source' ⊆ source)
    (hpos :
      ∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase : residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t) :
    (∀ᵐ x ∂ μ.restrict source',
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source' μ t := by
  constructor
  · exact ae_mono (Measure.restrict_mono hsubset le_rfl) hpos
  · exact
      (lintegral_mono'
        (Measure.restrict_mono hsubset le_rfl)
        (le_refl (fun x : α => ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))))).trans_lt
        (by simpa [residualNegPowerIntegrableOn] using hbase)

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability on a smaller source set
from residual negative-power integrability on a larger source set and nullity of
the residual zero locus there. -/
theorem residualSourceHypotheses_mono_of_zero_set_null
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source source' : Set α} {μ : Measure α} {t : ℝ}
    (hsubset : source' ⊆ source)
    (hzero :
      (μ.restrict source)
        {x | aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) = 0} = 0)
    (hbase : residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t) :
    (∀ᵐ x ∂ μ.restrict source',
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source' μ t := by
  exact
    residualSourceHypotheses_mono
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (source' := source')
      (μ := μ) (t := t) hsubset
      (residualSquareSum_pos_ae_of_zero_set_null
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := source) (μ := μ) hzero)
      hbase

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability from an explicitly
supplied source-measure pushforward.

This is only measure-transport plumbing.  The chart map, the equality
`μ.restrict source = Measure.map chart ν`, residual positivity after pulling
back along the chart, and chart-side residual integrability are all supplied. -/
theorem residualSourceHypotheses_of_measure_map
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α} {ν : Measure β} {chart : β → α} {t : ℝ}
    (hchart : AEMeasurable chart ν)
    (hmap : μ.restrict source = Measure.map chart ν)
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hpos_chart :
      ∀ᵐ y ∂ ν,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hbase_chart :
      (∫⁻ y : β, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t)) ∂ ν) < ∞) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  constructor
  · have hpos_map :
        ∀ᵐ x ∂ Measure.map chart ν,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) :=
      (ae_map_iff hchart hpos_meas).2 hpos_chart
    simpa [hmap] using hpos_map
  · have hle :
        (∫⁻ x : α, ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))
            ∂ Measure.map chart ν) ≤
          (∫⁻ y : β, ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t)) ∂ ν) := by
      exact lintegral_map_le
        (fun x : α => ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t)))
        chart
    exact lt_of_le_of_lt (by simpa [residualNegPowerIntegrableOn, hmap] using hle) hbase_chart

set_option linter.unusedSectionVars false in
/-- Residual source hypotheses from a signed-box chart pushforward and an
explicit absolute-monomial lower bound on the chart-side residual square.

This is an unweighted signed-box source-measure constructor.  It does not
construct the chart, prove the source-measure pushforward identity, transport a
Jacobian/density factor, compare the original DLN loss, or extract an RLCT. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_monomialLower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {t c : ℝ} {R : ι → ℝ} {k : ι → ℕ}
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hc : 0 < c) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  let signedBox : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  have hpos_chart :
      ∀ᵐ y ∂ signedBox,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)) := by
    have hcoord : ∀ᵐ y : ι → ℝ ∂ signedBox, ∀ i, 0 < |y i| := by
      dsimp [signedBox]
      exact ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := ι)
    filter_upwards [hcoord, hlower] with y hyabs hylower
    have hmonomial_pos :
        0 < ∏ i, (|y i|) ^ (2 * (k i : ℝ)) := by
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hyabs i) _
    exact lt_of_lt_of_le (mul_pos hc hmonomial_pos) hylower
  have hbase_chart :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t))
          ∂ signedBox) < ∞ := by
    dsimp [signedBox]
    exact
      lintegral_ofReal_loss_rpow_neg_signedBox_lt_top
        (k := k) (t := t) (R := R) (c := c)
        (loss := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
        hc ht hR hcrit hlower
  exact
    residualSourceHypotheses_of_measure_map
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (ν := signedBox) (chart := chart) (t := t)
      (by simpa [signedBox] using hchart)
      (by simpa [signedBox] using hmap)
      hpos_meas hpos_chart hbase_chart

set_option linter.unusedSectionVars false in
/-- Monomial-times-bounded-unit data on a signed box gives the residual lower
bound and source-density bounds consumed by the weighted signed-box residual
source constructor.

This is only the finite chart-side normal-crossing inequality package.  It does
not construct the chart, prove the source-measure pushforward identity, or
identify a Jacobian/density factor. -/
theorem signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
    {ι : Type*} [Fintype ι]
    {residual sourceDensity residualUnit densityUnit : (ι → ℝ) → ℝ}
    {R : ι → ℝ} {h k : ι → ℕ} {c C : ℝ}
    (hdensityUnit_aemeas :
      AEMeasurable densityUnit
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hres_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      residual y =
        residualUnit y * ∏ i, (|y i|) ^ (2 * (k i : ℝ)))
    (hdensity_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      sourceDensity y =
        densityUnit y * ∏ i, (|y i|) ^ (h i : ℝ))
    (hresUnit_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c ≤ residualUnit y)
    (hdensityUnit_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ densityUnit y)
    (hdensityUnit_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      densityUnit y ≤ C) :
    AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))) ∧
      (∀ᵐ y : ι → ℝ
        ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
        c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤ residual y) ∧
      (∀ᵐ y : ι → ℝ
        ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
        0 ≤ sourceDensity y) ∧
      (∀ᵐ y : ι → ℝ
        ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
        sourceDensity y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) := by
  let signedBox : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  have hmonomial_meas :
      Measurable fun y : ι → ℝ => ∏ i, (|y i|) ^ (h i : ℝ) := by
    fun_prop
  have hsource_aemeas :
      AEMeasurable sourceDensity signedBox := by
    have hprod :
        AEMeasurable
          (fun y : ι → ℝ => densityUnit y * ∏ i, (|y i|) ^ (h i : ℝ))
          signedBox :=
      hdensityUnit_aemeas.mul hmonomial_meas.aemeasurable
    have heq :
        (fun y : ι → ℝ => densityUnit y * ∏ i, (|y i|) ^ (h i : ℝ)) =ᵐ[signedBox]
          sourceDensity := by
      filter_upwards [hdensity_eq] with y hy
      exact hy.symm
    exact hprod.congr heq
  refine ⟨hsource_aemeas.ennreal_ofReal, ?_, ?_, ?_⟩
  · filter_upwards [hres_eq, hresUnit_lower] with y hyres hyunit
    rw [hyres]
    exact mul_le_mul_of_nonneg_right hyunit (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg (y i)) _)
  · filter_upwards [hdensity_eq, hdensityUnit_nonneg] with y hydensity hyunit
    rw [hydensity]
    exact mul_nonneg hyunit (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg (y i)) _)
  · filter_upwards [hdensity_eq, hdensityUnit_le] with y hydensity hyunit
    rw [hydensity]
    exact mul_le_mul_of_nonneg_right hyunit (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg (y i)) _)

set_option linter.unusedSectionVars false in
/-- Residual source hypotheses from a signed-box chart pushforward with a
supplied density and explicit absolute-monomial residual/density bounds.

This is a weighted signed-box source-measure constructor.  It assumes the
source-measure pushforward through `signedBox.withDensity (ofReal density)` and
the chart-side density bounds; it does not construct the chart, compute the
Jacobian/density factor, compare the original DLN loss, or extract an RLCT. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  let signedBox : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let weightedBox : Measure (ι → ℝ) :=
    signedBox.withDensity (fun y : ι → ℝ => ENNReal.ofReal (density y))
  let residual : (ι → ℝ) → ℝ := fun y =>
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge (chart y))
  have hpos_signed :
      ∀ᵐ y ∂ signedBox, 0 < residual y := by
    have hcoord : ∀ᵐ y : ι → ℝ ∂ signedBox, ∀ i, 0 < |y i| := by
      dsimp [signedBox]
      exact ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := ι)
    filter_upwards [hcoord, hlower] with y hyabs hylower
    have hmonomial_pos :
        0 < ∏ i, (|y i|) ^ (2 * (k i : ℝ)) := by
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hyabs i) _
    exact lt_of_lt_of_le (mul_pos hc hmonomial_pos) hylower
  have hpos_chart :
      ∀ᵐ y ∂ weightedBox, 0 < residual y := by
    exact (withDensity_absolutelyContinuous signedBox
      (fun y : ι → ℝ => ENNReal.ofReal (density y))).ae_le hpos_signed
  have hfinite_signed :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
        ∂ signedBox) < ∞ := by
    dsimp [signedBox, residual]
    exact
      lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
        (h := h) (k := k) (t := t) (R := R) (c := c) (C := C)
        (loss := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
        (density := density)
        hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le
  have hbase_chart :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox) < ∞ := by
    have hdensity_lt_top :
        ∀ᵐ y : ι → ℝ ∂ signedBox, ENNReal.ofReal (density y) < ∞ := by
      filter_upwards with y
      exact ENNReal.ofReal_lt_top
    have hwith :
        (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox) =
          ∫⁻ y : ι → ℝ,
            ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
            ∂ signedBox := by
      dsimp [weightedBox]
      rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        signedBox (by simpa [signedBox] using hdensity_aemeas) hdensity_lt_top
        (fun y : ι → ℝ => ENNReal.ofReal ((residual y) ^ (-t)))]
      simp [Pi.mul_apply]
    have hmul :
        (∫⁻ y : ι → ℝ,
            ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
            ∂ signedBox) =
          ∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
            ∂ signedBox := by
      apply lintegral_congr_ae
      filter_upwards [hdensity_nonneg] with y hyden_nonneg
      rw [mul_comm]
      exact (ENNReal.ofReal_mul' hyden_nonneg).symm
    calc
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox)
          = ∫⁻ y : ι → ℝ,
              ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
              ∂ signedBox := hwith
      _ = ∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
            ∂ signedBox := hmul
      _ < ∞ := hfinite_signed
  exact
    residualSourceHypotheses_of_measure_map
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (ν := weightedBox) (chart := chart) (t := t)
      (hchart.mono_ac (by
        simpa [signedBox, weightedBox] using
          withDensity_absolutelyContinuous signedBox
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
      (by simpa [signedBox, weightedBox] using hmap)
      hpos_meas
      (by simpa [residual] using hpos_chart)
      (by simpa [residual] using hbase_chart)

set_option linter.unusedSectionVars false in
/-- Weighted signed-box residual source hypotheses with the residual positive
set measurability derived from a measurable residual coordinate map. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hres_meas :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge))
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  exact
    residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (chart := chart) (density := density)
      (t := t) (c := c) (C := C) (R := R) (h := h) (k := k)
      hdensity_aemeas hchart hmap
      (measurableSet_residualSquareSum_pos_of_measurable
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) hres_meas)
      hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le

set_option linter.unusedSectionVars false in
/-- Weighted signed-box residual source hypotheses with residual positive-set
measurability derived from measurable fixed-basis edge matrices.

This consumes exactly the matrix-valued edge family used by the deterministic
p. 13 suffix recursion; it still assumes the signed-box chart, pushforward,
monomial residual lower bound, and density bounds. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  exact
    residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (chart := chart) (density := density)
      (t := t) (c := c) (C := C) (R := R) (h := h) (k := k)
      (measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
        (W := W) (B := B) U₀ hU₀ Cedge hEdgeMatrix)
      hdensity_aemeas hchart hmap
      hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le

set_option linter.unusedSectionVars false in
/-- Local finite-side p.13 regular-coordinate integrability from supplied
source-stratum residual integrability and supplied uniform-in-fiber loss/density
bounds.

This combines the uniform source-filter handoff in this file with the
finite-side bounded-density p.13 adapter from
`RegularSuspensionSquareSumIntegrability.lean`.  Residual positivity and
residual negative-power integrability are still explicit hypotheses on the
source rank stratum. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) μ t)
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (r := r) (rEdge := rEdge) (μ := μ) (ν := ν)
      (loss := loss) (density := density) (R := R) (c := c) (C := C)
      hsource_meas hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hxU, hloss_ae, hdensity_nonneg_ae, hdensity_le_ae⟩
  have hsubset : U ∩ sourceStratum ⊆ sourceStratum := Set.inter_subset_right
  rcases residualSourceHypotheses_mono
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := sourceStratum)
      (source' := U ∩ sourceStratum) (μ := μ) (t := t)
      hsubset hpos_source
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source) with
    ⟨hpos_U, hbase_U⟩
  have hfin :=
    lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
      (W := W) (B := B) sourceData
      (μ := μ.restrict (U ∩ sourceStratum)) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R)
      (c := c) (C := C) hR hc hC ht hpos_U
      (by simpa [residualNegPowerIntegrableOn] using hbase_U)
      (by simpa [ρ, sourceStratum] using hloss_ae)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg_ae)
      (by simpa [ρ, sourceStratum] using hdensity_le_ae)
  exact ⟨U, hUopen, hxU, by simpa [ρ, sourceStratum] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Source-local p.13 finite-integral handoff.

This is the local-source version of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.
The residual hypotheses and the final restricted product measure use the
supplied `source`, not the full source-rank stratum.  This is the correct shape
for a local chart image; no chart, pushforward, density transport, or
normal-crossing theorem is constructed here. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  rcases exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ) (ν := ν)
      (loss := loss) (density := density) (R := R) (c := c) (C := C)
      hsource_meas hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hxU, hloss_ae, hdensity_nonneg_ae, hdensity_le_ae⟩
  have hsubset : U ∩ source ⊆ source := Set.inter_subset_right
  rcases residualSourceHypotheses_mono
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source)
      (source' := U ∩ source) (μ := μ) (t := t)
      hsubset hpos_source
      (by simpa [residualNegPowerIntegrableOn] using hbase_source) with
    ⟨hpos_U, hbase_U⟩
  have hfin :=
    lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
      (W := W) (B := B) sourceData
      (μ := μ.restrict (U ∩ source)) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R)
      (c := c) (C := C) hR hc hC ht hpos_U
      (by simpa [residualNegPowerIntegrableOn] using hbase_U)
      (by simpa [ρ] using hloss_ae)
      (by simpa [ρ] using hdensity_nonneg_ae)
      (by simpa [ρ] using hdensity_le_ae)
  exact ⟨U, hUopen, hxU, by simpa [ρ] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Boundary-explicit consumer from a local chart source to the full
source-rank stratum.

The theorem assumes that inside a specified open neighborhood `Ulocal`, the
full source-rank stratum is contained in the supplied `localSource`.  The proof
shrinks the open integration set returned by the local-source theorem and uses
monotonicity of restricted product measures.  It does not prove the missing
p. 13 local inverse/source-coverage statement. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {localSource : Set α} {μ : Measure α} [SFinite μ]
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (Ulocal : Set α) (hUlocal_open : IsOpen Ulocal) (hx₀Ulocal : x₀ ∈ Ulocal)
    (hcoverage :
      Ulocal ∩ paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge ⊆
      Ulocal ∩ localSource)
    (hlocalSource_meas : MeasurableSet localSource)
    (hpos_local :
      ∀ᵐ x ∂ μ.restrict localSource,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_local :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge localSource μ t)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ localSource,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ localSource,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ localSource,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
        (W := W) (B := B) sourceData
        (source := localSource) (μ := μ) (ν := ν)
        (loss := loss) (density := density)
        (t := t) (R := R) (c := c) (C := C)
        hR hc hC ht hlocalSource_meas hpos_local
        (by simpa [residualNegPowerIntegrableOn] using hbase_local)
        (by simpa [ρ] using hloss)
        (by simpa [ρ] using hdensity_nonneg)
        (by simpa [ρ] using hdensity_le) with
    ⟨Uchart, hUchart_open, hx₀Uchart, hfinite_local⟩
  let U := Uchart ∩ Ulocal
  have hU_open : IsOpen U := hUchart_open.inter hUlocal_open
  have hx₀U : x₀ ∈ U := ⟨hx₀Uchart, hx₀Ulocal⟩
  have hsubset_local : U ∩ sourceStratum ⊆ Uchart ∩ localSource := by
    intro x hx
    have hxlocal : x ∈ Ulocal ∩ sourceStratum := ⟨hx.1.2, hx.2⟩
    have hxcovered : x ∈ Ulocal ∩ localSource := by
      exact hcoverage (by simpa [sourceStratum] using hxlocal)
    exact ⟨hx.1.1, hxcovered.2⟩
  let integrand : α × EuclideanSpace ℝ ρ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
          (fun u =>
            (loss (z.1, u)) ^
              (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
              density (z.1, u)) z.2)
  have hmeasure_le :
      (μ.restrict (U ∩ sourceStratum)).prod ν ≤
        (μ.restrict (Uchart ∩ localSource)).prod ν := by
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_prod_eq_prod_univ]
    exact Measure.restrict_mono (Set.prod_mono_left hsubset_local) le_rfl
  have hfinite_U :
      (∫⁻ z : α × EuclideanSpace ℝ ρ, integrand z ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    exact (lintegral_mono' hmeasure_le (le_refl integrand)).trans_lt
      (by simpa [integrand, ρ] using hfinite_local)
  exact ⟨U, hU_open, hx₀U, by simpa [integrand, ρ, sourceStratum] using hfinite_U⟩

set_option linter.unusedSectionVars false in
/-- Local-source finite-integral handoff with residual source hypotheses
supplied by a weighted signed-box residual chart.

Compared with
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix`,
the source set is supplied explicitly.  This matches a local chart image: the
pushforward identity and residual monomial data need only hold for that local
source, not for the whole source-rank stratum. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict source =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := source) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart hmap
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
      (W := W) (B := B) sourceData
      (source := source) (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := Rreg) (c := creg) (C := Creg)
      hRreg hcreg hCreg ht hsource_meas
      hpos_source
      (by simpa [residualNegPowerIntegrableOn] using hbase_source)
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Local-source signed-box finite-integral handoff from supplied
monomial-times-unit residual and density data.

This is the chart-side consumer expected after a local residual chart has been
supplied: the pushforward identity and the unit identities remain hypotheses,
while the residual lower bound and source-density bounds are derived by the
elementary monomial-unit inequality package. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {residualUnit densityUnit : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict source =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hdensityUnit_aemeas :
      AEMeasurable densityUnit
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hres_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
        residualUnit y * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)))
    (hsourceDensity_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y =
        densityUnit y * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hresUnit_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres ≤ residualUnit y)
    (hdensityUnit_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ densityUnit y)
    (hdensityUnit_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      densityUnit y ≤ Cres)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  rcases
      signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
        (residual := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
        (sourceDensity := sourceDensity)
        (residualUnit := residualUnit) (densityUnit := densityUnit)
        (R := Rres) (h := hres) (k := kres) (c := cres) (C := Cres)
        hdensityUnit_aemeas hres_eq hsourceDensity_eq hresUnit_lower
        hdensityUnit_nonneg hdensityUnit_le with
    ⟨hsourceDensity_aemeas, hres_lower, hsourceDensity_nonneg, hsourceDensity_le⟩
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
      (W := W) (B := B) sourceData
      (source := source) (μ := μ) (ν := ν)
      (sourceChart := sourceChart) (sourceDensity := sourceDensity)
      (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
      (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres) (kres := kres)
      hRreg hcreg hCreg ht hsource_meas hEdgeMatrix hsourceDensity_aemeas hsourceChart
      hmap hcres hCres hRres hcrit hres_lower hsourceDensity_nonneg hsourceDensity_le
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Local finite-integral handoff with residual source hypotheses supplied by
a weighted signed-box residual chart.

This composes the signed-box residual source-measure constructor with the
p.13 local finite-integral bridge.  It still assumes source-stratum
measurability, the signed-box pushforward and monomial bounds, and the local
regular-fiber loss/density bounds. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := Rreg) (c := creg) (C := Creg)
      hRreg hcreg hCreg ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Conditional p.13 finite-integral handoff from an adapted fixed-base
product-difference lower bound to an arbitrary supplied loss.

The comparison `c0 * adaptedProductDifferenceSquareSum <= loss` is an explicit
hypothesis.  This theorem only multiplies comparison constants before applying
the existing p.13 finite-side theorem; it does not compare the adapted
square-sum with the original DLN/statistical loss. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c c0 C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hc0 : 0 < c0) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge) μ t)
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_cmp :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B CedgeBase r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B CedgeBase r rEdge
  have hcc : 0 < c0 * c := mul_pos hc0 hc
  have hloss :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            (c0 * c) * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hadapted_lower, hloss_cmp] with x hxlower hxcmp u hu
    have hscaled :
        c0 * (c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
            aoyagiCoordinateSquareSum (fun i => u i))) ≤
          c0 *
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
      exact mul_le_mul_of_nonneg_left (hxlower u hu) (le_of_lt hc0)
    calc
      (c0 * c) * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x) +
          aoyagiCoordinateSquareSum (fun i => u i))
          = c0 * (c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
            aoyagiCoordinateSquareSum (fun i => u i))) := by ring
      _ ≤ c0 *
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := hscaled
      _ ≤ loss (x, u) := hxcmp u hu
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := R) (c := c0 * c) (C := C)
      hR hcc hC ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Local-source conditional p.13 finite-integral handoff from an adapted
fixed-base product-difference lower bound to an arbitrary supplied loss.

This is the local-source analogue of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss`.
The source set is supplied explicitly, so a future local chart package does not
have to upgrade its bounds to the full source-rank stratum. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c c0 C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hc0 : 0 < c0) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase source μ t)
    (hadapted_lower :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_cmp :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hcc : 0 < c0 * c := mul_pos hc0 hc
  have hloss :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            (c0 * c) * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hadapted_lower, hloss_cmp] with x hxlower hxcmp u hu
    have hscaled :
        c0 * (c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
            aoyagiCoordinateSquareSum (fun i => u i))) ≤
          c0 *
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
      exact mul_le_mul_of_nonneg_left (hxlower u hu) (le_of_lt hc0)
    calc
      (c0 * c) * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x) +
          aoyagiCoordinateSquareSum (fun i => u i))
          = c0 * (c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ CedgeBase x) +
            aoyagiCoordinateSquareSum (fun i => u i))) := by ring
      _ ≤ c0 *
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := hscaled
      _ ≤ loss (x, u) := hxcmp u hu
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
      (W := W) (B := B) sourceData
      (source := source) (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := R) (c := c0 * c) (C := C)
      hR hcc hC ht hsource_meas hpos_source
      (by simpa [residualNegPowerIntegrableOn] using hbase_source)
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking p.13 finite-integral handoff from an adapted fixed-base
product-difference lower bound to an arbitrary supplied loss, when the density
factor is supplied as a positive continuous function at the chart center.

This removes only the separate local density nonnegativity and boundedness
hypotheses from the fixed-radius adapted-loss comparison theorem.  The
comparison `c0 * adaptedProductDifferenceSquareSum <= loss` remains an
explicit hypothesis. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c c0 : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (hc0 : 0 < c0) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge) μ t)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_cmp :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u)) :
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          ENNReal.ofReal
            ((Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict
              (U ∩ paperEndpointFixedBaseSourceRankStratum
                (K := ℝ) W B CedgeBase r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B CedgeBase r rEdge
  rcases exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
      (s := sourceStratum) (Rmax := Rmax) hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hadapted_lower_R :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := by
    filter_upwards [hadapted_lower] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  have hloss_cmp_R :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u) := by
    filter_upwards [hloss_cmp] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss
        (W := W) (B := B) sourceData
        (μ := μ) (ν := ν) (CedgeProd := CedgeProd)
        (loss := loss) (density := density)
        (t := t) (R := R) (c := c) (c0 := c0) (C := C)
        hR hc hc0 hC ht
        (by simpa [sourceStratum] using hsource_meas)
        (by simpa [sourceStratum] using hpos_source)
        (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
        (by simpa [ρ, sourceStratum] using hadapted_lower_R)
        (by simpa [ρ, sourceStratum] using hloss_cmp_R)
        (by simpa [ρ, sourceStratum] using hdensity_nonneg)
        (by simpa [ρ, sourceStratum] using hdensity_le) with
    ⟨U, hUopen, hxU, hfin⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hxU, by simpa [ρ, sourceStratum] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Conditional p.13 finite-integral handoff for a chart loss identified with
the adapted fixed-base product-difference square-sum.

The product-coordinate lower bound and the identification of the chart loss
with the adapted square-sum are explicit hypotheses.  This theorem does not
construct the product chart or compare with the original DLN/statistical
loss. -/
theorem exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {chartLoss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge) μ t)
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_id :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = chartLoss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (chartLoss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B CedgeBase r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B CedgeBase r rEdge
  have hloss :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ chartLoss (x, u) := by
    filter_upwards [hadapted_lower, hloss_id] with x hxlower hxid u hu
    calc
      c * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x) +
          aoyagiCoordinateSquareSum (fun i => u i))
          ≤ paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := hxlower u hu
      _ = chartLoss (x, u) := hxid u hu
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := chartLoss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Local finite-side p.13 integrability when the transported density factor is
supplied as a positive continuous function at the chart center.

This removes the separate local nonnegativity and boundedness hypotheses for
the density by shrinking the regular-coordinate radius.  It still does not
construct the density/Jacobian factor or prove the loss lower bound. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) μ t)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          ENNReal.ofReal
            ((Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict
              (U ∩ paperEndpointFixedBaseSourceRankStratum
                (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
      (s := sourceStratum) (Rmax := Rmax) hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hloss_R :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hsource_meas hpos_source hbase_source
      (by simpa [ρ, sourceStratum] using hloss_R)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le) with
    ⟨U, hUopen, hxU, hfin⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hxU, by simpa [ρ, sourceStratum] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Local finite-side p.13 integrability with the concrete chart-side inverse
Jacobian density for the left-endpoint product step.

This specializes
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`
to
`productReductionStepRawOrderInverseJacobianDensity` composed with
`paperEndpointFixedBaseP13RawOrderTuple`.  It removes only the abstract
continuity/positivity hypotheses on the density factor; the loss lower bound
and residual-source integrability hypotheses remain supplied. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex V 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv))}
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := V) (B := Bv) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) μ t)
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  productReductionStepRawOrderInverseJacobianDensity
                    (paperEndpointFixedBaseP13RawOrderTuple
                      V Bv U₀ hU₀ CedgeBase (z.1, u))) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let density : α × EuclideanSpace ℝ ρ → ℝ :=
    fun xu ↦
      productReductionStepRawOrderInverseJacobianDensity
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase xu)
  have hdensity_cont : ContinuousAt density (x₀, 0) := by
    simpa [density, ρ] using
      continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) hCedgeBase hbase
  have hdensity_pos : 0 < density (x₀, 0) := by
    simpa [density, ρ] using
      paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) x₀
  simpa [density, ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
      (W := V) (B := Bv) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (c := c)
      hRmax hc ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hloss)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking local finite-integral handoff with residual source
hypotheses supplied by a weighted signed-box residual chart and density bounds
supplied by positivity and continuity at the chart center.

This composes the signed-box residual source-measure constructor with the
continuous-density p.13 local finite-integral bridge.  It still assumes
source-stratum measurability, the signed-box pushforward and monomial bounds,
the density factor itself, and the local regular-fiber loss lower bound. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hcreg : 0 < creg) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (c := creg)
      hRmax hcreg ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hloss)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking p.13 finite-integral handoff for the concrete
product-step inverse Jacobian density, with residual source hypotheses supplied
by a weighted signed-box residual chart.

This removes only the abstract regular-fiber density factor from the signed-box
front end: the residual signed-box pushforward, source-density monomial bound,
and local regular-fiber loss lower bound are still explicit hypotheses.  It
does not identify the signed-box source density with the product-step inverse
Jacobian density and does not prove a product-chart pushforward theorem. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex V 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv))}
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hcreg : 0 < creg) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex V) (reverseEdge V Bv) U₀ 0))) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  productReductionStepRawOrderInverseJacobianDensity
                    (paperEndpointFixedBaseP13RawOrderTuple
                      V Bv U₀ hU₀ CedgeBase (z.1, u))) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := V) (B := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeBase) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase
      (V := V) (Bv := Bv) sourceData
      (μ := μ) (ν := ν) (loss := loss)
      (t := t) (Rmax := Rmax) (c := creg)
      hRmax hcreg ht hCedgeBase hbase
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking local finite-integral handoff from a globally continuous
edge family, a weighted signed-box residual chart, and a positive continuous
density factor.

Global continuity of `Cedge` supplies both source-stratum measurability and
measurability of the fixed-basis endpoint edge matrices consumed by the
deterministic p.13 suffix recursion.  The signed-box chart, weighted
pushforward, residual monomial bound, density factor, and loss lower bound are
still explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hcreg : 0 < creg) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hsource_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W) (B := B) (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge
  have hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
    refine (continuous_pi ?_).measurable
    intro p
    have hCedge_p : Continuous fun x : α ↦ Cedge x p :=
      (continuous_apply p).comp hCedge
    have hcoord : Continuous
        (fun f : reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) :=
      continuous_linearMap_toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hcoord.comp hCedge_p
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (creg := creg) (cres := cres) (Cres := Cres)
      (Rres := Rres) (hres := hres) (kres := kres)
      hRmax hcreg ht hsource_meas hEdgeMatrix
      hsourceDensity_aemeas hsourceChart
      (by simpa [sourceStratum] using hmap)
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hloss)

/-- Radius-shrinking local finite-integral handoff from a measurable fixed-base
edge-matrix family, a weighted signed-box residual chart, a positive continuous
density factor, and an explicit comparison from the adapted p.13 square-sum to
the supplied loss.

This is the measurable-edge-matrix variant of the continuous-edge front end:
the source-stratum measurability and residual-coordinate measurability are both
derived from the fixed-basis edge matrices consumed by the deterministic suffix
recursion.  The signed-box chart, weighted pushforward, residual monomial
bound, product-coordinate adapted lower bound, and adapted-to-loss comparison
remain explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c c0 cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (hc0 : 0 < c0) (ht : 0 < t)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_cmp :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hsource_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_measurable_edgeMatrix
        (W := W) (B := B) U₀ hU₀
        (Cedge := Cedge) (r := r) (rEdge := rEdge) hEdgeMatrix
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (CedgeProd := CedgeProd)
      (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (c := c) (c0 := c0)
      hRmax hc hc0 ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hadapted_lower)
      (by simpa [ρ, sourceStratum] using hloss_cmp)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking local finite-integral handoff from a globally continuous
edge family, a weighted signed-box residual chart, a positive continuous
density factor, and an explicit comparison from the adapted p.13 square-sum to
the supplied loss.

This is the top finite-integral plumbing front end for this file.  It still
assumes the signed-box source chart and pushforward, residual monomial lower
bound, product-coordinate adapted lower bound, and positive comparison from
the adapted square-sum to `loss`. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c c0 cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (hc0 : 0 < c0) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_cmp :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hsource_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W) (B := B) (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge
  have hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
    refine (continuous_pi ?_).measurable
    intro p
    have hCedge_p : Continuous fun x : α ↦ Cedge x p :=
      (continuous_apply p).comp hCedge
    have hcoord : Continuous
        (fun f : reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) :=
      continuous_linearMap_toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hcoord.comp hCedge_p
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (CedgeProd := CedgeProd)
      (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (c := c) (c0 := c0)
      hRmax hc hc0 ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hadapted_lower)
      (by simpa [ρ, sourceStratum] using hloss_cmp)

end PaperEndpointFixedBaseRegularCoordinateSourceData

end FixedBaseRealLocalMeasure

end Aoyagi
end DLN
end DLNFibre

end
