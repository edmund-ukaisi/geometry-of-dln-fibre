import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure

/-!
# Retained-passive local source with computed Jacobian density

This file is a leaf bridge from the retained-passive raw-order change of
variables with computed formal/product Jacobian density to the fixed-base p.13
local-source measure socket.  It is still a local chart-measure identity; it
does not construct an original source prior, identify signed-box densities,
prove normal crossings, compute a pole order, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

set_option linter.style.longLine false

section RetainedPassiveLocalJacobianMeasure

universe v

variable {M : ℕ}
  (W : Fin (M + 2) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- A realized retained-passive local source inherits any supplied weighted
raw-order change-of-variables identity after composition with the source
chart.

The hypothesis `hcov` is the only place where the density is used.  This
helper keeps the local-source restriction argument separate from the later
formal/product determinant specializations. -/
theorem measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_of_realization_of_cov
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    (sourceChart :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ → α)
    (J :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ → ℝ≥0∞)
    (hCedge : Continuous Cedge)
    (hsourceChart :
      AEMeasurable sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀))))
    (hrealize :
      ∀ y ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀),
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (Cedge (sourceChart y) p :
                reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) y)
    (hcov :
      Measure.map
          (fun z :
              TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) z))
          ((m.restrict
            (topologyTupleDetChartSet
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀))).withDensity J) =
        Measure.map sourceChart
          (m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀)))) :
    let S : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let T : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge
    let μ := Measure.map sourceChart (m.restrict T)
    μ.restrict localSource =
      Measure.map
        (fun z :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z))
        ((m.restrict S).withDensity J) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge
  let μ : Measure α := Measure.map sourceChart (m.restrict T)
  have hs : NullMeasurableSet S m := by
    simpa [S, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') m
  let Factual : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let Ψ : TopologyTuple ρ κ' ℝ → α :=
    fun z ↦
      sourceChart
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)
  have hlocal_abs :
      μ.restrict localSource =
        Measure.map Ψ ((m.restrict S).withDensity Factual) := by
    simpa [S, T, localSource, μ, Ψ, Factual, ρ, κ'] using
      measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_of_realization
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (m := m) (sourceChart := sourceChart)
        hCedge
        (by simpa [T, ρ, κ'] using hsourceChart)
        (by
          intro y hy
          simpa [ρ, κ'] using hrealize y (by simpa [T, ρ, κ'] using hy))
  have hcov_abs :
      Measure.map Ψ ((m.restrict S).withDensity Factual) =
        Measure.map sourceChart (m.restrict T) := by
    simpa [S, T, Ψ, Factual, ρ, κ'] using
      map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
        (ρ := ρ) (κ' := κ') (β := α) m sourceChart hs
        (by simpa [T, ρ, κ'] using hsourceChart)
  have hcov_J :
      Measure.map Ψ ((m.restrict S).withDensity J) =
        Measure.map sourceChart (m.restrict T) := by
    simpa [S, T, Ψ, ρ, κ'] using hcov
  change μ.restrict localSource = Measure.map Ψ ((m.restrict S).withDensity J)
  calc
    μ.restrict localSource =
        Measure.map Ψ ((m.restrict S).withDensity Factual) := hlocal_abs
    _ = Measure.map sourceChart (m.restrict T) := hcov_abs
    _ = Measure.map Ψ ((m.restrict S).withDensity J) := hcov_J.symm

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Realized retained-passive local-source measure identity with the formal
raw-order determinant density. -/
theorem measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_of_realization
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    (sourceChart :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ → α)
    (hCedge : Continuous Cedge)
    (hsourceChart :
      AEMeasurable sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀))))
    (hrealize :
      ∀ y ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀),
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (Cedge (sourceChart y) p :
                reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) y) :
    let S : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let T : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge
    let μ := Measure.map sourceChart (m.restrict T)
    μ.restrict localSource =
      Measure.map
        (fun z :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z))
        ((m.restrict S).withDensity
          (fun z :
              TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := M) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) z))) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let J : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  have hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m := by
    exact
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') m
  have hcov :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
        Measure.map sourceChart
          (m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
    simpa [J, ρ, κ'] using
      map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_map_restrict_rawSourceChart
        (M := M) (ρ := ρ) (κ' := κ') (β := α) m sourceChart hs
        (by simpa [ρ, κ'] using hsourceChart)
  simpa [J, ρ, κ'] using
    measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_of_realization_of_cov
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (m := m) (sourceChart := sourceChart) (J := J)
      hCedge hsourceChart hrealize hcov

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Realized retained-passive local-source measure identity with the
solved-`A1` product determinant density. -/
theorem measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_of_realization
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure]
    (sourceChart :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ → α)
    (hCedge : Continuous Cedge)
    (hsourceChart :
      AEMeasurable sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀))))
    (hrealize :
      ∀ y ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀),
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              (Cedge (sourceChart y) p :
                reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) y) :
    let S : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let T : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge
    let μ := Measure.map sourceChart (m.restrict T)
    μ.restrict localSource =
      Measure.map
        (fun z :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z))
        ((m.restrict S).withDensity
          (fun z :
              TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) z))) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let J : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := M) (ρ := ρ) (κ' := κ') z)
  have hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m := by
    exact
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') m
  have hcov :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ ↦
            sourceChart
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          ((m.restrict
            (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity J) =
        Measure.map sourceChart
          (m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
    simpa [J, ρ, κ'] using
      map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_map_restrict_rawSourceChart
        (M := M) (ρ := ρ) (κ' := κ') (β := α) m sourceChart hs
        (by simpa [ρ, κ'] using hsourceChart)
  simpa [J, ρ, κ'] using
    measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_of_realization_of_cov
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (m := m) (sourceChart := sourceChart) (J := J)
      hCedge hsourceChart hrealize hcov

private theorem retainedPassiveP13CanonicalSourceChart_aemeasurable
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ)) :
    AEMeasurable
      (fun y :
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) y)))
      (m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀))) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  have hTnull : NullMeasurableSet T m := by
    exact
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet.nullMeasurableSet
  have hsourceContOn : ContinuousOn sourceChart T := by
    rw [continuousOn_iff_continuous_restrict]
    let toDetChart :
        T →
          {data :
            RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
            data.detChart} :=
      fun y ↦
        ⟨ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1),
          (mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := ρ) (κ' := κ') y.1)).1
            (topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ') y.2)⟩
    have hInv :
        Continuous
          (fun y : T ↦
            topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    have hToDetChart : Continuous toDetChart := by
      have hamb :
          Continuous
            (fun y : T ↦
              ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
                (topologyTupleEdgeRawOrderInverse
                  (K := ℝ) (ρ := ρ) (κ' := κ') y.1)) :=
        (continuous_ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp hInv
      exact hamb.subtype_mk _
    have hchart :
        Continuous
          (fun data :
              {data :
                RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
                data.detChart} ↦
            paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U₀ hU₀ data) :=
      continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
        (K := ℝ) W B U₀ hU₀
    simpa [sourceChart, toDetChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData] using
      hchart.comp hToDetChart
  simpa [T, sourceChart, ρ, κ', EFam] using
    ContinuousOn.aemeasurable₀ hsourceContOn hTnull

private theorem retainedPassiveP13CanonicalSourceChart_realize
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))} :
    ∀ y ∈
        topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀),
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : ∀ q : Fin (M + 1),
                reverseVertex W q.castSucc →L[ℝ] reverseVertex W q.succ ↦ E)
              (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
                (ofTopologyTuple
                  (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀)
                  (topologyTupleEdgeRawOrderInverse
                    (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                    (κ' := throughSubspaceEndpointComplementIndex
                      (reverseVertex W) (reverseEdge W B) U₀) y))) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        edgeFamilyOfRawOrderTuple
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) y := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  intro y hy
  have hraw :
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y) =
        y :=
    topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
      (K := ℝ) (ρ := ρ) (κ' := κ') hy
  calc
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun p : Fin (M + 1) ↦
          ((fun E : EFam ↦ E) (sourceChart y) p :
            reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := ρ) (κ' := κ') y)).edgeMatrix := by
      simpa [sourceChart, EFam] using
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := ℝ) W B (U₀ := U₀) (hU₀ := hU₀)
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := ρ) (κ' := κ') y))
    _ =
        topologyTupleEdgeMatrix
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := ρ) (κ' := κ') y) := by
      rfl
    _ =
        edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := ρ) (κ' := κ') y)) := by
      exact
        (edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := ρ) (κ' := κ') y)).symm
    _ = edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := by
      rw [hraw]

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- On the determinant chart, the canonical retained-passive chart-side residual
readout is the suffix residual product of the raw edge-matrix tuple.

This is a chart-expression identification only.  It does not prove residual
zero-locus nullity, a.e. positivity, finite negative-power integrability,
normal crossings, pole order, or an RLCT statement. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualProduct
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (z :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)
    (hz :
      z ∈ topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
        (sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
      AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualProduct
          (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z)
          (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
  dsimp only
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let y : TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hy :
      y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') := by
    exact
      mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') hz
  have hrealize :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := by
    simpa [sourceChart, EFam, y, ρ, κ'] using
      retainedPassiveP13CanonicalSourceChart_realize
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) y hy
  have hedge :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z := by
    calc
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := hrealize
      _ =
          topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z := by
        simp [y, ρ, κ',
          edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := ρ) (κ' := κ') z]
  have hres :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y) =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
              (fun p : Fin (M + 1) ↦
                ((fun E : EFam ↦ E) (sourceChart y) p :
                  reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
    simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges, EFam] using
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
        (K := ℝ) (N := M + 1) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y)
  calc
    paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
        (sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y) := by
      rfl
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
              (fun p : Fin (M + 1) ↦
                ((fun E : EFam ↦ E) (sourceChart y) p :
                  reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := hres
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualProduct
            (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z)
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
      rw [hedge]

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- On the determinant chart, the canonical retained-passive chart-side residual
readout is the residual-factor product of the stored `C` blocks in the
retained-passive chart datum.

This is the source-readback form of
`paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualProduct`.
It removes the continuous source-family/readback layer from the chart-side
residual expression, but it does not prove residual zero-locus nullity, a.e.
positivity, finite negative-power integrability, normal crossings, pole order,
or an RLCT statement. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualFactorProduct
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (z :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)
    (hz :
      z ∈ topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
        (sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
      AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
  dsimp only
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let y : TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z
  have hy :
      y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') := by
    exact
      mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') hz
  have hreadout :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y) =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (sourceReadback (K := ℝ) (ρ := ρ)
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
                (fun p : Fin (M + 1) ↦
                  ((fun E : EFam ↦ E) (sourceChart y) p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))).C
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
    simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges, EFam] using
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
        (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y)
  have hrealize :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := by
    simpa [sourceChart, EFam, y, ρ, κ'] using
      retainedPassiveP13CanonicalSourceChart_realize
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) y hy
  have hedge :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
        topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z := by
    calc
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) (sourceChart y) p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := hrealize
      _ =
          topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z := by
        simp [y, ρ, κ',
          edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := ρ) (κ' := κ') z]
  have hdet :
      (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).detChart := by
    simpa [topologyTupleDetChartSet, ρ, κ'] using hz
  have hsource :
      sourceReadback (K := ℝ) (ρ := ρ)
          (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z) =
        ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z := by
    simpa [topologyTupleEdgeMatrix, ρ, κ'] using
      sourceReadback_edgeMatrix_eq
        (K := ℝ) (ρ := ρ)
        (data := ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z) hdet
  calc
    paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
        (sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) (sourceChart y) := by
      rfl
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (sourceReadback (K := ℝ) (ρ := ρ)
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
                (fun p : Fin (M + 1) ↦
                  ((fun E : EFam ↦ E) (sourceChart y) p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))).C
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := hreadout
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (sourceReadback (K := ℝ) (ρ := ρ)
              (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ') z)).C
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
      rw [hedge]
    _ =
        AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z).C
            (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))) := by
      rw [hsource]

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive local-source measure identity with
the formal raw-order determinant density. -/
theorem measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] :
    let S : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let T : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let sourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ →
          (∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    μ.restrict localSource =
      Measure.map
        (fun z :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z))
        ((m.restrict S).withDensity
          (fun z :
              TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
            ENNReal.ofReal
              (Aoyagi.retainedPassiveFormalRawOrderJacobianAbsDetAt
                (M := M) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) z))) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  have hsourceChart :
      AEMeasurable sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
    simpa [sourceChart, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_aemeasurable
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hrealize :
      ∀ y ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'),
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              ((fun E : EFam ↦ E) (sourceChart y) p :
                reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := by
    simpa [sourceChart, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_realize
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
  simpa [sourceChart, ρ, κ', EFam] using
    measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_of_realization
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EFam ↦ E)
      (m := m) (sourceChart := sourceChart)
      (by simpa [EFam] using (continuous_id : Continuous (fun E : EFam ↦ E)))
      hsourceChart hrealize

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive local-source measure identity with
the solved-`A1` product determinant density. -/
theorem measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] :
    let S : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let T : Set
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
    let sourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ →
          (∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀)
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    μ.restrict localSource =
      Measure.map
        (fun z :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
          sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z))
        ((m.restrict S).withDensity
          (fun z :
              TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) ℝ ↦
            ENNReal.ofReal
              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := M) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀) z))) := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  have hsourceChart :
      AEMeasurable sourceChart
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
    simpa [sourceChart, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_aemeasurable
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hrealize :
      ∀ y ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'),
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun p : Fin (M + 1) ↦
              ((fun E : EFam ↦ E) (sourceChart y) p :
                reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) =
          edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y := by
    simpa [sourceChart, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_realize
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
  simpa [sourceChart, ρ, κ', EFam] using
    measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_of_realization
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EFam ↦ E)
      (m := m) (sourceChart := sourceChart)
      (by simpa [EFam] using (continuous_id : Continuous (fun E : EFam ↦ E)))
      hsourceChart hrealize

private theorem retainedPassiveP13CanonicalSourceChart_comp_topologyTupleEdgeRawOrder_aemeasurable_withDensity_formalProductAbsDet
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let ν :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    AEMeasurable
      (fun z : TopologyTuple ρ κ' ℝ ↦
        sourceChart
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) ν := by
  dsimp only
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let ν : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') z))
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  have hs : NullMeasurableSet S m := by
    simpa [S, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') m
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_restrict : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn hs
  have hΦ_ν : AEMeasurable Φ ν := by
    simpa [ν] using hΦ_restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmapRaw :
      Measure.map Φ ν = m.restrict T := by
    simpa [ν, Φ, S, T, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := M) (ρ := ρ) (κ' := κ') m hs
  have hsource_T :
      AEMeasurable sourceChart (m.restrict T) := by
    simpa [sourceChart, T, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_aemeasurable
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hsource_map :
      AEMeasurable sourceChart (Measure.map Φ ν) := by
    rw [hmapRaw]
    exact hsource_T
  simpa [Function.comp_def, Φ, sourceChart, ν, ρ, κ', EFam] using
    hsource_map.comp_aemeasurable hΦ_ν

set_option linter.unusedSectionVars false in
/-- In the canonical retained-passive p.13 identity-source case, the residual
square-sum positive set is measurable.

This is finite fixed-base coordinate bookkeeping: the identity edge-family map
is continuous, so the fixed-basis edge-matrix family is continuous, the residual
block coordinate map is measurable, and the positive set of its square-sum is
measurable. -/
theorem measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)] :
    MeasurableSet {x :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) |
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀
          (fun E :
            (∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ↦ E) x)} := by
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  have hCedge : Continuous (fun E : EFam ↦ E) := by
    simpa [EFam] using (continuous_id : Continuous (fun E : EFam ↦ E))
  have hEdgeMatrixCont :
      Continuous fun x : EFam ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) x p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) := by
    simpa [EFam] using
      continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
        (K := ℝ) (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EFam ↦ E) hCedge
  have hEdgeMatrix :
      Measurable fun x : EFam ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            ((fun E : EFam ↦ E) x p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) :=
    hEdgeMatrixCont.measurable
  have hresidual :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)) := by
    exact
      measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EFam ↦ E) hEdgeMatrix
  simpa [EFam] using
    measurableSet_residualSquareSum_pos_of_measurable
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EFam ↦ E) hresidual

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive local-source residual hypotheses
from chart-side hypotheses for the solved-`A1` product-density measure.

This theorem uses the canonical product-density change-of-variables identity as
the source-measure pushforward in `residualSourceHypotheses_of_measure_map`.
The chart-side residual positivity, residual positive-set measurability, and
finite integral remain explicit hypotheses. -/
theorem residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] {t : ℝ} :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let ν :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    MeasurableSet {x : EFam |
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} →
    (∀ᵐ z ∂ ν,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ ν) < ∞ →
    (∀ᵐ x ∂ μ.restrict localSource,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (fun E : EFam ↦ E) localSource μ t := by
  dsimp only
  intro hpos_meas hpos_chart hbase_chart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
      (fun E : EFam ↦ E)
  let μ : Measure EFam := Measure.map sourceChart (m.restrict T)
  let ν : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') z))
  let chart : TopologyTuple ρ κ' ℝ → EFam :=
    fun z ↦
      sourceChart
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)
  have hmap :
      μ.restrict localSource = Measure.map chart ν := by
    simpa [μ, ν, chart, sourceChart, localSource, S, T, ρ, κ', EFam] using
      measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  have hchart : AEMeasurable chart ν := by
    simpa [ν, chart, sourceChart, S, T, ρ, κ', EFam] using
      retainedPassiveP13CanonicalSourceChart_comp_topologyTupleEdgeRawOrder_aemeasurable_withDensity_formalProductAbsDet
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) m
  exact
    residualSourceHypotheses_of_measure_map
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EFam ↦ E)
      (source := localSource) (μ := μ) (ν := ν) (chart := chart) (t := t)
      hchart hmap hpos_meas hpos_chart hbase_chart

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive local-source residual hypotheses from
chart-side hypotheses only.

Compared with
`residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet`,
this front end discharges the source-side residual positive-set measurability
for the canonical identity source family.  The chart-side residual positivity
and finite residual integral remain explicit. -/
theorem residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] {t : ℝ} :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let ν :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    (∀ᵐ z ∂ ν,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ ν) < ∞ →
    (∀ᵐ x ∂ μ.restrict localSource,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (fun E : EFam ↦ E) localSource μ t := by
  dsimp only
  intro hpos_chart hbase_chart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
      (fun E : EFam ↦ E)
  let μ : Measure EFam := Measure.map sourceChart (m.restrict T)
  let ν : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') z))
  have hpos_meas :
      MeasurableSet {x : EFam |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} := by
    simpa [EFam] using
      measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
  simpa [ρ, κ', S, T, EFam, sourceChart, localSource, μ, ν] using
    residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (m := m) (t := t)
      hpos_meas hpos_chart hbase_chart

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive finite-integral handoff for the
solved-`A1` product-density source measure.

The theorem composes the canonical product-density residual-source handoff with
the retained-passive p.13 local finite-integral socket.  The chart-side
residual positivity, residual positive-set measurability, and residual
negative-power integral remain explicit hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀
        ((fun p : Fin (M + 1) ↦
          LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
          ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
        (fun E :
            (∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let base : EFam :=
      fun p : Fin (M + 1) ↦
        LinearMap.toContinuousLinearMap (reverseEdge W B p)
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let νChart :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
    MeasurableSet {x : EFam |
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} →
    (∀ᵐ z ∂ νChart,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ νChart) < ∞ →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ U : Set EFam, IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EFam × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  dsimp only
  intro hpos_meas hpos_chart hbase_chart hloss hdensity_nonneg hdensity_le
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let base : EFam :=
    fun p : Fin (M + 1) ↦
      LinearMap.toContinuousLinearMap (reverseEdge W B p)
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
      (fun E : EFam ↦ E)
  let μ : Measure EFam := Measure.map sourceChart (m.restrict T)
  let νChart : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') z))
  let ρreg :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
  have hresidual :
      (∀ᵐ x ∂ μ.restrict localSource,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)) ∧
        residualNegPowerIntegrableOn
          (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EFam ↦ E) localSource μ t := by
    simpa [ρ, κ', S, T, EFam, sourceChart, localSource, μ, νChart] using
      residualSourceHypotheses_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) (m := m) (t := t)
        hpos_meas hpos_chart hbase_chart
  have hCedge : Continuous (fun E : EFam ↦ E) := by
    simpa [EFam] using (continuous_id : Continuous (fun E : EFam ↦ E))
  have hbase :
      (fun E : EFam ↦ E) base =
        fun p : Fin (M + 1) ↦
          LinearMap.toContinuousLinearMap (reverseEdge W B p) := by
    rfl
  simpa [ρreg, sourceStratum, μ, sourceChart, T, base, localSource, EFam] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hCedge hbase
      (by simpa [μ, localSource, EFam] using hresidual.1)
      (by simpa [μ, localSource, residualNegPowerIntegrableOn, EFam] using hresidual.2)
      (by simpa [ρreg, base, localSource, EFam] using hloss)
      (by simpa [ρreg, base, localSource, EFam] using hdensity_nonneg)
      (by simpa [ρreg, base, localSource, EFam] using hdensity_le)

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive finite-integral handoff from
chart-side residual hypotheses only.

This front end discharges the source-side residual positive-set measurability
for the canonical identity source family, then delegates to
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet`.
The chart-side residual positivity, chart-side finite residual integral, local
loss lower bound, and local density bounds remain explicit. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_of_chartSide
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀
        ((fun p : Fin (M + 1) ↦
          LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
          ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
        (fun E :
            (∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let base : EFam :=
      fun p : Fin (M + 1) ↦
        LinearMap.toContinuousLinearMap (reverseEdge W B p)
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let νChart :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
    (∀ᵐ z ∂ νChart,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ νChart) < ∞ →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ U : Set EFam, IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EFam × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  dsimp only
  intro hpos_chart hbase_chart hloss hdensity_nonneg hdensity_le
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  have hpos_meas :
      MeasurableSet {x : EFam |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} := by
    simpa [EFam] using
      measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
  simpa [EFam] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
      (W := W) (B := B) sourceData (m := m) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hpos_meas hpos_chart hbase_chart
      hloss hdensity_nonneg hdensity_le

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Canonical fixed-base retained-passive finite-integral handoff for a
continuous positive transported density factor.

This is the radius-shrinking version of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet`:
continuity and positivity of the density at the chart center produce local
nonnegativity and boundedness after shrinking the regular-coordinate radius.
The chart-side residual hypotheses and the local loss lower bound remain
explicit. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀
        ((fun p : Fin (M + 1) ↦
          LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
          ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
        (fun E :
            (∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let base : EFam :=
      fun p : Fin (M + 1) ↦
        LinearMap.toContinuousLinearMap (reverseEdge W B p)
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let νChart :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
    ContinuousAt density (base, (0 : EuclideanSpace ℝ ρreg)) →
    0 < density (base, (0 : EuclideanSpace ℝ ρreg)) →
    MeasurableSet {x : EFam |
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} →
    (∀ᵐ z ∂ νChart,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ νChart) < ∞ →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) Rmax →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
    ∃ R C : ℝ, ∃ U : Set EFam,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EFam × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  dsimp only
  intro hdensity_cont hdensity_pos hpos_meas hpos_chart hbase_chart hloss
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  let base : EFam :=
    fun p : Fin (M + 1) ↦
      LinearMap.toContinuousLinearMap (reverseEdge W B p)
  let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
    fun y ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
      (fun E : EFam ↦ E)
  let μ : Measure EFam := Measure.map sourceChart (m.restrict T)
  let νChart : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity
      (fun z : TopologyTuple ρ κ' ℝ ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := M) (ρ := ρ) (κ' := κ') z))
  let ρreg :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
  rcases exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
      (s := localSource) (Rmax := Rmax)
      (E := EuclideanSpace ℝ ρreg) hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hloss_R :
      ∀ᶠ x in nhdsWithin base localSource,
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet
        (W := W) (B := B) sourceData (m := m) (ν := ν)
        (loss := loss) (density := density) (t := t) (R := R) (c := c) (C := C)
        hR hc hC ht hpos_meas hpos_chart hbase_chart
        (by simpa [ρreg, base, localSource, EFam] using hloss_R)
        (by simpa [ρreg, base, localSource, EFam] using hdensity_nonneg)
        (by simpa [ρreg, base, localSource, EFam] using hdensity_le) with
    ⟨U, hUopen, hbaseU, hfinite⟩
  exact
    ⟨R, C, U, hR, hRle, hC, hUopen, by simpa [base] using hbaseU,
      by simpa [ρreg, sourceStratum, μ, sourceChart, T, base, localSource, EFam] using hfinite⟩

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
/-- Radius-shrinking canonical fixed-base retained-passive finite-integral
handoff from chart-side residual hypotheses and a continuous positive density.

This front end combines the canonical residual positive-set measurability lemma
with
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density`.
The chart-side residual positivity, chart-side finite residual integral, and
local loss lower bound remain explicit. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density_of_chartSide
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    [BorelSpace
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀
        ((fun p : Fin (M + 1) ↦
          LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
          ∀ p : Fin (M + 1),
            reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
        (fun E :
            (∀ p : Fin (M + 1),
              reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin (M + 1),
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let S : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let EFam := ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let base : EFam :=
      fun p : Fin (M + 1) ↦
        LinearMap.toContinuousLinearMap (reverseEdge W B p)
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀
        (fun E : EFam ↦ E)
    let μ := Measure.map sourceChart (m.restrict T)
    let νChart :=
      (m.restrict S).withDensity
        (fun z : TopologyTuple ρ κ' ℝ ↦
          ENNReal.ofReal
            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := M) (ρ := ρ) (κ' := κ') z))
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B (fun E : EFam ↦ E) r rEdge
    ContinuousAt density (base, (0 : EuclideanSpace ℝ ρreg)) →
    0 < density (base, (0 : EuclideanSpace ℝ ρreg)) →
    (∀ᵐ z ∂ νChart,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := ρ) (κ' := κ') z)))) →
    (∫⁻ z : TopologyTuple ρ κ' ℝ,
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
            (sourceChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t)) ∂ νChart) < ∞ →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) Rmax →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
    ∃ R C : ℝ, ∃ U : Set EFam,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EFam × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  dsimp only
  intro hdensity_cont hdensity_pos hpos_chart hbase_chart hloss
  let EFam := ∀ p : Fin (M + 1),
    reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
  have hpos_meas :
      MeasurableSet {x : EFam |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E) x)} := by
    simpa [EFam] using
      measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_id
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
  simpa [EFam] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13CanonicalLocalSource_formalProductAbsDet_continuousAt_pos_density
      (W := W) (B := B) sourceData (m := m) (ν := ν)
      (loss := loss) (density := density) (t := t) (Rmax := Rmax) (c := c)
      hRmax hc ht hdensity_cont hdensity_pos hpos_meas hpos_chart hbase_chart hloss

end PaperEndpointFixedBaseRegularCoordinateSourceData

end RetainedPassiveLocalJacobianMeasure

end Aoyagi
end DLN
end DLNFibre
