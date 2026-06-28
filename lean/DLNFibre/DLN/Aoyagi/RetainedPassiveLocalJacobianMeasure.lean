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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end RetainedPassiveLocalJacobianMeasure

end Aoyagi
end DLN
end DLNFibre
