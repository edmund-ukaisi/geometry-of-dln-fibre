import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawOrderReference

/-!
# Case 2 passive-theta original-volume readback from determinant domination

This file composes the same-shrink raw/source package with the original-volume
readback bridge.  The determinant-side reverse domination and source-density
lower bound remain explicit hypotheses.

It does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.
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

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

private instance instIsTopologicalAddGroup_tupleReal
    {N : ℕ} (d : Fin (N + 1) → ℕ) :
    IsTopologicalAddGroup (Tuple (k := ℝ) d) := by
  change IsTopologicalAddGroup
    (∀ i : Fin N, Fin (d i.succ) → Fin (d i.castSucc) → ℝ)
  infer_instance

private instance instBorelSpace_tupleReal
    {N : ℕ} (d : Fin (N + 1) → ℕ) :
    BorelSpace (Tuple (k := ℝ) d) := by
  change BorelSpace
    (∀ i : Fin N, Fin (d i.succ) → Fin (d i.castSucc) → ℝ)
  infer_instance

private noncomputable def originalTupleVolumeHaarScalarOfMap
    {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasurableSpace E] [BorelSpace E]
    (d : Fin (N + 1) → ℕ)
    (L : E ≃L[ℝ] Tuple (k := ℝ) d)
    (m : Measure E) [m.IsAddHaarMeasure] : NNReal := by
  haveI : IsTopologicalAddGroup (Tuple (k := ℝ) d) :=
    instIsTopologicalAddGroup_tupleReal d
  haveI : BorelSpace (Tuple (k := ℝ) d) := by
    change BorelSpace
      (∀ i : Fin N, Fin (d i.succ) → Fin (d i.castSucc) → ℝ)
    infer_instance
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  let hMapHaar : Measure.IsAddHaarMeasure (Measure.map L m) :=
    L.isAddHaarMeasure_map m
  exact
    @Measure.addHaarScalarFactor
      (Tuple (k := ℝ) d) _ _ _ _ _
      (Measure.map L m)
      (originalTupleVolume d)
      (isAddHaarMeasure_originalTupleVolume d)
      hMapHaar.toIsFiniteMeasureOnCompacts
      hMapHaar.toIsAddLeftInvariant

/-- A pointwise lower bound on the image of a restricted set gives the
corresponding a.e. lower bound after restricting any measure to that set. -/
theorem ae_restrict_comp_lower_of_forall_image_lower
    {α β : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {f : α → β} {g : β → ℝ≥0∞} {ε : ℝ≥0∞}
    (hV : MeasurableSet V) (h : ∀ y ∈ f '' V, ε ≤ g y) :
    ∀ᵐ x ∂ μ.restrict V, ε ≤ g (f x) := by
  filter_upwards [ae_restrict_mem hV] with x hx
  exact h (f x) ⟨x, hx, rfl⟩

/-- A pointwise upper bound on a measurable restricted set gives the
corresponding a.e. upper bound after restricting any measure to that set. -/
theorem ae_restrict_upper_of_forall_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} {K : ℝ}
    (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ K) :
    ∀ᵐ x ∂ μ.restrict s, f x ≤ K := by
  filter_upwards [ae_restrict_mem hs] with x hx
  exact h x hx

/-- A strict lower bound at a continuity point gives the corresponding
eventual non-strict lower bound. -/
theorem eventually_const_le_of_continuousAt_lt
    {α : Type*} [TopologicalSpace α] {f : α → ℝ≥0∞} {x₀ : α}
    {ε : ℝ≥0∞}
    (hf : ContinuousAt f x₀) (hε : ε < f x₀) :
    ∀ᶠ x in nhds x₀, ε ≤ f x := by
  have hnbd : Set.Ioi ε ∈ nhds (f x₀) :=
    isOpen_Ioi.mem_nhds hε
  exact
    (show ∀ᶠ x in nhds x₀, f x ∈ Set.Ioi ε from hf hnbd).mono
      fun _ hx ↦ le_of_lt hx

/-- A strict upper bound at a continuity point gives the corresponding
eventual non-strict upper bound. -/
theorem eventually_le_const_of_continuousAt_lt
    {α : Type*} [TopologicalSpace α] {f : α → ℝ} {x₀ : α} {K : ℝ}
    (hf : ContinuousAt f x₀) (hK : f x₀ < K) :
    ∀ᶠ x in nhds x₀, f x ≤ K := by
  have hnbd : Set.Iio K ∈ nhds (f x₀) :=
    isOpen_Iio.mem_nhds hK
  exact
    (show ∀ᶠ x in nhds x₀, f x ∈ Set.Iio K from hf hnbd).mono
      fun _ hx ↦ le_of_lt hx

/-- Convert readout support on a chart piece into support by an intersection
with the corresponding source-cylinder preimage.

This is pure set algebra.  The caller supplies the pointwise identity between
the readout of chart-produced edge families and the theta-side coordinate. -/
theorem chartPiece_subset_sourceChart_image_inter_preimage_of_readout_mem
    {Θ EdgeFamily Center : Type*} {sourceChart : Θ → EdgeFamily}
    {readout : EdgeFamily → Center} {y : Θ → Center} {V : Set Θ}
    {A : Set Center} {chartPiece : Set EdgeFamily}
    (hchartPiece : chartPiece ⊆ sourceChart '' V)
    (hreadout : ∀ z ∈ V, readout (sourceChart z) = y z)
    (hsupport : ∀ E ∈ chartPiece, readout E ∈ A) :
    chartPiece ⊆ sourceChart '' (V ∩ {z | y z ∈ A}) := by
  intro E hE
  rcases hchartPiece hE with ⟨z, hzV, rfl⟩
  refine ⟨z, ⟨hzV, ?_⟩, rfl⟩
  simpa [hreadout z hzV] using hsupport (sourceChart z) hE

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Concrete source-cylinder support bridge for the enlarged with-following
Case 2 endpoint source chart.

The enlarged readback stores the `C 1` selected-entry inverse readout as the
`yNext` coordinate.  Therefore a local left-inverse identity for the readback
turns chart-piece support by this readout into support by the theta-side
source cylinder. -/
theorem chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    {V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)}
    {chartPiece :
      Set
        (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ]
          reverseVertex W₂ p.succ)} :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    (∀ z ∈ V, readback (sourceChart z) = z) →
      chartPiece ⊆ sourceChart '' V →
        (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
          chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) := by
  intro Θ EdgeFamily sourceChart readback cOneReadout signedBox sourceCylinder
    hleft hchartPiece hsupport
  have hcOne :
      ∀ z ∈ V, cOneReadout (sourceChart z) = z.1.yNext := by
    intro z hz
    have hcongr := congrArg (fun w : Θ ↦ w.1.yNext) (hleft z hz)
    simpa [readback, cOneReadout,
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback,
      Case2PassiveThetaWithFollowingFactor.mk, Case2PassiveTheta.yNext] using hcongr
  simpa [sourceCylinder] using
    chartPiece_subset_sourceChart_image_inter_preimage_of_readout_mem
      (sourceChart := sourceChart) (readout := cOneReadout)
      (y := fun z : Θ ↦ z.1.yNext) (V := V)
      (A := signedBox) (chartPiece := chartPiece)
      hchartPiece hcOne hsupport

/-- If the chosen source neighborhood already lies in a support set, ordinary
source-chart image support upgrades to image support over the intersection. -/
theorem chartPiece_subset_sourceChart_image_inter_of_subset
    {Θ EdgeFamily : Type*} {sourceChart : Θ → EdgeFamily}
    {V A : Set Θ} {chartPiece : Set EdgeFamily}
    (hVA : V ⊆ A) (hchartPiece : chartPiece ⊆ sourceChart '' V) :
    chartPiece ⊆ sourceChart '' (V ∩ A) := by
  intro E hE
  rcases hchartPiece hE with ⟨z, hzV, rfl⟩
  exact ⟨z, ⟨hzV, hVA hzV⟩, rfl⟩

set_option linter.style.longLine false in
/-- A raw-order/source-chart endpoint patch is contained in the active endpoint
image when the chart piece is produced by source points in the signed-box
cylinder.

This is only set algebra.  The caller supplies the concrete injectivity of the
raw-order map on the determinant chart, the injectivity of the p.13 raw chart
on the raw-source chart, the pointwise source-chart compatibility, and the
active endpoint factorization. -/
theorem endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
    {Θ RawTuple EdgeFamily : Type*}
    {Y : Θ → RawTuple}
    {sourceChart : Θ → EdgeFamily}
    {rawOrderOnEndpoint : RawTuple → RawTuple}
    {rawDetChart rawSourceSet : Set RawTuple}
    {rawChart : RawTuple → EdgeFamily}
    {activeChart : Θ → Θ}
    {activeWriteback : Θ → RawTuple}
    {V sourceCylinder : Set Θ}
    {chartPiece : Set EdgeFamily}
    (hchartPiece : chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder))
    (hYdet : ∀ z ∈ V, Y z ∈ rawDetChart)
    (hrawMem : ∀ z ∈ V, rawOrderOnEndpoint (Y z) ∈ rawSourceSet)
    (hrawEq : ∀ z ∈ V, rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z)
    (hrawChart_inj : Set.InjOn rawChart rawSourceSet)
    (hrawOrder_inj : Set.InjOn rawOrderOnEndpoint rawDetChart)
    (hactive :
      ∀ z ∈ V, Y z = activeWriteback (activeChart z)) :
    rawDetChart ∩
        rawOrderOnEndpoint ⁻¹' (rawSourceSet ∩ rawChart ⁻¹' chartPiece) ⊆
      activeWriteback '' (activeChart '' (V ∩ sourceCylinder)) := by
  intro y hy
  rcases hy with ⟨hydet, hyraw, hychart⟩
  rcases hchartPiece hychart with ⟨z, hz, hsource_eq⟩
  have hzV : z ∈ V := hz.1
  have hraw_chart_eq :
      rawChart (rawOrderOnEndpoint y) =
        rawChart (rawOrderOnEndpoint (Y z)) := by
    calc
      rawChart (rawOrderOnEndpoint y) = sourceChart z := hsource_eq.symm
      _ = rawChart (rawOrderOnEndpoint (Y z)) := (hrawEq z hzV).symm
  have hraw_order_eq :
      rawOrderOnEndpoint y = rawOrderOnEndpoint (Y z) :=
    hrawChart_inj hyraw (hrawMem z hzV) hraw_chart_eq
  have hy_eq_Y : y = Y z :=
    hrawOrder_inj hydet (hYdet z hzV) hraw_order_eq
  refine ⟨activeChart z, ⟨z, hz, rfl⟩, ?_⟩
  exact (hy_eq_Y.trans (hactive z hzV)).symm

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Local endpoint-patch determinant/reference domination for the concrete p.13 raw patch.
/-- Localized determinant/reference domination on the concrete with-following
p.13 endpoint patch.

For a chart piece supported by the source-chart image over the selected-entry
source cylinder, the determinant-side endpoint patch

`rawDetChart ∩ rawOrderOnEndpoint ⁻¹'
  (rawSourceSet ∩ rawChart ⁻¹' chartPiece)`

is contained in the active selected-entry endpoint image.  The active endpoint
Haar theorem therefore gives a finite scalar domination by the endpoint
topology-tuple image of the same restricted reference source.

This is a localized endpoint-patch comparison.  It does not prove full
determinant-chart Haar transport, exact raw-Haar pushforward, Haar
normalization, source-density positivity, source-image/source-rank coverage,
original-prior transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_rawHaar_restrict_endpointPatch_le_smul_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
            ∃ Cdet : ℝ≥0∞,
              Cdet < ∞ ∧
                rawHaar.restrict
                    (rawDetChart ∩ rawOrderOnEndpoint ⁻¹'
                      (rawSourceSet ∩ rawChart ⁻¹' chartPiece)) ≤
                  Cdet • Measure.map Y (referenceSource.restrict V) := by
  intro Θ RawTuple EdgeFamily Y referenceSource sourceChart rawOrderOnEndpoint
    rawDetChart rawSourceSet rawChart pivotNext signedBox sourceCylinder
  let pivotSet : Set Θ :=
    {z | case2PassiveThetaPivotNonzero
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous (fun z : Θ ↦ z.1.yNext pivotNext) := by
      simpa [Θ, pivotNext, Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd.comp
            (continuous_fst : Continuous (fun z : Θ ↦ z.1))))
    simpa [pivotSet, pivotNext, case2PassiveThetaPivotNonzero] using
      (isOpen_ne.preimage hpivot_cont)
  let Gpivot : Set Θ := G ∩ pivotSet
  have hGpivot_open : IsOpen Gpivot := hGopen.inter hpivotSet_open
  have hz₀Gpivot : z₀ ∈ Gpivot := by
    exact ⟨hz₀G, by simpa [pivotSet] using hpivot₀⟩
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, sourceChart, rawOrderOnEndpoint,
          rawDetChart, rawSourceSet, rawChart] using
          exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ Gpivot hGpivot_open hz₀Gpivot) with
    ⟨V, hVopen, hz₀V, hVGpivot, hraw_point, _hmeasure_maps⟩
  have hVG : V ⊆ G := fun z hz ↦ (hVGpivot hz).1
  have hVpivot : V ⊆ pivotSet := fun z hz ↦ (hVGpivot hz).2
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece_sub_cylinder
  let activeChart : Θ → Θ :=
    fun z ↦
      ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
  let activeWriteback : Θ ≃L[ℝ] RawTuple :=
    (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
  let endpointPatch : Set RawTuple :=
    rawDetChart ∩ rawOrderOnEndpoint ⁻¹'
      (rawSourceSet ∩ rawChart ⁻¹' chartPiece)
  let activePatchImage := activeChart '' (V ∩ sourceCylinder)
  have hrawOrder_inj : Set.InjOn rawOrderOnEndpoint rawDetChart := by
    intro y hy y' hy' hyy
    have hyinv :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) = y := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy
    have hyinv' :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') = y' := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy'
    calc
      y =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) := hyinv.symm
      _ =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') := by rw [hyy]
      _ = y' := hyinv'
  have hrawChart_inj : Set.InjOn rawChart rawSourceSet := by
    intro y hy y' hy' hchart_eq
    let Sraw : Set RawTuple := rawSourceSet
    let H :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
        (K := ℝ) W₂ B₂ U₀ hU₀
    let yy : Sraw := ⟨y, by simpa [Sraw, rawSourceSet, RawTuple] using hy⟩
    let yy' : Sraw := ⟨y', by simpa [Sraw, rawSourceSet, RawTuple] using hy'⟩
    have hHval : (H yy).1 = (H yy').1 := by
      calc
        (H yy).1 = rawChart y := by
          simpa [H, yy, rawChart, Sraw, rawSourceSet, RawTuple] using
            paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy
        _ = rawChart y' := hchart_eq
        _ = (H yy').1 := by
          simpa [H, yy', rawChart, Sraw, rawSourceSet, RawTuple] using
            (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy').symm
    have hH : H yy = H yy' := Subtype.ext hHval
    exact congrArg Subtype.val (H.injective hH)
  have hraw_point_V :
      ∀ z ∈ V,
        Y z ∈ rawDetChart ∧
          rawOrderOnEndpoint (Y z) ∈ rawSourceSet ∧
          rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := by
    intro z hz
    let zfields : Θ :=
      Case2PassiveThetaWithFollowingFactor.mk
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
        z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2
    have hzfields_eq : zfields = z := by
      simp [zfields, Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.mk, Case2PassiveTheta.A1passive,
        Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
        Case2PassiveTheta.Ctop, Case2PassiveTheta.F3,
        Case2PassiveTheta.yNext]
    have hzraw_fields : zfields ∈ V := by
      simpa [hzfields_eq] using hz
    rcases
        hraw_point z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
          z.1.yNext z.2 hzraw_fields with
      ⟨hYdet_z, _hrawMem_z, _hrawEq_z, _hsource_z, _hread_z, _hleft_z⟩
    have hYdet_fields : Y zfields ∈ rawDetChart := by
      simpa [zfields, Y, rawDetChart, Case2PassiveThetaWithFollowingFactor.mk] using
        hYdet_z
    have hrawMem_fields : rawOrderOnEndpoint (Y zfields) ∈ rawSourceSet := by
      have hm :=
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (by simpa [rawDetChart] using hYdet_fields)
      change
        topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (Y zfields) ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      exact hm
    have hrawEq_fields :
        rawChart (rawOrderOnEndpoint (Y zfields)) = sourceChart zfields := by
      let retainedData : Θ →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
        fun z ↦
          case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
      have hdet_fields : (retainedData zfields).detChart := by
        exact
          (topologyTuple_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (retainedData zfields)).1
            (by simpa [Y, rawDetChart, retainedData] using hYdet_fields)
      have h :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
          (data := retainedData zfields) hdet_fields
      change
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
            (K := ℝ) W₂ B₂ U₀ hU₀
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
              (topologyTuple (retainedData zfields))) =
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            (K := ℝ) W₂ B₂ U₀ hU₀ (retainedData zfields)
      exact h
    subst zfields
    exact ⟨hYdet_fields, hrawMem_fields, hrawEq_fields⟩
  have hYdet : ∀ z ∈ V, Y z ∈ rawDetChart := fun z hz ↦
    (hraw_point_V z hz).1
  have hrawMem : ∀ z ∈ V, rawOrderOnEndpoint (Y z) ∈ rawSourceSet := fun z hz ↦
    (hraw_point_V z hz).2.1
  have hrawEq :
      ∀ z ∈ V, rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z :=
    fun z hz ↦ (hraw_point_V z hz).2.2
  have hactive_factor :
      ∀ z ∈ V, Y z = activeWriteback (activeChart z) := by
    intro z hz
    simpa [Θ, RawTuple, Y, activeWriteback, activeChart, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext z eNext e
  have hpatch : endpointPatch ⊆ activeWriteback '' activePatchImage := by
    simpa [endpointPatch, activePatchImage] using
      endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
        (Y := Y) (sourceChart := sourceChart)
        (rawOrderOnEndpoint := rawOrderOnEndpoint)
        (rawDetChart := rawDetChart) (rawSourceSet := rawSourceSet)
        (rawChart := rawChart) (activeChart := activeChart)
        (activeWriteback := activeWriteback) (V := V)
        (sourceCylinder := sourceCylinder) (chartPiece := chartPiece)
        hchartPiece_sub_cylinder hYdet hrawMem hrawEq hrawChart_inj
        hrawOrder_inj hactive_factor
  have hVpivot' :
      V ⊆ {z |
        case2PassiveThetaPivotNonzero
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1} := by
    intro z hz
    simpa [pivotSet] using hVpivot hz
  have hactive :
      ∃ Cdet : ℝ≥0∞,
        Cdet < ∞ ∧
          rawHaar.restrict endpointPatch ≤
            Cdet •
              case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                n hS hcont hnext eNext e Rres V := by
    simpa [Θ, RawTuple, pivotNext, signedBox, sourceCylinder, activeChart,
      activePatchImage, activeWriteback, endpointPatch] using
      (_root_.DLNFibre.DLN.Aoyagi.rawHaar_restrict_endpointPatch_le_smul_case2PassiveThetaWithFollowingFactorEndpointReferenceImage_of_subset_activeWriteback_activeSelectedEntryImage_inter_signedBox_of_subset_pivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext eNext e Rres V hVopen.measurableSet
        hVpivot' rawHaar endpointPatch hpatch)
  rcases hactive with ⟨Cdet, hCdet, hdom⟩
  refine ⟨Cdet, hCdet, ?_⟩
  simpa [endpointPatch, RawTuple, Y, referenceSource,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure] using hdom

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Source-cylinder support supplies the active endpoint containment needed by
-- the localized raw-patch source-density handoff.
/-- Localized with-following reverse raw-patch domination from source-cylinder
chart-piece support and a lower source-density bound.

For a p.13 chart piece supported by `sourceChart '' (V ∩ sourceCylinder)`,
the endpoint patch over `rawSourceSet ∩ rawChart ⁻¹' chartPiece` is contained
in the active selected-entry endpoint image.  The existing active-containment
raw-patch handoff then gives finite scalar domination of the raw patch by the
coordinate source measure.

This theorem keeps the source-density lower bound explicit.  It does not prove
full determinant-chart Haar transport, exact raw-Haar pushforward,
Haar-scalar normalization, source-density positivity, source-image/source-rank
coverage, original-prior transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity : Θ → ℝ≥0∞ := fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
        ∀ {ε : ℝ≥0∞},
          MeasurableSet chartPiece →
            chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
              (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                ε ≠ 0 →
                  ε ≠ ∞ →
                    ∃ Cdet : ℝ≥0∞,
                      Cdet < ∞ ∧
                        let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                        let D := Cdet * ε⁻¹
                        D < ∞ ∧
                          rawHaar.restrict P ≤
                            D • Measure.map rawMap
                              (coordinateSourceMeasure.restrict V) := by
  intro Θ RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily
    sourceChart sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet rawChart pivotNext signedBox
    sourceCylinder activeChart activeWriteback
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, sourceChart, rawOrderOnEndpoint,
          rawDetChart, rawSourceSet, rawChart] using
          exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vraw, hVraw_open, hz₀Vraw, hVrawG, hraw_point, _hraw_measure⟩
  haveI : OpensMeasurableSpace RawTuple := by
    dsimp [RawTuple]
    infer_instance
  haveI :
      OpensMeasurableSpace
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) := by
    infer_instance
  rcases
      (by
        simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ,
          EdgeFamily, sourceChart, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, rawSourceSet, pivotNext,
          signedBox, sourceCylinder, activeChart, activeWriteback] using
          exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres Vraw
            hVraw_open hz₀Vraw) with
    ⟨V, hV_open, hz₀V, hV_Vraw, hraw_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVrawG (hV_Vraw hz)
  refine ⟨V, hV_open, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece
    hchartPiece_sub_cylinder hsource_lower hε_ne_zero hε_ne_top
  let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
  have hP_sub : P ⊆ rawSourceSet := by
    intro y hy
    exact hy.1
  have hendpoint_nm :
      NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar := by
    simpa [P, RawTuple, EdgeFamily, rawOrderOnEndpoint, rawDetChart,
      rawSourceSet, rawChart] using
      nullMeasurableSet_topologyTupleDetChart_inter_rawOrder_preimage_p13RawOrderSourceChart_chartPiece
        (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
        rawHaar hchartPiece
  have hrawOrder_inj : Set.InjOn rawOrderOnEndpoint rawDetChart := by
    intro y hy y' hy' hyy
    have hyinv :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) = y := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy
    have hyinv' :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') = y' := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy'
    calc
      y =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) := hyinv.symm
      _ =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') := by rw [hyy]
      _ = y' := hyinv'
  have hrawChart_inj : Set.InjOn rawChart rawSourceSet := by
    intro y hy y' hy' hchart_eq
    let Sraw : Set RawTuple := rawSourceSet
    let H :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
        (K := ℝ) W₂ B₂ U₀ hU₀
    let yy : Sraw := ⟨y, by simpa [Sraw, rawSourceSet, RawTuple] using hy⟩
    let yy' : Sraw := ⟨y', by simpa [Sraw, rawSourceSet, RawTuple] using hy'⟩
    have hHval : (H yy).1 = (H yy').1 := by
      calc
        (H yy).1 = rawChart y := by
          simpa [H, yy, rawChart, Sraw, rawSourceSet, RawTuple] using
            paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy
        _ = rawChart y' := hchart_eq
        _ = (H yy').1 := by
          simpa [H, yy', rawChart, Sraw, rawSourceSet, RawTuple] using
            (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy').symm
    have hH : H yy = H yy' := Subtype.ext hHval
    exact congrArg Subtype.val (H.injective hH)
  have hraw_point_V :
      ∀ z ∈ V,
        Y z ∈ rawDetChart ∧
          rawOrderOnEndpoint (Y z) ∈ rawSourceSet ∧
          rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := by
    intro z hz
    let zfields : Θ :=
      Case2PassiveThetaWithFollowingFactor.mk
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
        z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2
    have hzfields_eq : zfields = z := by
      simp [zfields, Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.mk, Case2PassiveTheta.A1passive,
        Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
        Case2PassiveTheta.Ctop, Case2PassiveTheta.F3,
        Case2PassiveTheta.yNext]
    have hzraw_fields :
        zfields ∈ Vraw := by
      simpa [hzfields_eq] using hV_Vraw hz
    rcases
        hraw_point z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
          z.1.yNext z.2 hzraw_fields with
      ⟨hYdet_z, _hrawMem_z, _hrawEq_z, _hsource_z, _hread_z, _hleft_z⟩
    have hYdet_fields : Y zfields ∈ rawDetChart := by
      simpa [zfields, Y, rawDetChart, Case2PassiveThetaWithFollowingFactor.mk] using
        hYdet_z
    have hrawMem_fields : rawOrderOnEndpoint (Y zfields) ∈ rawSourceSet := by
      have hm :=
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (by simpa [rawDetChart] using hYdet_fields)
      change
        topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (Y zfields) ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      exact hm
    have hrawEq_fields :
        rawChart (rawOrderOnEndpoint (Y zfields)) = sourceChart zfields := by
      let retainedData : Θ →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
        fun z ↦
          case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
      have hdet_fields : (retainedData zfields).detChart := by
        exact
          (topologyTuple_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (retainedData zfields)).1
            (by simpa [Y, rawDetChart, retainedData] using hYdet_fields)
      have h :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
          (data := retainedData zfields) hdet_fields
      change
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
            (K := ℝ) W₂ B₂ U₀ hU₀
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
              (topologyTuple (retainedData zfields))) =
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            (K := ℝ) W₂ B₂ U₀ hU₀ (retainedData zfields)
      exact h
    subst zfields
    exact ⟨hYdet_fields, hrawMem_fields, hrawEq_fields⟩
  have hYdet : ∀ z ∈ V, Y z ∈ rawDetChart := fun z hz ↦
    (hraw_point_V z hz).1
  have hrawMem : ∀ z ∈ V, rawOrderOnEndpoint (Y z) ∈ rawSourceSet := fun z hz ↦
    (hraw_point_V z hz).2.1
  have hrawEq :
      ∀ z ∈ V, rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := fun z hz ↦
    (hraw_point_V z hz).2.2
  have hactive_factor :
      ∀ z ∈ V, Y z = activeWriteback (activeChart z) := by
    intro z hz
    simpa [Θ, RawTuple, Y, activeWriteback, activeChart, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext z eNext e
  have hpatch :
      rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P ⊆
        activeWriteback '' (activeChart '' (V ∩ sourceCylinder)) := by
    simpa [P] using
      endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
        (Y := Y) (sourceChart := sourceChart)
        (rawOrderOnEndpoint := rawOrderOnEndpoint)
        (rawDetChart := rawDetChart) (rawSourceSet := rawSourceSet)
        (rawChart := rawChart) (activeChart := activeChart)
        (activeWriteback := activeWriteback) (V := V)
        (sourceCylinder := sourceCylinder) (chartPiece := chartPiece)
        hchartPiece_sub_cylinder hYdet hrawMem hrawEq hrawChart_inj
        hrawOrder_inj hactive_factor
  rcases
      hraw_package rawHaar (P := P) (ε := ε)
        hP_sub hendpoint_nm hpatch hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDfinite, hdom⟩
  refine ⟨Cdet, hCdet, ?_⟩
  dsimp only
  exact ⟨hDfinite, hdom⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- With-following localized determinant/source-density wrapper for chart-piece readback.
/-- Same-shrink with-following original-volume readback domination from
localized endpoint-patch determinant domination and a lower source-density
bound.

For a p.13 chart piece, the raw patch is
`rawSourceSet ∩ rawChart ⁻¹' chartPiece`.  It is enough to assume determinant
reverse domination only on the corresponding endpoint patch
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P`.  The theorem then feeds the
localized raw-patch domination into the localized original-volume readback
bridge.

The endpoint-patch domination and source-density lower bound remain explicit
hypotheses.  This theorem does not prove determinant-chart Haar transport,
raw-order Haar transport, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      NullMeasurableSet
                          (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar →
                        rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                          Cdet • Measure.map Y (referenceSource.restrict V) →
                          Cdet < ∞ →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  let cHaar :=
                                    (originalTupleVolumeHaarScalarOfMap d
                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                        W₂ B₂ U₀) rawHaar)
                                  let D := Cdet * ε⁻¹
                                  D < ∞ ∧
                                    AEMeasurable readback
                                      (originalVolume.restrict chartPiece) ∧
                                      Measure.map readback
                                          (originalVolume.restrict chartPiece) ≤
                                        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                          coordinateSourceMeasure.restrict G) := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vrb, hVrbopen, hz₀Vrb, hVrbG, hleft_rb, hsource_inj_rb,
      hsource_contOn_rb, _hsource_image_rb, himage_p13_rb, hreadback_bridge⟩
  rcases
      (by
        simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ,
          EdgeFamily, sourceChart, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, rawSourceSet] using
          exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres Vrb hVrbopen hz₀Vrb) with
    ⟨V, hVopen, hz₀V, hV_vrb, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVrbG (hV_vrb hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_rb z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 (hV_vrb hz)
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj_rb (hV_vrb hz) (hV_vrb hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn_rb.mono hV_vrb
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_rb (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 (hV_vrb hzV) rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV,
    hsource_contOnV, hsource_imageV, himage_p13V, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P hendpoint_nm hdet_dom hCdet hsource_lower
    hε_ne_zero hε_ne_top cHaar D
  have hchartPiece_sub_vrb : chartPiece ⊆ sourceChart '' Vrb := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hV_vrb hzV, rfl⟩
  have hP_sub : P ⊆ rawSourceSet := by
    intro y hy
    exact hy.1
  have hrawPatch_sub : rawSourceSet ∩ rawChart ⁻¹' chartPiece ⊆ P := by
    intro y hy
    simpa [P] using hy
  rcases
      hraw_dom_package rawHaar (P := P) (Cdet := Cdet) (ε := ε)
        hP_sub hendpoint_nm hdet_dom hCdet hsource_lower hε_ne_zero
        hε_ne_top with
    ⟨hDfinite, hraw_dom⟩
  have hrestrict_vrb :
      (coordinateSourceMeasure.restrict V).restrict Vrb =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hV_vrb hzV))
  have hraw_dom_bridge :
      rawHaar.restrict P ≤
        D • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vrb) := by
    simpa [RawTuple, rawMap, coordinateSourceMeasure, D, hrestrict_vrb] using hraw_dom
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
            (coordinateSourceMeasure.restrict V).restrict G) := by
    simpa [RawTuple, rawMap, rawSourceSet, rawChart, d, originalVolume,
      cHaar, D] using
      hreadback_bridge (coordinateSourceMeasure.restrict V) rawHaar
        chartPiece P (D := D) hchartPiece hchartPiece_sub_vrb hP_sub
        hrawPatch_sub hraw_dom_bridge
  have hV_le_G :
      coordinateSourceMeasure.restrict V ≤
        (1 : ℝ≥0∞) • coordinateSourceMeasure.restrict G := by
    simpa using (Measure.restrict_mono hVG le_rfl)
  have hrestrict_G :
      (coordinateSourceMeasure.restrict V).restrict G =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hVG hzV))
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
          coordinateSourceMeasure.restrict G := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) * (1 : ℝ≥0∞)) •
            coordinateSourceMeasure.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul
        (by simpa [hrestrict_G] using hreadback_volume.2) hV_le_G
    simpa [mul_one] using hstep
  exact ⟨by simpa [D] using hDfinite, hreadback_volume.1, hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper obtains the raw-patch scalar from active endpoint containment
-- before applying the same-shrink original-volume readback bridge.
/-- Same-shrink with-following original-volume readback domination from active
endpoint-image containment and a lower source-density bound.

For a p.13 chart piece, the raw patch is
`rawSourceSet ∩ rawChart ⁻¹' chartPiece`, and the endpoint patch is
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P`.  The p.13 measurability lemma
supplies the endpoint-patch null-measurability socket.  Active endpoint-image
containment supplies, through the raw-patch active-containment theorem, a
finite endpoint scalar `Cdet`; the original-volume readback bridge consumes
the resulting raw domination with scalar `D = Cdet * ε⁻¹`.

The active containment and source-density lower bound remain explicit
hypotheses.  This theorem does not prove active containment from chart-piece
support, determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      {z | z.1.yNext ∈ signedBox}
    let activeChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ≃L[ℝ]
          RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointPatch : Set RawTuple :=
                        rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                      let activePatchImage := activeChart '' (V ∩ sourceCylinder)
                      endpointPatch ⊆ activeWriteback '' activePatchImage →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              ∃ Cdet : ℝ≥0∞,
                                Cdet < ∞ ∧
                                  let cHaar :=
                                    (originalTupleVolumeHaarScalarOfMap d
                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                        W₂ B₂ U₀) rawHaar)
                                  let D := Cdet * ε⁻¹
                                  D < ∞ ∧
                                    AEMeasurable readback
                                      (originalVolume.restrict chartPiece) ∧
                                      Measure.map readback
                                          (originalVolume.restrict chartPiece) ≤
                                        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                          coordinateSourceMeasure.restrict G) := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vrb, hVrbopen, hz₀Vrb, hVrbG, hleft_rb, hsource_inj_rb,
      hsource_contOn_rb, _hsource_image_rb, himage_p13_rb, hreadback_bridge⟩
  rcases
      (by
        simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ,
          EdgeFamily, sourceChart, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, rawSourceSet, pivotNext,
          signedBox, sourceCylinder, activeChart, activeWriteback] using
          exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres Vrb hVrbopen hz₀Vrb) with
    ⟨V, hVopen, hz₀V, hV_vrb, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVrbG (hV_vrb hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_rb z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 (hV_vrb hz)
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj_rb (hV_vrb hz) (hV_vrb hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn_rb.mono hV_vrb
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_rb (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 (hV_vrb hzV) rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV,
    hsource_contOnV, hsource_imageV, himage_p13V, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_image
    P endpointPatch activePatchImage hpatch hsource_lower hε_ne_zero hε_ne_top
  have hchartPiece_sub_vrb : chartPiece ⊆ sourceChart '' Vrb := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hV_vrb hzV, rfl⟩
  have hp13 :
      P ⊆ rawSourceSet ∧
        NullMeasurableSet endpointPatch rawHaar := by
    simpa [P, endpointPatch, RawTuple, EdgeFamily, rawOrderOnEndpoint,
      rawDetChart, rawSourceSet, rawChart] using
      nullMeasurableSet_topologyTupleDetChart_inter_rawOrder_preimage_p13RawOrderSourceChart_chartPiece
        (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
        rawHaar hchartPiece
  have hrawPatch_sub : rawSourceSet ∩ rawChart ⁻¹' chartPiece ⊆ P := by
    intro y hy
    simpa [P] using hy
  rcases
      hraw_dom_package rawHaar (P := P) (ε := ε)
        hp13.1 hp13.2 hpatch hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDfinite, hraw_dom⟩
  refine ⟨Cdet, hCdet, ?_⟩
  dsimp only
  let cHaar :=
    (originalTupleVolumeHaarScalarOfMap d
      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
        W₂ B₂ U₀) rawHaar)
  let D := Cdet * ε⁻¹
  have hrestrict_vrb :
      (coordinateSourceMeasure.restrict V).restrict Vrb =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hV_vrb hzV))
  have hraw_dom_bridge :
      rawHaar.restrict P ≤
        D • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vrb) := by
    simpa [RawTuple, rawMap, coordinateSourceMeasure, D, hrestrict_vrb] using hraw_dom
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
            (coordinateSourceMeasure.restrict V).restrict G) := by
    simpa [RawTuple, rawMap, rawSourceSet, rawChart, d, originalVolume,
      cHaar, D] using
      hreadback_bridge (coordinateSourceMeasure.restrict V) rawHaar
        chartPiece P (D := D) hchartPiece hchartPiece_sub_vrb
        hp13.1 hrawPatch_sub hraw_dom_bridge
  have hV_le_G :
      coordinateSourceMeasure.restrict V ≤
        (1 : ℝ≥0∞) • coordinateSourceMeasure.restrict G := by
    simpa using (Measure.restrict_mono hVG le_rfl)
  have hrestrict_G :
      (coordinateSourceMeasure.restrict V).restrict G =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hVG hzV))
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
          coordinateSourceMeasure.restrict G) := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) * (1 : ℝ≥0∞)) •
            coordinateSourceMeasure.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul
        (by simpa [hrestrict_G] using hreadback_volume.2) hV_le_G
    simpa [mul_one] using hstep
  exact ⟨by simpa [D] using hDfinite, hreadback_volume.1,
    by simpa [cHaar, D] using hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant proves active endpoint containment from source-cylinder support.
/-- Same-shrink with-following original-volume readback domination from
source-cylinder chart-piece support and a lower source-density bound.

Compared with
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower`,
the chart-piece support is strengthened to
`chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)`.  Raw/source compatibility,
injectivity of the raw-order and p.13 raw-chart maps, and the active endpoint
factorization then prove the endpoint-patch containment required by the active
containment wrapper.

This theorem still does not derive source-cylinder support from ordinary
`chartPiece ⊆ sourceChart '' V`; that requires a separate support bridge such
as C-one readout support or a shrink with `V ⊆ sourceCylinder`.  It also does
not prove determinant-chart Haar transport, exact raw-Haar pushforward, Haar
normalization, source-density positivity, source coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
                      (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∃ Cdet : ℝ≥0∞,
                              Cdet < ∞ ∧
                                let cHaar :=
                                  (originalTupleVolumeHaarScalarOfMap d
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀) rawHaar)
                                let D := Cdet * ε⁻¹
                                D < ∞ ∧
                                  AEMeasurable readback
                                    (originalVolume.restrict chartPiece) ∧
                                    Measure.map readback
                                        (originalVolume.restrict chartPiece) ≤
                                      ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                        coordinateSourceMeasure.restrict G) := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, sourceChart, readback,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, rawChart] using
          exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vraw, hVraw_open, hz₀Vraw, hVrawG, hraw_point, _hraw_measure⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet,
          rawChart, d, originalVolume, pivotNext, signedBox, sourceCylinder,
          activeChart, activeWriteback] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres Vraw hVraw_open hz₀Vraw) with
    ⟨V, hV_open, hz₀V, hV_Vraw, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hactive_package⟩
  have hVG : V ⊆ G := by
    intro z hz
    exact hVrawG (hV_Vraw hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_V z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_V (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hV_open, hz₀V, hVG, hleftV, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13V, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_cylinder
    hsource_lower hε_ne_zero hε_ne_top
  have hchartPiece_sub_image : chartPiece ⊆ sourceChart '' V := by
    intro E hE
    rcases hchartPiece_sub_cylinder hE with ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, rfl⟩
  let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
  let endpointPatch : Set RawTuple := rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
  let activePatchImage := activeChart '' (V ∩ sourceCylinder)
  have hrawOrder_inj : Set.InjOn rawOrderOnEndpoint rawDetChart := by
    intro y hy y' hy' hyy
    have hyinv :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) = y := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy
    have hyinv' :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') = y' := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy'
    calc
      y =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) := hyinv.symm
      _ =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') := by rw [hyy]
      _ = y' := hyinv'
  have hrawChart_inj : Set.InjOn rawChart rawSourceSet := by
    intro y hy y' hy' hchart_eq
    let Sraw : Set RawTuple := rawSourceSet
    let H :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
        (K := ℝ) W₂ B₂ U₀ hU₀
    let yy : Sraw := ⟨y, by simpa [Sraw, rawSourceSet, RawTuple] using hy⟩
    let yy' : Sraw := ⟨y', by simpa [Sraw, rawSourceSet, RawTuple] using hy'⟩
    have hHval : (H yy).1 = (H yy').1 := by
      calc
        (H yy).1 = rawChart y := by
          simpa [H, yy, rawChart, Sraw, rawSourceSet, RawTuple] using
            paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy
        _ = rawChart y' := hchart_eq
        _ = (H yy').1 := by
          simpa [H, yy', rawChart, Sraw, rawSourceSet, RawTuple] using
            (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy').symm
    have hH : H yy = H yy' := Subtype.ext hHval
    exact congrArg Subtype.val (H.injective hH)
  have hraw_point_V :
      ∀ z ∈ V,
        Y z ∈ rawDetChart ∧
          rawOrderOnEndpoint (Y z) ∈ rawSourceSet ∧
          rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := by
    intro z hz
    let zfields : Θ :=
      Case2PassiveThetaWithFollowingFactor.mk
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
        z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2
    have hzfields_eq : zfields = z := by
      simp [zfields, Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.mk, Case2PassiveTheta.A1passive,
        Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
        Case2PassiveTheta.Ctop, Case2PassiveTheta.F3,
        Case2PassiveTheta.yNext]
    have hzraw_fields :
        zfields ∈ Vraw := by
      simpa [hzfields_eq] using hV_Vraw hz
    rcases
        hraw_point z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
          z.1.yNext z.2 hzraw_fields with
      ⟨hYdet_z, _hrawMem_z, _hrawEq_z, _hsource_z, _hread_z, _hleft_z⟩
    have hYdet_fields : Y zfields ∈ rawDetChart := by
      simpa [zfields, Y, rawDetChart, Case2PassiveThetaWithFollowingFactor.mk] using
        hYdet_z
    have hrawMem_fields : rawOrderOnEndpoint (Y zfields) ∈ rawSourceSet := by
      have hm :=
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (by simpa [rawDetChart] using hYdet_fields)
      change
        topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (Y zfields) ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      exact hm
    have hrawEq_fields :
        rawChart (rawOrderOnEndpoint (Y zfields)) = sourceChart zfields := by
      let retainedData : Θ →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
        fun z ↦
          case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
      have hdet_fields : (retainedData zfields).detChart := by
        exact
          (topologyTuple_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (retainedData zfields)).1
            (by simpa [Y, rawDetChart, retainedData] using hYdet_fields)
      have h :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
          (data := retainedData zfields) hdet_fields
      change
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
            (K := ℝ) W₂ B₂ U₀ hU₀
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
              (topologyTuple (retainedData zfields))) =
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            (K := ℝ) W₂ B₂ U₀ hU₀ (retainedData zfields)
      exact h
    subst zfields
    exact ⟨hYdet_fields, hrawMem_fields, hrawEq_fields⟩
  have hYdet : ∀ z ∈ V, Y z ∈ rawDetChart := fun z hz ↦
    (hraw_point_V z hz).1
  have hrawMem : ∀ z ∈ V, rawOrderOnEndpoint (Y z) ∈ rawSourceSet := fun z hz ↦
    (hraw_point_V z hz).2.1
  have hrawEq :
      ∀ z ∈ V, rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := fun z hz ↦
    (hraw_point_V z hz).2.2
  have hactive_factor :
      ∀ z ∈ V, Y z = activeWriteback (activeChart z) := by
    intro z hz
    simpa [Θ, RawTuple, Y, activeWriteback, activeChart, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext z eNext e
  have hpatch : endpointPatch ⊆ activeWriteback '' activePatchImage := by
    simpa [P, endpointPatch, activePatchImage] using
      endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
        (Y := Y) (sourceChart := sourceChart)
        (rawOrderOnEndpoint := rawOrderOnEndpoint)
        (rawDetChart := rawDetChart) (rawSourceSet := rawSourceSet)
        (rawChart := rawChart) (activeChart := activeChart)
        (activeWriteback := activeWriteback) (V := V)
        (sourceCylinder := sourceCylinder) (chartPiece := chartPiece)
        hchartPiece_sub_cylinder hYdet hrawMem hrawEq hrawChart_inj
        hrawOrder_inj hactive_factor
  rcases
      hactive_package rawHaar chartPiece (ε := ε) hchartPiece
        hchartPiece_sub_image hpatch hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDfinite, hreadback_meas, hreadback_le_vraw⟩
  refine ⟨Cdet, hCdet, ?_⟩
  dsimp only
  let cHaar :=
    (originalTupleVolumeHaarScalarOfMap d
      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
        W₂ B₂ U₀) rawHaar)
  let D := Cdet * ε⁻¹
  refine ⟨by simpa [D] using hDfinite, hreadback_meas, ?_⟩
  have hVraw_le_G :
      coordinateSourceMeasure.restrict Vraw ≤
        (1 : ℝ≥0∞) • coordinateSourceMeasure.restrict G := by
    simpa [Θ] using (Measure.restrict_mono (μ := coordinateSourceMeasure) hVrawG le_rfl)
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
          coordinateSourceMeasure.restrict G) := by
    have hstep :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) * (1 : ℝ≥0∞)) •
            coordinateSourceMeasure.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul
        (by simpa [Θ, cHaar, D] using hreadback_le_vraw) hVraw_le_G
    simpa [Θ, mul_one] using hstep
  exact by simpa [Θ, cHaar, D] using hmap_le_G

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant obtains source-cylinder support from C-one signed-box support.
/-- Same-shrink with-following original-volume readback domination from C-one
readout support and a lower source-density bound.

The caller supplies ordinary local chart-piece support
`chartPiece ⊆ sourceChart '' V` and the pointwise signed-box condition
`cOneReadout E ∈ signedBox` on the chart piece.  The local readback
left-inverse identifies `cOneReadout (sourceChart z)` with `z.1.yNext`, so
these hypotheses give the source-cylinder support consumed by
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower`.

This theorem does not prove the C-one signed-box condition for arbitrary chart
pieces.  It also does not prove determinant-chart Haar transport, exact
raw-Haar pushforward, Haar normalization, source-density positivity, source
coverage, source-rank coverage, original source-prior transport, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V,
                E ∈
                  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
                    (K := ℝ) W₂ B₂ U₀ hU₀) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              ∃ Cdet : ℝ≥0∞,
                                Cdet < ∞ ∧
                                  let cHaar :=
                                    (originalTupleVolumeHaarScalarOfMap d
                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                        W₂ B₂ U₀) rawHaar)
                                  let D := Cdet * ε⁻¹
                                  D < ∞ ∧
                                    AEMeasurable readback
                                      (originalVolume.restrict chartPiece) ∧
                                      Measure.map readback
                                          (originalVolume.restrict chartPiece) ≤
                                        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                          coordinateSourceMeasure.restrict G) := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback cOneReadout sourceDensity coordinateSourceMeasure d
    originalVolume signedBox sourceCylinder
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          d, originalVolume, signedBox, sourceCylinder] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V,
      hsource_cylinder_package⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_V z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13V :
      ∀ E ∈ sourceChart '' V,
        E ∈
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
            (K := ℝ) W₂ B₂ U₀ hU₀ := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_V (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hV_open, hz₀V, hVG, hleftV, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13V, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_image
    hcOne_support hsource_lower hε_ne_zero hε_ne_top
  have hchartPiece_sub_cylinder :
      chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) := by
    simpa [Θ, EdgeFamily, sourceChart, readback, cOneReadout, signedBox,
      sourceCylinder] using
      chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
        W₂ B₂ n hS hcont hnext hU₀ eNext e Rres
        hleftV hchartPiece_sub_image hcOne_support
  exact
    hsource_cylinder_package rawHaar chartPiece (ε := ε)
      hchartPiece hchartPiece_sub_cylinder hsource_lower hε_ne_zero hε_ne_top

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper composes two large localized measure packages through long let-blocks.
/-- Same-shrink with-following original-volume readback domination from a
localized endpoint-image weighted-Haar identity and lower endpoint density
bound.

For the p.13 chart piece, the endpoint patch is
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' (rawSourceSet ∩ rawChart ⁻¹' chartPiece)`.
The p.13 measurability lemma supplies the null-measurable-set socket, while the
endpoint weighted-Haar handoff supplies the determinant-side finite-scalar
domination socket consumed by the existing readback theorem.

The endpoint image identity and lower bound remain explicit hypotheses.  This
does not prove determinant-chart Haar transport, raw-order Haar transport,
source-image coverage, original source-prior transport, normal crossings, pole
order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      endpointReferenceImage =
                          (rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict
                              (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  let cHaar :=
                                    (originalTupleVolumeHaarScalarOfMap d
                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                        W₂ B₂ U₀) rawHaar)
                                  let D := Cdet * ε⁻¹
                                  D < ∞ ∧
                                    AEMeasurable readback
                                      (originalVolume.restrict chartPiece) ∧
                                      Measure.map readback
                                          (originalVolume.restrict chartPiece) ≤
                                        ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                          coordinateSourceMeasure.restrict G) := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P endpointReferenceImage hendpoint hCdet
    hendpoint_lower hsource_lower hε_ne_zero hε_ne_top cHaar D
  dsimp [RawTuple] at rawHaar endpointReferenceImage hendpoint hendpoint_lower ⊢
  have hp13 :
      P ⊆ rawSourceSet ∧
        NullMeasurableSet
          (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar := by
    simpa [P, RawTuple, EdgeFamily, rawOrderOnEndpoint, rawDetChart,
      rawSourceSet, rawChart] using
      nullMeasurableSet_topologyTupleDetChart_inter_rawOrder_preimage_p13RawOrderSourceChart_chartPiece
        (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
        rawHaar hchartPiece
  have hdet_dom :
      rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
        Cdet • Measure.map Y (referenceSource.restrict V) := by
    simpa [P, RawTuple, rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity,
      endpointReferenceImage, Y, referenceSource] using
      rawHaar_restrict_endpointPatch_le_smul_case2PassiveThetaWithFollowingFactorEndpointReferenceImage_of_eq_withDensity_formalProductAbsDet_of_one_le_mul_density
        W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e Rres V
        rawHaar (P := P) (Cdet := Cdet) hendpoint hCdet hendpoint_lower
  simpa [P, RawTuple, EdgeFamily, rawOrderOnEndpoint, rawDetChart,
    endpointReferenceImage, endpointJacobianDensity, rawSourceSet, rawChart, d,
    originalVolume, cHaar, D] using
    hvolume_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
      hchartPiece hchartPiece_sub_image (by simpa [P] using hp13.2)
      (by simpa [P] using hdet_dom) hCdet hsource_lower hε_ne_zero hε_ne_top

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper elaborates through the large localized readback package.
/-- Same-shrink with-following original-prior readback domination from
localized endpoint-patch determinant domination, a lower source-density bound,
and a local upper bound for the original prior density.

This is the prior analogue of
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower`.
The raw patch remains
`rawSourceSet ∩ rawChart ⁻¹' chartPiece`, and the determinant-side hypothesis
remains localized to
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' (rawSourceSet ∩ rawChart ⁻¹' chartPiece)`.

The endpoint-patch domination, source-density lower bound, and prior-density
upper bound remain explicit hypotheses.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior origin, source-image coverage, source-rank coverage, normal
crossings, pole order, finite-integral transfer, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      NullMeasurableSet
                          (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar →
                        rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                          Cdet • Measure.map Y (referenceSource.restrict V) →
                          Cdet < ∞ →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                      density E ≤ Kprior) →
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict G := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P hendpoint_nm hdet_dom hCdet hsource_lower
    hε_ne_zero hε_ne_top density Kprior hdensity cHaar Ddet Dvol Cprior
  rcases
      (by
        simpa [RawTuple, EdgeFamily, d, originalVolume, cHaar, Ddet, Dvol, P] using
          hvolume_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
            hchartPiece hchartPiece_sub_image hendpoint_nm hdet_dom hCdet
            hsource_lower hε_ne_zero hε_ne_top) with
    ⟨hDdet, hreadback_volume, hvolume_readback_dom⟩
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  haveI :
      SFinite
        (originalEdgeFamilyVolume (V := reverseVertex W₂)
          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)) := by
    dsimp [originalEdgeFamilyVolume, originalTupleVolume, originalCoordinateVolume]
    infer_instance
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume hvolume_readback_dom hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  exact ⟨hCprior,
    by simpa [originalPriorPiece] using hprior_readback.1,
    by simpa [originalPriorPiece, Cprior] using hprior_readback.2⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This adapter sharpens active-containment readback domination to the returned shrink.
/-- Same-shrink with-following original-prior readback domination from active
endpoint-image containment.

This is a support-sharpened version of
`exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper`.
The active-containment theorem gives domination by the ambient
`coordinateSourceMeasure.restrict G`; chart-piece support inside
`sourceChart '' V`, the returned local left inverse, and `V ⊆ G` sharpen the
target to `coordinateSourceMeasure.restrict V`.

The active containment, source-density lower bound, prior-density upper bound,
and `ε ≠ 0, ∞` remain explicit hypotheses.  This theorem does not prove
active containment, source-density positivity, determinant-chart Haar
transport, exact raw-Haar pushforward, Haar normalization, source coverage,
source-rank coverage, original source-prior transport beyond the bounded-
density comparison, normal crossings, pole order, finite-integral transfer, or
RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      {z | z.1.yNext ∈ signedBox}
    let activeChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ≃L[ℝ]
          RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointPatch : Set RawTuple :=
                        rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                      let activePatchImage := activeChart '' (V ∩ sourceCylinder)
                      endpointPatch ⊆ activeWriteback '' activePatchImage →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                  density E ≤ Kprior) →
                                  ∃ Cdet : ℝ≥0∞,
                                    Cdet < ∞ ∧
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict V := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume
    pivotNext signedBox sourceCylinder activeChart activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume, pivotNext, signedBox, sourceCylinder, activeChart,
          activeWriteback] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_image
    P endpointPatch activePatchImage hpatch hsource_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  rcases
      hvolume_package rawHaar chartPiece (ε := ε) hchartPiece
        hchartPiece_sub_image hpatch hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDdet, hreadback_volume, hvolume_readback_dom⟩
  let cHaar :=
    (originalTupleVolumeHaarScalarOfMap d
      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
        W₂ B₂ U₀) rawHaar)
  let Ddet := Cdet * ε⁻¹
  let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
  let Cprior := ENNReal.ofReal Kprior * Dvol
  let μprior :=
    originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density
  let originalPriorPiece := μprior.restrict chartPiece
  haveI :
      SFinite
        (originalEdgeFamilyVolume (V := reverseVertex W₂)
          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)) := by
    dsimp [originalEdgeFamilyVolume, originalTupleVolume, originalCoordinateVolume]
    infer_instance
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, μprior, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume
      (by simpa [cHaar, Ddet, Dvol] using hvolume_readback_dom)
      hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) (by simpa [Ddet] using hDdet)
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  have hmapV :
      Measure.map readback (μprior.restrict chartPiece) ≤
        Cprior • coordinateSourceMeasure.restrict V := by
    simpa [μprior, Cprior] using
      measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
        (Θ := Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
        (E := EdgeFamily)
        (source := chartPiece) (V := V) (G := G)
        (sourceChart := sourceChart) (readback := readback)
        (μ := μprior) (θμ := coordinateSourceMeasure) (c := Cprior)
        hchartPiece hVopen.measurableSet hchartPiece_sub_image hleft_local hVG
        (by simpa [originalPriorPiece, μprior] using hprior_readback.1)
        (by simpa [originalPriorPiece, μprior, Cprior] using hprior_readback.2)
  refine ⟨Cdet, hCdet, ?_⟩
  exact ⟨hCprior,
    by simpa [originalPriorPiece, μprior] using hprior_readback.1,
    by simpa [μprior, Cprior] using hmapV⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper composes the endpoint-reference volume theorem with prior domination on the returned shrink.
/-- Same-shrink original-prior readback domination targeting the returned
coordinate-source restriction.

The hypotheses are the endpoint-reference weighted-Haar identity, endpoint
lower bound, source-density lower bound, and prior-density upper bound.  The
final domination target is
`coordinateSourceMeasure.restrict V`, using support of the readback map on the
returned chart.  It still does not prove determinant-chart Haar transport,
raw-order Haar transport, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, finite-integral
transfer, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      endpointReferenceImage =
                          (rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict
                              (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                      density E ≤ Kprior) →
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict V := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity, rawSourceSet,
          p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P endpointReferenceImage hendpoint hCdet
    hendpoint_lower hsource_lower hε_ne_zero hε_ne_top density Kprior
    hdensity cHaar Ddet Dvol Cprior
  rcases
      (by
        simpa [RawTuple, EdgeFamily, endpointReferenceImage,
          endpointJacobianDensity, d, originalVolume, cHaar, Ddet, Dvol, P] using
          hvolume_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
            hchartPiece hchartPiece_sub_image hendpoint hCdet
            hendpoint_lower hsource_lower hε_ne_zero hε_ne_top) with
    ⟨hDdet, hreadback_volume, hvolume_readback_dom⟩
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume hvolume_readback_dom hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  have hmapV :
      Measure.map readback
          ((originalEdgeFamilyPrior
            (V := reverseVertex W₂)
            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
            density).restrict chartPiece) ≤
        Cprior • coordinateSourceMeasure.restrict V := by
    exact
      measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
        (source := chartPiece) (V := V) (G := G)
        (sourceChart := sourceChart) (readback := readback)
        (μ := originalEdgeFamilyPrior
          (V := reverseVertex W₂)
          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
          density)
        (θμ := coordinateSourceMeasure) (c := Cprior)
        hchartPiece hVopen.measurableSet hchartPiece_sub_image
        hleft_local hVG
        (by simpa [originalPriorPiece] using hprior_readback.1)
        (by simpa [originalPriorPiece, Cprior] using hprior_readback.2)
  exact ⟨hCprior,
    by simpa [originalPriorPiece] using hprior_readback.1,
    hmapV⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper adds the bounded original-prior density handoff to source-cylinder support.
/-- Same-shrink with-following original-prior readback domination from
source-cylinder chart-piece support, a lower source-density bound, and a local
upper bound for the original prior density.

This is the prior analogue of
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower`.
The source-cylinder original-volume wrapper supplies the original-volume
readback domination with scalar `Dvol = cHaar⁻¹ * (Cdet * ε⁻¹)`.  The
prior-density upper bound gives `originalPrior.restrict chartPiece ≤ ofReal
Kprior • originalVolume.restrict chartPiece`, and the generic readback
domination handoff multiplies the final scalar by `ofReal Kprior`.

The source-cylinder support, source-density lower bound, prior-density upper
bound, and `ε ≠ 0, ∞` remain explicit hypotheses.  This theorem does not prove
source-cylinder support, C-one support, source-density positivity,
determinant-chart Haar transport, exact raw-Haar pushforward, Haar
normalization, source coverage, source-rank coverage, original source-prior
transport beyond the bounded-density comparison, finite-integral transfer,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
                      (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                density E ≤ Kprior) →
                                ∃ Cdet : ℝ≥0∞,
                                  Cdet < ∞ ∧
                                    let cHaar :=
                                      (originalTupleVolumeHaarScalarOfMap d
                                        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                          W₂ B₂ U₀) rawHaar)
                                    let Ddet := Cdet * ε⁻¹
                                    let Dvol :=
                                      (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                    let Cprior := ENNReal.ofReal Kprior * Dvol
                                    Cprior < ∞ ∧
                                      AEMeasurable readback
                                        ((originalEdgeFamilyPrior
                                          (V := reverseVertex W₂)
                                          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                          density).restrict chartPiece) ∧
                                        Measure.map readback
                                            ((originalEdgeFamilyPrior
                                              (V := reverseVertex W₂)
                                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                              density).restrict chartPiece) ≤
                                          Cprior • coordinateSourceMeasure.restrict G := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet,
          rawChart, d, originalVolume, pivotNext, signedBox, sourceCylinder,
          activeChart, activeWriteback] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_cylinder
    hsource_lower hε_ne_zero hε_ne_top density Kprior hdensity
  rcases
      hvolume_package rawHaar chartPiece (ε := ε) hchartPiece
        hchartPiece_sub_cylinder hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDdet, hreadback_volume, hvolume_readback_dom⟩
  let cHaar :=
    (originalTupleVolumeHaarScalarOfMap d
      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
        W₂ B₂ U₀) rawHaar)
  let Ddet := Cdet * ε⁻¹
  let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
  let Cprior := ENNReal.ofReal Kprior * Dvol
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  haveI :
      SFinite
        (originalEdgeFamilyVolume (V := reverseVertex W₂)
          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)) := by
    dsimp [originalEdgeFamilyVolume, originalTupleVolume, originalCoordinateVolume]
    infer_instance
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume
      (by simpa [Θ, cHaar, Ddet, Dvol] using hvolume_readback_dom)
      hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) (by simpa [Ddet] using hDdet)
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  refine ⟨Cdet, hCdet, ?_⟩
  exact ⟨hCprior,
    by simpa [originalPriorPiece] using hprior_readback.1,
    by simpa [Θ, originalPriorPiece, Cprior] using hprior_readback.2⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper obtains source-cylinder support from C-one signed-box support.
/-- Same-shrink with-following original-prior readback domination from C-one
readout support, a lower source-density bound, and a local upper bound for the
original prior density.

The caller supplies ordinary local chart-piece support
`chartPiece ⊆ sourceChart '' V`, the pointwise signed-box condition
`cOneReadout E ∈ signedBox` on the chart piece, and the prior-density upper
bound.  The support bridge converts this to source-cylinder support, and the
source-cylinder original-prior wrapper supplies the readback domination with
final scalar `ofReal Kprior * (cHaar⁻¹ * (Cdet * ε⁻¹))`.

This theorem does not prove the C-one signed-box condition for arbitrary chart
pieces.  It also does not prove source-density positivity, determinant-chart
Haar transport, exact raw-Haar pushforward, Haar normalization, source
coverage, source-rank coverage, original source-prior transport beyond the
bounded-density comparison, finite-integral transfer, normal crossings, pole
order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V,
                E ∈
                  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
                    (K := ℝ) W₂ B₂ U₀ hU₀) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                  density E ≤ Kprior) →
                                  ∃ Cdet : ℝ≥0∞,
                                    Cdet < ∞ ∧
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict G := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback cOneReadout sourceDensity coordinateSourceMeasure d
    originalVolume signedBox sourceCylinder
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          d, originalVolume, signedBox, sourceCylinder] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V,
      hsource_cylinder_package⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_V z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13V :
      ∀ E ∈ sourceChart '' V,
        E ∈
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
            (K := ℝ) W₂ B₂ U₀ hU₀ := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_V (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hV_open, hz₀V, hVG, hleftV, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13V, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_image
    hcOne_support hsource_lower hε_ne_zero hε_ne_top density Kprior hdensity
  have hchartPiece_sub_cylinder :
      chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) := by
    simpa [Θ, EdgeFamily, sourceChart, readback, cOneReadout, signedBox,
      sourceCylinder] using
      chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
        W₂ B₂ n hS hcont hnext hU₀ eNext e Rres
        hleftV hchartPiece_sub_image hcOne_support
  exact
    hsource_cylinder_package rawHaar chartPiece (ε := ε)
      hchartPiece hchartPiece_sub_cylinder hsource_lower hε_ne_zero hε_ne_top
      hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper adds the bounded original-prior density handoff to active containment.
/-- Same-shrink with-following original-prior readback domination from active
endpoint-image containment, a lower source-density bound, and a local upper
bound for the original prior density.

This is the prior analogue of
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower`.
The active containment supplies the original-volume readback domination with
scalar `Dvol = cHaar⁻¹ * (Cdet * ε⁻¹)`.  The prior-density upper bound gives
`originalPrior.restrict chartPiece ≤ ofReal Kprior • originalVolume.restrict
chartPiece`, and the generic readback domination handoff multiplies the final
scalar by `ofReal Kprior`.

The active containment, source-density lower bound, prior-density upper bound,
and `ε ≠ 0, ∞` remain explicit hypotheses.  This theorem does not prove
active containment from chart-piece support, C-one support, source-density
positivity, determinant-chart Haar transport, exact raw-Haar pushforward, Haar
normalization, source coverage, source-rank coverage, original source-prior
transport beyond the bounded-density comparison, normal crossings, pole order,
finite-integral transfer, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      {z | z.1.yNext ∈ signedBox}
    let activeChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ≃L[ℝ]
          RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointPatch : Set RawTuple :=
                        rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                      let activePatchImage := activeChart '' (V ∩ sourceCylinder)
                      endpointPatch ⊆ activeWriteback '' activePatchImage →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                  density E ≤ Kprior) →
                                  ∃ Cdet : ℝ≥0∞,
                                    Cdet < ∞ ∧
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict G := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume
    pivotNext signedBox sourceCylinder activeChart activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume, pivotNext, signedBox, sourceCylinder, activeChart,
          activeWriteback] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece ε hchartPiece hchartPiece_sub_image
    P endpointPatch activePatchImage hpatch hsource_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  rcases
      hvolume_package rawHaar chartPiece (ε := ε) hchartPiece
        hchartPiece_sub_image hpatch hsource_lower hε_ne_zero hε_ne_top with
    ⟨Cdet, hCdet, hDdet, hreadback_volume, hvolume_readback_dom⟩
  let cHaar :=
    (originalTupleVolumeHaarScalarOfMap d
      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
        W₂ B₂ U₀) rawHaar)
  let Ddet := Cdet * ε⁻¹
  let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
  let Cprior := ENNReal.ofReal Kprior * Dvol
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  haveI :
      SFinite
        (originalEdgeFamilyVolume (V := reverseVertex W₂)
          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)) := by
    dsimp [originalEdgeFamilyVolume, originalTupleVolume, originalCoordinateVolume]
    infer_instance
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume
      (by simpa [cHaar, Ddet, Dvol] using hvolume_readback_dom)
      hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) (by simpa [Ddet] using hDdet)
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  refine ⟨Cdet, hCdet, ?_⟩
  exact ⟨hCprior,
    by simpa [originalPriorPiece] using hprior_readback.1,
    by simpa [originalPriorPiece, Cprior] using hprior_readback.2⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper transfers any finite with-following source integral through the prior readback package.
/-- With-following original-prior chart-piece finite-integral transfer from
endpoint-density readback domination.

The source-side finite integral is an explicit hypothesis.  This theorem only
uses the endpoint-density prior readback wrapper and the generic measurable
readback transfer lemma, so it proves no source-side residual integrability,
source-image coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_prod_originalEdgeFamilyPrior_restrict_chartPiece_of_case2PassiveThetaWithFollowingFactor_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      endpointReferenceImage =
                          (rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict
                              (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                      density E ≤ Kprior) →
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        ∀ {β : Type*} [MeasurableSpace β]
                                          {ν : Measure β} [SFinite ν]
                                          {F : EdgeFamily × β → ℝ≥0∞},
                                          Measurable
                                            (fun z :
                                                Case2PassiveThetaWithFollowingFactor
                                                    (ρ := Fin (Module.finrank ℝ U₀))
                                                    (τ := τ) n S J × β ↦
                                              F (sourceChart z.1, z.2)) →
                                            (∫⁻ z :
                                                Case2PassiveThetaWithFollowingFactor
                                                    (ρ := Fin (Module.finrank ℝ U₀))
                                                    (τ := τ) n S J × β,
                                              F (sourceChart z.1, z.2) ∂
                                                (coordinateSourceMeasure.restrict G).prod ν) < ∞ →
                                              (∫⁻ z : EdgeFamily × β, F z ∂
                                                ((originalEdgeFamilyPrior
                                                  (V := reverseVertex W₂)
                                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                  density).restrict chartPiece).prod ν) < ∞ := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity, rawSourceSet,
          p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P endpointReferenceImage hendpoint hCdet
    hendpoint_lower hsource_lower hε_ne_zero hε_ne_top density Kprior
    hdensity cHaar Ddet Dvol Cprior
  rcases
      (by
        simpa [RawTuple, EdgeFamily, endpointReferenceImage,
          endpointJacobianDensity, d, originalVolume, cHaar, Ddet, Dvol, P] using
          hvolume_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
            hchartPiece hchartPiece_sub_image hendpoint hCdet
            hendpoint_lower hsource_lower hε_ne_zero hε_ne_top) with
    ⟨hDdet, hreadback_volume, hvolume_readback_dom⟩
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume hvolume_readback_dom hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  refine ⟨hCprior, ?_⟩
  intro β _instβ ν _instν F hFsource hfinite
  haveI : SFinite originalPriorPiece := by
    dsimp [originalPriorPiece, originalEdgeFamilyPrior, originalEdgeFamilyVolume,
      originalTupleVolume, originalCoordinateVolume]
    infer_instance
  have hright_pointwise :
      ∀ E ∈ chartPiece, sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    rw [hleft_local z hzV]
  have hright :
      ∀ᵐ E ∂ originalPriorPiece, sourceChart (readback E) = E := by
    filter_upwards [ae_restrict_mem hchartPiece] with E hE
    exact hright_pointwise E hE
  simpa [originalPriorPiece] using
    lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul
      (μ := originalPriorPiece) (θμ := coordinateSourceMeasure.restrict G)
      (η := ν) (readback := readback) (sourceChart := sourceChart)
      (C := Cprior) (F := F)
      (by simpa [originalPriorPiece] using hprior_readback.1)
      hright
      (by simpa [originalPriorPiece, Cprior] using hprior_readback.2)
      hCprior hFsource hfinite

universe uβ

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Specialize a product finite-integral transfer continuation to the
with-following readback product residual.

This is only the final measure-bookkeeping step after a prior-readback theorem
has produced a transfer continuation for arbitrary product integrands.  The
source-side measurability and finite integral remain explicit hypotheses. -/
theorem lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_lt_top_of_forall_prod_transfer
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {Θ : Type*} [MeasurableSpace Θ]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {sourceChart :
      Θ →
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ}
    {θμ : Measure Θ}
    {μ :
      Measure
        (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)}
    [SFinite θμ] [SFinite μ] {t : ℝ}
    (htransfer :
      ∀ {β : Type uβ} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
        {F :
          (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) × β →
            ℝ≥0∞},
        Measurable (fun z : Θ × β ↦ F (sourceChart z.1, z.2)) →
          (∫⁻ z : Θ × β, F (sourceChart z.1, z.2) ∂ θμ.prod ν) < ∞ →
            (∫⁻ z :
                (∀ p : Fin 2,
                    reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) × β,
              F z ∂ μ.prod ν) < ∞)
    (hmeas :
      Measurable
        (fun z : Θ ↦
          ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
                W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z))) ^ (-t))))
    (hfinite :
      (∫⁻ z : Θ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z))) ^ (-t)) ∂ θμ) < ∞) :
    (∫⁻ E :
        (∀ p : Fin 2,
          reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ),
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t)) ∂ μ) < ∞ := by
  let residualIntegrand :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞ :=
    fun E ↦
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
  exact
    lintegral_lt_top_of_forall_prod_transfer_unit
      (θμ := θμ) (μ := μ) (sourceChart := sourceChart)
      (f := residualIntegrand) htransfer
      (by simpa [residualIntegrand] using hmeas)
      (by simpa [residualIntegrand] using hfinite)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Specialize the product-transfer continuation to the readback product
residual using a source-chart left inverse and a finite source product-residual
integral.

This is still only a conditional handoff: the transfer continuation and the
source-side measurability remain explicit hypotheses. -/
theorem lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_lt_top_of_forall_prod_transfer_of_leftInverse
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)}
    {θμ :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)}
    {μ :
      Measure
        (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)}
    [SFinite (θμ.restrict V)] [SFinite μ] {t : ℝ}
    (hV : MeasurableSet V)
    (hleft :
      ∀ z ∈ V,
        case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z)
    (htransfer :
      ∀ {β : Type uβ} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
        {F :
          (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) × β →
            ℝ≥0∞},
        Measurable
          (fun z :
              Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J × β ↦
            F
              (case2PassiveThetaWithFollowingFactorEndpointSourceChart
                W₂ B₂ n hS hcont hnext hU₀ eNext e z.1, z.2)) →
          (∫⁻ z :
              Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J × β,
            F
              (case2PassiveThetaWithFollowingFactorEndpointSourceChart
                W₂ B₂ n hS hcont hnext hU₀ eNext e z.1, z.2) ∂
              (θμ.restrict V).prod ν) < ∞ →
            (∫⁻ z :
                (∀ p : Fin 2,
                    reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) × β,
              F z ∂ μ.prod ν) < ∞)
    (hmeas :
      Measurable
        (fun z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
                W₂ B₂ n hS hcont hnext hU₀ eNext e
                (case2PassiveThetaWithFollowingFactorEndpointSourceChart
                  W₂ B₂ n hS hcont hnext hU₀ eNext e z))) ^ (-t))))
    (hfinite_source :
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorProductResidualReadout
              (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)) ^ (-t)) ∂
          θμ.restrict V) < ∞) :
    (∫⁻ E :
        (∀ p : Fin 2,
          reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ),
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t)) ∂ μ) < ∞ := by
  let Θ :=
    Case2PassiveThetaWithFollowingFactor
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let sourceChart : Θ → EdgeFamily :=
    case2PassiveThetaWithFollowingFactorEndpointSourceChart
      W₂ B₂ n hS hcont hnext hU₀ eNext e
  have hfinite_readback :
      (∫⁻ z : Θ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z))) ^ (-t)) ∂
          θμ.restrict V) < ∞ := by
    have hcongr :
        (fun z : Θ ↦
          ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
                W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z))) ^ (-t))) =ᵐ[θμ.restrict V]
          fun z : Θ ↦
            ENNReal.ofReal
              ((aoyagiCoordinateSquareSum
                (case2PassiveThetaWithFollowingFactorProductResidualReadout
                  (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)) ^ (-t)) := by
      filter_upwards [ae_restrict_mem hV] with z hz
      rw [
        aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
          W₂ B₂ n hS hcont hnext hU₀ eNext e z (hleft z hz)]
    have heq :=
      lintegral_congr_ae hcongr
    rw [heq]
    simpa [Θ] using hfinite_source
  exact
    lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_lt_top_of_forall_prod_transfer
      W₂ B₂ n hS hcont hnext hU₀ eNext e
      (sourceChart := sourceChart) (θμ := θμ.restrict V) (μ := μ)
      htransfer (by simpa [Θ, EdgeFamily, sourceChart] using hmeas)
      (by simpa [Θ, EdgeFamily, sourceChart] using hfinite_readback)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The wrapper composes two large localized measure-transfer packages whose
-- dependent lets and measure instances are expensive for elaboration.
/-- With-following readback product-residual finite integrability for original
edge-family priors, assuming the localized endpoint-density and prior-density
inputs.

The source-side product-residual finite integral is supplied internally by the
unit source-image-density coordinate-source theorem.  The endpoint image
identity, determinant-density lower bound, prior-density upper bound, and
measurability of the readback residual integrand remain explicit hypotheses.
This theorem proves no endpoint Haar transport, source-image coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointReferenceImage_eq_withDensity_formalProductAbsDet_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun _ ↦ (1 : ℝ≥0∞)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    Measurable (fun z : Θ ↦ residualIntegrand (sourceChart z)) →
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      endpointReferenceImage =
                          (rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict
                              (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                density E ≤ Kprior) →
                                (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                                  (originalEdgeFamilyPrior
                                    (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart endpointJacobianDensity rawSourceSet p13SourceSet rawChart d
    originalVolume residualIntegrand hmeas
  rcases
      exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceImageDensity_one
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        (hDomainOpens := inferInstance)
        (hDomainBorel := inferInstance)
        (hDomainPolish := inferInstance)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        G hGopen hz₀G with
    ⟨passiveLocalSet, passiveMeasure, followingPatch, K, Vsource,
      hz₀passive, hpassive_open, hpassive_meas, hpassive_eq,
      hpassive_lt_top, hpassive_le, hK_pos, hz₀_following,
      hfollowing_open, hfollowing_meas, hfollowing_lt_top,
      hfollowing_det, hfollowing_inv_bound,
      hVsource_open, hz₀Vsource, hVsourceG, hVsource_passive,
      hVsource_following, hdetVsource, hleft_source, hsource_inj,
      hsource_contOn, hsource_image_meas, hprod⟩
  have hfinite_source :
      (∫⁻ z : Θ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorProductResidualReadout
              (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)) ^ (-t)) ∂
          coordinateSourceMeasure.restrict Vsource) < ∞ := by
    simpa [Θ, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure,
      case2PassiveThetaWithFollowingFactorProductResidualReadout] using hprod.2
  rcases
      exists_open_lintegral_prod_originalEdgeFamilyPrior_restrict_chartPiece_of_case2PassiveThetaWithFollowingFactor_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀
        (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞)) Rres Vsource
        hVsource_open hz₀Vsource with
    ⟨V, hV_open, hz₀V, hVVsource, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hprior_package⟩
  refine ⟨V, hV_open, hz₀V, ?_, hleft_V, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13_V, ?_⟩
  · exact Set.Subset.trans hVVsource hVsourceG
  · intro rawHaar _instRawHaar chartPiece Cdet hchartPiece hchartPiece_sub_image
      P endpointReferenceImage hendpoint hCdet hendpoint_lower density Kprior hdensity
    have hsource_lower_unit :
        ∀ᵐ z ∂baseJ.restrict V, (1 : ℝ≥0∞) ≤ sourceDensity z := by
      filter_upwards [] with z
      simp [sourceDensity]
    rcases
        hprior_package rawHaar chartPiece (Cdet := Cdet) (ε := (1 : ℝ≥0∞))
          hchartPiece hchartPiece_sub_image hendpoint hCdet hendpoint_lower
          hsource_lower_unit (by simp) (by simp) hdensity with
      ⟨hCprior, htransfer⟩
    let priorPiece :=
      (originalEdgeFamilyPrior (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
    haveI hreferenceSource_sfinite : SFinite referenceSource := by
      dsimp [referenceSource,
        case2PassiveThetaWithFollowingFactorReferenceSourceMeasure]
      haveI :
          SFinite
            (case2PassiveThetaReferenceSourceMeasure
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres) :=
        sFinite_case2PassiveThetaReferenceSourceMeasure
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
      haveI :
          SFinite
            (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) :=
        sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
      infer_instance
    haveI : SFinite (coordinateSourceMeasure.restrict Vsource) := by
      dsimp [coordinateSourceMeasure, baseJ]
      infer_instance
    haveI : SFinite priorPiece := by
      dsimp [priorPiece, originalEdgeFamilyPrior, originalEdgeFamilyVolume,
        originalTupleVolume, originalCoordinateVolume]
      infer_instance
    have hfinite_readback :
        (∫⁻ z : Θ, residualIntegrand (sourceChart z) ∂
          coordinateSourceMeasure.restrict Vsource) < ∞ := by
      have hcongr :
          (fun z : Θ ↦ residualIntegrand (sourceChart z)) =ᵐ[
              coordinateSourceMeasure.restrict Vsource]
            fun z : Θ ↦
              ENNReal.ofReal
                ((aoyagiCoordinateSquareSum
                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                    (ρ := Fin (Module.finrank ℝ U₀))
                    n hS hcont hnext z eNext e)) ^ (-t)) := by
        filter_upwards [ae_restrict_mem hVsource_open.measurableSet] with z hz
        have hsquare :=
          aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
            W₂ B₂ n hS hcont hnext hU₀ eNext e z (hleft_source z hz)
        simpa [residualIntegrand, sourceChart] using
          congrArg (fun x : ℝ => ENNReal.ofReal (x ^ (-t))) hsquare
      have heq := lintegral_congr_ae hcongr
      rw [heq]
      simpa [Θ, EdgeFamily] using hfinite_source
    let F : EdgeFamily × PUnit.{1} → ℝ≥0∞ := fun z ↦ residualIntegrand z.1
    have hF_source :
        Measurable (fun z : Θ × PUnit.{1} ↦ F (sourceChart z.1, z.2)) := by
      simpa [F] using hmeas.comp measurable_fst
    have hfinite_source_prod :
        (∫⁻ z : Θ × PUnit.{1}, F (sourceChart z.1, z.2) ∂
          (coordinateSourceMeasure.restrict Vsource).prod
            (Measure.dirac (PUnit.unit : PUnit.{1}))) < ∞ := by
      rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{1})]
      simpa [F] using hfinite_readback
    have htarget_prod :
        (∫⁻ z : EdgeFamily × PUnit.{1}, F z ∂
          priorPiece.prod (Measure.dirac (PUnit.unit : PUnit.{1}))) < ∞ :=
      htransfer (β := PUnit.{1}) (ν := Measure.dirac (PUnit.unit : PUnit.{1}))
        (F := F) hF_source hfinite_source_prod
    have htarget :
        (∫⁻ E : EdgeFamily, residualIntegrand E ∂ priorPiece) < ∞ := by
      rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{1})] at htarget_prod
      simpa [F] using htarget_prod
    simpa [priorPiece, residualIntegrand] using htarget


set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant keeps only the direct endpoint-patch domination socket.
/-- With-following readback product-residual finite integrability for original
edge-family priors from direct endpoint-patch domination.

The source-side product-residual finite integral is supplied internally by the
unit source-image-density coordinate-source theorem.  The endpoint input is the
weaker direct domination
`rawHaar.restrict endpointPatch <= Cdet • endpointReferenceImage`, rather than
an endpoint weighted-Haar identity plus determinant-density lower bound.  The
prior-density upper bound remains explicit; source-side a.e.-measurability of
the readback residual integrand is discharged from the local left-inverse and
finite-coordinate product-residual measurability. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointPatch_restrict_le_smul_endpointReferenceImage_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun _ ↦ (1 : ℝ≥0∞)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      rawHaar.restrict
                          (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                        Cdet • endpointReferenceImage →
                        Cdet < ∞ →
                          ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                            (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                              density E ≤ Kprior) →
                              (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                                (originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart originalVolume
    residualIntegrand
  rcases
      exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceImageDensity_one
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        (hDomainOpens := inferInstance)
        (hDomainBorel := inferInstance)
        (hDomainPolish := inferInstance)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        G hGopen hz₀G with
    ⟨passiveLocalSet, passiveMeasure, followingPatch, K, Vsource,
      hz₀passive, hpassive_open, hpassive_meas, hpassive_eq,
      hpassive_lt_top, hpassive_le, hK_pos, hz₀_following,
      hfollowing_open, hfollowing_meas, hfollowing_lt_top,
      hfollowing_det, hfollowing_inv_bound,
      hVsource_open, hz₀Vsource, hVsourceG, hVsource_passive,
      hVsource_following, hdetVsource, hleft_source, hsource_inj,
      hsource_contOn, hsource_image_meas, hprod⟩
  have hfinite_source :
      (∫⁻ z : Θ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorProductResidualReadout
              (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)) ^ (-t)) ∂
          coordinateSourceMeasure.restrict Vsource) < ∞ := by
    simpa [Θ, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure,
      case2PassiveThetaWithFollowingFactorProductResidualReadout] using hprod.2
  rcases
      exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀
        (fun _ : EdgeFamily ↦ (1 : ℝ≥0∞)) Rres Vsource
        hVsource_open hz₀Vsource with
    ⟨V, hV_open, hz₀V, hVVsource, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hprior_package⟩
  refine ⟨V, hV_open, hz₀V, ?_, hleft_V, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13_V, ?_⟩
  · exact Set.Subset.trans hVVsource hVsourceG
  · intro rawHaar _instRawHaar chartPiece Cdet hchartPiece hchartPiece_sub_image
      P endpointReferenceImage hdet_dom hCdet density Kprior hdensity
    have hp13 :
        P ⊆ rawSourceSet ∧
          NullMeasurableSet
            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar := by
      simpa [P, RawTuple, EdgeFamily, rawOrderOnEndpoint, rawDetChart,
        rawSourceSet, rawChart] using
        nullMeasurableSet_topologyTupleDetChart_inter_rawOrder_preimage_p13RawOrderSourceChart_chartPiece
          (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
          rawHaar hchartPiece
    have hsource_lower_unit :
        ∀ᵐ z ∂baseJ.restrict V, (1 : ℝ≥0∞) ≤ sourceDensity z := by
      filter_upwards [] with z
      simp [sourceDensity]
    have hdet_dom' :
        rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
          Cdet • Measure.map Y (referenceSource.restrict V) := by
      simpa [P, RawTuple, endpointReferenceImage, Y, referenceSource,
        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure] using
        hdet_dom
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let cHaar :=
      (originalTupleVolumeHaarScalarOfMap d
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W₂ B₂ U₀) rawHaar)
    let Ddet := Cdet * (1 : ℝ≥0∞)⁻¹
    let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
    let Cprior := ENNReal.ofReal Kprior * Dvol
    rcases
        hprior_package rawHaar chartPiece (Cdet := Cdet) (ε := (1 : ℝ≥0∞))
          hchartPiece hchartPiece_sub_image
          (by simpa [P] using hp13.2)
          hdet_dom'
          hCdet hsource_lower_unit (by simp) (by simp) hdensity with
      ⟨hCprior, hreadback_meas, hreadback_dom⟩
    have hCprior' : Cprior < ∞ := by
      simpa [Cprior, Dvol, Ddet, cHaar, d] using hCprior
    let priorPiece :=
      (originalEdgeFamilyPrior (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
    haveI hreferenceSource_sfinite : SFinite referenceSource := by
      dsimp [referenceSource,
        case2PassiveThetaWithFollowingFactorReferenceSourceMeasure]
      haveI :
          SFinite
            (case2PassiveThetaReferenceSourceMeasure
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres) :=
        sFinite_case2PassiveThetaReferenceSourceMeasure
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
      haveI :
          SFinite
            (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) :=
        sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
      infer_instance
    haveI : SFinite (coordinateSourceMeasure.restrict Vsource) := by
      dsimp [coordinateSourceMeasure, baseJ]
      infer_instance
    haveI : SFinite priorPiece := by
      dsimp [priorPiece, originalEdgeFamilyPrior, originalEdgeFamilyVolume,
        originalTupleVolume, originalCoordinateVolume]
      infer_instance
    have hfinite_readback :
        (∫⁻ z : Θ, residualIntegrand (sourceChart z) ∂
          coordinateSourceMeasure.restrict Vsource) < ∞ := by
      have hcongr :
          (fun z : Θ ↦ residualIntegrand (sourceChart z)) =ᵐ[
              coordinateSourceMeasure.restrict Vsource]
            fun z : Θ ↦
              ENNReal.ofReal
                ((aoyagiCoordinateSquareSum
                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                    (ρ := Fin (Module.finrank ℝ U₀))
                    n hS hcont hnext z eNext e)) ^ (-t)) := by
        filter_upwards [ae_restrict_mem hVsource_open.measurableSet] with z hz
        have hsquare :=
          aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
            W₂ B₂ n hS hcont hnext hU₀ eNext e z (hleft_source z hz)
        simpa [residualIntegrand, sourceChart] using
          congrArg (fun x : ℝ => ENNReal.ofReal (x ^ (-t))) hsquare
      have heq := lintegral_congr_ae hcongr
      rw [heq]
      simpa [Θ, EdgeFamily] using hfinite_source
    let F : EdgeFamily × PUnit.{1} → ℝ≥0∞ := fun z ↦ residualIntegrand z.1
    have hF_source :
        AEMeasurable (fun z : Θ × PUnit.{1} ↦ F (sourceChart z.1, z.2))
          ((baseJ.restrict Vsource).prod
            (Measure.dirac (PUnit.unit : PUnit.{1}))) := by
      have hsource_product_meas :
          Measurable
            (fun z : Θ ↦
              ENNReal.ofReal
                ((aoyagiCoordinateSquareSum
                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                    (ρ := Fin (Module.finrank ℝ U₀))
                    n hS hcont hnext z eNext e)) ^ (-t))) := by
        simpa [Θ] using
          measurable_case2PassiveThetaWithFollowingFactorProductResidualIntegrand
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            n hS hcont hnext eNext e (t := t)
      have hsource_readback_ae :
          AEMeasurable (fun z : Θ ↦ residualIntegrand (sourceChart z))
            (baseJ.restrict Vsource) := by
        have hcongr :
            (fun z : Θ ↦
              ENNReal.ofReal
                ((aoyagiCoordinateSquareSum
                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                    (ρ := Fin (Module.finrank ℝ U₀))
                    n hS hcont hnext z eNext e)) ^ (-t))) =ᵐ[
                baseJ.restrict Vsource]
              fun z : Θ ↦ residualIntegrand (sourceChart z) := by
          filter_upwards [ae_restrict_mem hVsource_open.measurableSet] with z hz
          have hsquare :=
            aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
              W₂ B₂ n hS hcont hnext hU₀ eNext e z (hleft_source z hz)
          simpa [residualIntegrand, sourceChart] using
            congrArg (fun x : ℝ => ENNReal.ofReal (x ^ (-t))) hsquare.symm
        exact hsource_product_meas.aemeasurable.congr hcongr
      have hfst :
          AEMeasurable (fun z : Θ × PUnit.{1} ↦ residualIntegrand (sourceChart z.1))
            ((baseJ.restrict Vsource).prod
              (Measure.dirac (PUnit.unit : PUnit.{1}))) :=
        hsource_readback_ae.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst
            (μ := baseJ.restrict Vsource)
            (ν := Measure.dirac (PUnit.unit : PUnit.{1})))
      simpa [F] using hfst
    have hfinite_source_prod :
        (∫⁻ z : Θ × PUnit.{1}, F (sourceChart z.1, z.2) ∂
          (baseJ.restrict Vsource).prod
            (Measure.dirac (PUnit.unit : PUnit.{1}))) < ∞ := by
      rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{1})]
      simpa [F, coordinateSourceMeasure, sourceDensity] using hfinite_readback
    have hright_pointwise :
        ∀ E ∈ chartPiece, sourceChart (readback E) = E := by
      intro E hE
      rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
      simpa [sourceChart, readback] using congrArg sourceChart (hleft_V z hzV)
    have hright :
        ∀ᵐ E ∂priorPiece, sourceChart (readback E) = E := by
      filter_upwards [ae_restrict_mem hchartPiece] with E hE
      exact hright_pointwise E hE
    have htarget_prod :
        (∫⁻ z : EdgeFamily × PUnit.{1}, F z ∂
          priorPiece.prod (Measure.dirac (PUnit.unit : PUnit.{1}))) < ∞ :=
      lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul_of_aemeasurable_source
        (Θ := Θ) (E := EdgeFamily) (β := PUnit.{1})
        (μ := priorPiece) (θμ := baseJ.restrict Vsource)
        (η := Measure.dirac (PUnit.unit : PUnit.{1})) (readback := readback)
        (sourceChart := sourceChart) (C := Cprior) (F := F)
        (by simpa [priorPiece] using hreadback_meas)
        hright
        (by
          simpa [Θ, EdgeFamily, priorPiece, baseJ, Cprior, Dvol, Ddet, cHaar, d]
            using hreadback_dom)
        hCprior' hF_source hfinite_source_prod
    have htarget :
        (∫⁻ E : EdgeFamily, residualIntegrand E ∂ priorPiece) < ∞ := by
      rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{1})] at htarget_prod
      simpa [F] using htarget_prod
    simpa [priorPiece, residualIntegrand] using htarget

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant obtains the direct endpoint scalar from active endpoint Haar domination.
/-- With-following readback product-residual finite integrability for original
edge-family priors from active endpoint scalar domination.

The local set is first shrunk inside the selected-pivot nonzero locus, so the
active endpoint theorem can be applied with `Omega := V`.  The only endpoint
geometry still assumed is the containment of the p.13 endpoint patch in the
active writeback image of the selected-entry active patch.  Prior-density
upper bounds remain explicit. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun _ ↦ (1 : ℝ≥0∞)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointPatch : Set RawTuple :=
                        rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                      let activePatchImage := activeChart '' (V ∩ sourceCylinder)
                      endpointPatch ⊆ activeWriteback '' activePatchImage →
                        ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                          (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                            density E ≤ Kprior) →
                            (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                              (originalEdgeFamilyPrior
                                (V := reverseVertex W₂)
                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart originalVolume
    residualIntegrand pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  let pivotSet : Set Θ :=
    {z | case2PassiveThetaPivotNonzero
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous (fun z : Θ ↦ z.1.yNext pivotNext) := by
      simpa [Θ, pivotNext, Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd.comp
            (continuous_fst : Continuous (fun z : Θ ↦ z.1))))
    simpa [pivotSet, pivotNext, case2PassiveThetaPivotNonzero] using
      (isOpen_ne.preimage hpivot_cont)
  let Gpivot : Set Θ := G ∩ pivotSet
  have hGpivot_open : IsOpen Gpivot := hGopen.inter hpivotSet_open
  have hz₀Gpivot : z₀ ∈ Gpivot := by
    exact ⟨hz₀G, by simpa [pivotSet] using hpivot₀⟩
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointPatch_restrict_le_smul_endpointReferenceImage_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        Gpivot hGpivot_open hz₀Gpivot with
    ⟨V, hV_open, hz₀V, hVGpivot, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  have hVG : V ⊆ G := by
    intro z hz
    exact (hVGpivot hz).1
  have hVpivot : V ⊆ pivotSet := by
    intro z hz
    exact (hVGpivot hz).2
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_image
    P endpointPatch activePatchImage hpatch density Kprior hdensity
  have hVpivot' :
      V ⊆ {z |
        case2PassiveThetaPivotNonzero
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1} := by
    intro z hz
    simpa [pivotSet] using hVpivot hz
  have hactive :
      ∃ Cdet : ℝ≥0∞,
        Cdet < ∞ ∧
          rawHaar.restrict endpointPatch ≤
            Cdet •
              case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                n hS hcont hnext eNext e Rres V := by
    simpa [Θ, RawTuple, pivotNext, signedBox, sourceCylinder, activeChart,
      activePatchImage, activeWriteback, endpointPatch] using
      (_root_.DLNFibre.DLN.Aoyagi.rawHaar_restrict_endpointPatch_le_smul_case2PassiveThetaWithFollowingFactorEndpointReferenceImage_of_subset_activeWriteback_activeSelectedEntryImage_inter_signedBox_of_subset_pivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext eNext e Rres V hV_open.measurableSet
        hVpivot' rawHaar endpointPatch hpatch)
  rcases hactive with ⟨Cdet, hCdet, hdom⟩
  exact
    hfinite_package rawHaar chartPiece (Cdet := Cdet)
      hchartPiece hchartPiece_sub_image
      (by simpa [RawTuple, P, endpointPatch] using hdom) hCdet hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant proves the active endpoint containment from source-cylinder chart-piece support.
/-- With-following readback product-residual finite integrability for original
edge-family priors from active endpoint scalar domination, with the p.13
endpoint containment discharged for source-cylinder chart pieces.

The chart-piece hypothesis is strengthened from `chartPiece ⊆ sourceChart '' V`
to `chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)`.  This is the support
visible in the named selected-entry reference source measure.  Under that
support condition, raw-order injectivity, p.13 raw-chart injectivity, the local
raw/source compatibility, and active endpoint factorization prove the endpoint
patch containment consumed by the active Haar-domination theorem. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ := fun _ ↦ (1 : ℝ≥0∞)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
                      ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                        (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                          density E ≤ Kprior) →
                          (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                            (originalEdgeFamilyPrior
                              (V := reverseVertex W₂)
                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                              density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart originalVolume
    residualIntegrand pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, sourceChart, readback,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, rawChart] using
          exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vraw, hVraw_open, hz₀Vraw, hVrawG, hraw_point, _hraw_measure⟩
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        Vraw hVraw_open hz₀Vraw with
    ⟨V, hV_open, hz₀V, hV_Vraw, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  have hVG : V ⊆ G := by
    intro z hz
    exact hVrawG (hV_Vraw hz)
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V, hsource_contOn_V,
    hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_cylinder
    density Kprior hdensity
  have hchartPiece_sub_image : chartPiece ⊆ sourceChart '' V := by
    intro E hE
    rcases hchartPiece_sub_cylinder hE with ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, rfl⟩
  let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
  let endpointPatch : Set RawTuple := rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
  let activePatchImage := activeChart '' (V ∩ sourceCylinder)
  have hrawOrder_inj : Set.InjOn rawOrderOnEndpoint rawDetChart := by
    intro y hy y' hy' hyy
    have hyinv :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) = y := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy
    have hyinv' :
        topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') = y' := by
      simpa [rawOrderOnEndpoint, rawDetChart, RawTuple] using
        topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          hy'
    calc
      y =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y) := hyinv.symm
      _ =
          topologyTupleEdgeRawOrderInverse
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (rawOrderOnEndpoint y') := by rw [hyy]
      _ = y' := hyinv'
  have hrawChart_inj : Set.InjOn rawChart rawSourceSet := by
    intro y hy y' hy' hchart_eq
    let Sraw : Set RawTuple := rawSourceSet
    let H :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
        (K := ℝ) W₂ B₂ U₀ hU₀
    let yy : Sraw := ⟨y, by simpa [Sraw, rawSourceSet, RawTuple] using hy⟩
    let yy' : Sraw := ⟨y', by simpa [Sraw, rawSourceSet, RawTuple] using hy'⟩
    have hHval : (H yy).1 = (H yy').1 := by
      calc
        (H yy).1 = rawChart y := by
          simpa [H, yy, rawChart, Sraw, rawSourceSet, RawTuple] using
            paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy
        _ = rawChart y' := hchart_eq
        _ = (H yy').1 := by
          simpa [H, yy', rawChart, Sraw, rawSourceSet, RawTuple] using
            (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
              (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) yy').symm
    have hH : H yy = H yy' := Subtype.ext hHval
    exact congrArg Subtype.val (H.injective hH)
  have hraw_point_V :
      ∀ z ∈ V,
        Y z ∈ rawDetChart ∧
          rawOrderOnEndpoint (Y z) ∈ rawSourceSet ∧
          rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := by
    intro z hz
    let zfields : Θ :=
      Case2PassiveThetaWithFollowingFactor.mk
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
        z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2
    have hzfields_eq : zfields = z := by
      simp [zfields, Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.mk, Case2PassiveTheta.A1passive,
        Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
        Case2PassiveTheta.Ctop, Case2PassiveTheta.F3,
        Case2PassiveTheta.yNext]
    have hzraw_fields :
        zfields ∈ Vraw := by
      simpa [hzfields_eq] using hV_Vraw hz
    rcases
        hraw_point z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
          z.1.yNext z.2 hzraw_fields with
      ⟨hYdet_z, _hrawMem_z, _hrawEq_z, _hsource_z, _hread_z, _hleft_z⟩
    have hYdet_fields : Y zfields ∈ rawDetChart := by
      simpa [zfields, Y, rawDetChart, Case2PassiveThetaWithFollowingFactor.mk] using
        hYdet_z
    have hrawMem_fields : rawOrderOnEndpoint (Y zfields) ∈ rawSourceSet := by
      have hm :=
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (by simpa [rawDetChart] using hYdet_fields)
      change
        topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (Y zfields) ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
      exact hm
    have hrawEq_fields :
        rawChart (rawOrderOnEndpoint (Y zfields)) = sourceChart zfields := by
      let retainedData : Θ →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
        fun z ↦
          case2PassiveThetaWithFollowingFactorEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
      have hdet_fields : (retainedData zfields).detChart := by
        exact
          (topologyTuple_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (retainedData zfields)).1
            (by simpa [Y, rawDetChart, retainedData] using hYdet_fields)
      have h :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
          (data := retainedData zfields) hdet_fields
      change
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
            (K := ℝ) W₂ B₂ U₀ hU₀
            (topologyTupleEdgeRawOrder
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
              (topologyTuple (retainedData zfields))) =
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            (K := ℝ) W₂ B₂ U₀ hU₀ (retainedData zfields)
      exact h
    subst zfields
    exact ⟨hYdet_fields, hrawMem_fields, hrawEq_fields⟩
  have hYdet : ∀ z ∈ V, Y z ∈ rawDetChart := fun z hz ↦
    (hraw_point_V z hz).1
  have hrawMem : ∀ z ∈ V, rawOrderOnEndpoint (Y z) ∈ rawSourceSet := fun z hz ↦
    (hraw_point_V z hz).2.1
  have hrawEq :
      ∀ z ∈ V, rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z := fun z hz ↦
    (hraw_point_V z hz).2.2
  have hactive_factor :
      ∀ z ∈ V, Y z = activeWriteback (activeChart z) := by
    intro z hz
    simpa [Θ, RawTuple, Y, activeWriteback, activeChart, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n hS hcont hnext z eNext e
  have hpatch : endpointPatch ⊆ activeWriteback '' activePatchImage := by
    simpa [P, endpointPatch, activePatchImage] using
      endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
        (Y := Y) (sourceChart := sourceChart)
        (rawOrderOnEndpoint := rawOrderOnEndpoint)
        (rawDetChart := rawDetChart) (rawSourceSet := rawSourceSet)
        (rawChart := rawChart) (activeChart := activeChart)
        (activeWriteback := activeWriteback) (V := V)
        (sourceCylinder := sourceCylinder) (chartPiece := chartPiece)
        hchartPiece_sub_cylinder hYdet hrawMem hrawEq hrawChart_inj
        hrawOrder_inj hactive_factor
  exact
    hfinite_package rawHaar chartPiece hchartPiece hchartPiece_sub_image
      hpatch hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant obtains source-cylinder support from the with-following C-one readout.
/-- With-following readback product-residual finite integrability for original
edge-family priors from active endpoint scalar domination, with source-cylinder
support discharged by C-one readout support on the chart piece.

The chart piece only has to lie in the local source-chart image `sourceChart ''
V` and satisfy `cOneReadout E ∈ signedBox` pointwise.  The local readback
left-inverse identifies the C-one readout of `sourceChart z` with `z.1.yNext`,
so the chart piece is actually supported in
`sourceChart '' (V ∩ sourceCylinder)`, which is the hypothesis consumed by the
existing source-cylinder wrapper. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
                        ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                          (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                            density E ≤ Kprior) →
                            (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                              (originalEdgeFamilyPrior
                                (V := reverseVertex W₂)
                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback cOneReadout p13SourceSet
    originalVolume residualIntegrand signedBox
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        G hGopen hz₀G with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_image
    hcOne density Kprior hdensity
  have hchartPiece_sub_cylinder :
      chartPiece ⊆ sourceChart '' (V ∩ {z : Θ | z.1.yNext ∈ signedBox}) := by
    simpa [Θ, EdgeFamily, sourceChart, readback, cOneReadout, signedBox] using
      chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
        W₂ B₂ n hS hcont hnext hU₀ eNext e Rres
        (V := V) (chartPiece := chartPiece)
        hleft_V hchartPiece_sub_image hcOne
  exact
    hfinite_package rawHaar chartPiece hchartPiece
      (by simpa [Θ, signedBox] using hchartPiece_sub_cylinder)
      hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant chooses the source-cylinder shrink after a local prior-density bound.
/-- Source-cylinder supported with-following readback product-residual finite
integrability from an eventual prior-density upper bound along the source
chart.

The chart-piece support remains the source-cylinder image
`chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)`.  The local upper bound for
the original-prior density is supplied as an eventual bound for
`density ∘ sourceChart` near `z₀`; the proof shrinks inside that event and
turns the resulting pointwise chart-piece bound into the restricted a.e. bound
needed by the scalar-domination wrapper. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_eventually_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_eventually :
      ∀ᶠ z in nhds z₀,
        density
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) ≤ Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
                      (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                        (originalEdgeFamilyPrior
                          (V := reverseVertex W₂)
                          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                          density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily Y sourceChart readback rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart originalVolume
    residualIntegrand pivotNext signedBox sourceCylinder activeChart
    activeWriteback
  rcases eventually_nhds_iff.mp hprior_eventually with
    ⟨Gprior, hGprior_bound, hGprior_open, hz₀Gprior⟩
  let Gshrink : Set Θ := G ∩ Gprior
  have hGshrink_open : IsOpen Gshrink := hGopen.inter hGprior_open
  have hz₀Gshrink : z₀ ∈ Gshrink := ⟨hz₀G, hz₀Gprior⟩
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_priorDensity_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        Gshrink hGshrink_open hz₀Gshrink with
    ⟨V, hV_open, hz₀V, hV_Gshrink, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  have hVG : V ⊆ G := fun z hz ↦ (hV_Gshrink hz).1
  have hVGprior : V ⊆ Gprior := fun z hz ↦ (hV_Gshrink hz).2
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_cylinder
  have hpoint_chartPiece :
      ∀ E ∈ chartPiece, density E ≤ Kprior := by
    intro E hE
    rcases hchartPiece_sub_cylinder hE with ⟨z, hz, rfl⟩
    exact hGprior_bound z (hVGprior hz.1)
  have hdensity :
      ∀ᵐ E ∂ originalVolume.restrict chartPiece, density E ≤ Kprior :=
    ae_restrict_upper_of_forall_mem hchartPiece hpoint_chartPiece
  exact
    hfinite_package rawHaar chartPiece hchartPiece hchartPiece_sub_cylinder
      (density := density) (Kprior := Kprior) hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Continuity of the prior pullback is the intended consumer of the eventual-bound wrapper.
/-- Source-cylinder supported with-following readback product-residual finite
integrability from a continuous local prior-density pullback and a strict
basepoint upper bound. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) →
                      (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                        (originalEdgeFamilyPrior
                          (V := reverseVertex W₂)
                          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                          density).restrict chartPiece) < ∞ := by
  exact
    exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_eventually_priorDensity_comp_sourceChart_upper
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
      (density := density) (Kprior := Kprior)
      (eventually_le_const_of_continuousAt_lt hprior_cont hprior_lt)
      G hGopen hz₀G

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This variant combines C-one source-cylinder support with the local prior-density bound.
/-- With-following readback product-residual finite integrability from C-one
signed-box support and an eventual prior-density upper bound along the source
chart.

This combines the C-one support bridge with the source-cylinder eventual
prior-density wrapper: chart pieces only need to be contained in
`sourceChart '' V` and pointwise supported by the C-one readout. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_eventually_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_eventually :
      ∀ᶠ z in nhds z₀,
        density
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) ≤ Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
                        (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                          (originalEdgeFamilyPrior
                            (V := reverseVertex W₂)
                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                            density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback cOneReadout p13SourceSet
    residualIntegrand signedBox
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_eventually_priorDensity_comp_sourceChart_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        (density := density) (Kprior := Kprior) hprior_eventually
        G hGopen hz₀G with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_image hcOne
  have hchartPiece_sub_cylinder :
      chartPiece ⊆ sourceChart '' (V ∩ {z : Θ | z.1.yNext ∈ signedBox}) := by
    simpa [Θ, EdgeFamily, sourceChart, readback, cOneReadout, signedBox] using
      chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
        W₂ B₂ n hS hcont hnext hU₀ eNext e Rres
        (V := V) (chartPiece := chartPiece)
        hleft_V hchartPiece_sub_image hcOne
  exact
    hfinite_package rawHaar chartPiece hchartPiece
      (by simpa [Θ, signedBox] using hchartPiece_sub_cylinder)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Continuous prior pullback is the intended consumer of the combined C-one wrapper.
/-- With-following readback product-residual finite integrability from C-one
signed-box support, continuity of the prior-density pullback, and a strict
basepoint upper bound. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∀ E ∈ chartPiece, cOneReadout E ∈ signedBox) →
                        (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                          (originalEdgeFamilyPrior
                            (V := reverseVertex W₂)
                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                            density).restrict chartPiece) < ∞ := by
  exact
    exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_cOneReadout_mem_signedBox_eventually_priorDensity_comp_sourceChart_upper
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
      (density := density) (Kprior := Kprior)
      (eventually_le_const_of_continuousAt_lt hprior_cont hprior_lt)
      G hGopen hz₀G

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- If the basepoint is in the signed box, shrink inside the source cylinder.
/-- With-following readback product-residual finite integrability after
shrinking the local source chart inside the selected-entry signed-box
cylinder.

If the basepoint already has `yNext` in the selected-entry signed box, then
the source cylinder is an open neighborhood of the basepoint.  Shrinking inside
it removes the chart-piece source-cylinder or C-one readout support hypothesis:
ordinary support `chartPiece ⊆ sourceChart '' V` is enough. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_z0_yNext_mem_signedBox_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (hz₀_signedBox :
      z₀.1.yNext ∈ SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                        (originalEdgeFamilyPrior
                          (V := reverseVertex W₂)
                          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                          density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet
    residualIntegrand signedBox sourceCylinder
  have hsourceCylinder_open : IsOpen sourceCylinder := by
    have hcont_y :
        Continuous (fun z : Θ ↦ z.1.yNext) := by
      change Continuous
        (fun z :
            (Case2PassiveTheta.PassiveFields
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
              (Case2PassiveTheta.Center n S J → ℝ)) ×
              Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ ↦
          z.1.2)
      exact continuous_snd.comp continuous_fst
    simpa [sourceCylinder, signedBox] using
      (SelectedEntrySignedBox.CenterCoord.isOpen_signedBoxSet Rres).preimage hcont_y
  let Gshrink : Set Θ := G ∩ sourceCylinder
  have hGshrink_open : IsOpen Gshrink := hGopen.inter hsourceCylinder_open
  have hz₀Gshrink : z₀ ∈ Gshrink := by
    exact ⟨hz₀G, by simpa [sourceCylinder, signedBox] using hz₀_signedBox⟩
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_continuousAt_priorDensity_comp_sourceChart_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
        (density := density) (Kprior := Kprior) hprior_cont hprior_lt
        Gshrink hGshrink_open hz₀Gshrink with
    ⟨V, hV_open, hz₀V, hV_Gshrink, hleft_V, hsource_inj_V,
      hsource_contOn_V, hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  have hVG : V ⊆ G := fun z hz ↦ (hV_Gshrink hz).1
  have hVsourceCylinder : V ⊆ sourceCylinder := fun z hz ↦ (hV_Gshrink hz).2
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub_image
  have hchartPiece_sub_cylinder :
      chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder) :=
    chartPiece_subset_sourceChart_image_inter_of_subset
      (sourceChart := sourceChart) hVsourceCylinder hchartPiece_sub_image
  exact
    hfinite_package rawHaar chartPiece hchartPiece hchartPiece_sub_cylinder

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Choose a signed box around the basepoint, then use the signed-box shrink.
/-- With-following readback product-residual finite integrability after
choosing a selected-entry signed box around the basepoint and shrinking the
local source chart inside it.

This is the radius-free version of the basepoint signed-box shrink: since the
chosen radii do not occur in the conclusion, every basepoint has a sufficiently
large signed box, and ordinary support `chartPiece ⊆ sourceChart '' V` is
enough. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                        (originalEdgeFamilyPrior
                          (V := reverseVertex W₂)
                          (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                          density).restrict chartPiece) < ∞ := by
  rcases
      SelectedEntrySignedBox.CenterCoord.exists_pos_mem_signedBoxSet
        z₀.1.yNext with
    ⟨Rres, hRres, hz₀_signedBox⟩
  exact
    exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_z0_yNext_mem_signedBox_continuousAt_priorDensity_comp_sourceChart_upper
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) Rres ht hRres hcrit
      hz₀_signedBox (density := density) (Kprior := Kprior)
      hprior_cont hprior_lt G hGopen hz₀G

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The theorem has the same large dependent finite-dimensional chart signature as its neighbors.
/-- With-following readback product-residual finite integrability on p.13 chart
pieces whose readback lands in the returned theta neighborhood.

This is the readback-preimage support version of
`exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_continuousAt_priorDensity_comp_sourceChart_upper`.
The local p.13 image equality converts
`chartPiece ⊆ p13SourceSet` and `chartPiece ⊆ readback ⁻¹' V` into
`chartPiece ⊆ sourceChart '' V`. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_p13SourceSet_readback_preimage_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ p13SourceSet →
                      chartPiece ⊆ readback ⁻¹' V →
                        (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                          (originalEdgeFamilyPrior
                            (V := reverseVertex W₂)
                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                            density).restrict chartPiece) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet residualIntegrand
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_continuousAt_priorDensity_comp_sourceChart_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) ht hcrit
        (density := density) (Kprior := Kprior) hprior_cont hprior_lt
        G hGopen hz₀G with
    ⟨W, hW_open, hz₀W, hWG, _hleft_W, _hsource_inj_W, _hsource_contOn_W,
      _hsource_image_meas_W, _himage_p13_W, hfinite_package⟩
  rcases
      (by
        simpa [Θ, EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_eq_p13SourceEdgeFamilySet_inter_readback_preimage
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ W hW_open hz₀W) with
    ⟨V, hV_open, hz₀V, hVW, _hdetV, _hpivotV, hleft_V_raw,
      hsource_inj_V_raw, hsource_contOn_V_raw, hsource_image_meas_V_raw,
      himage_eq_V_raw⟩
  have hVG : V ⊆ G := fun z hz ↦ hWG (hVW hz)
  have hleft_V : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_V_raw z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hsource_inj_V : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj_V_raw
  have hsource_contOn_V : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn_V_raw
  have hsource_image_meas_V : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image_meas_V_raw
  have himage_eq_V : sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V := by
    simpa [sourceChart, readback, p13SourceSet] using himage_eq_V_raw
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_eq_V, ?_⟩
  intro rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_p13 hchartPiece_readback
  have hchartPiece_image_V : chartPiece ⊆ sourceChart '' V := by
    intro E hE
    rw [himage_eq_V]
    exact ⟨hchartPiece_p13 hE, hchartPiece_readback hE⟩
  have hchartPiece_image_W : chartPiece ⊆ sourceChart '' W := by
    intro E hE
    rcases hchartPiece_image_V hE with ⟨z, hzV, hzE⟩
    exact ⟨z, hVW hzV, hzE⟩
  exact hfinite_package rawHaar chartPiece hchartPiece hchartPiece_image_W

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Use the whole local source-chart image as the chart piece.
/-- With-following readback product-residual finite integrability over the
full local source-chart image.

This is the source-image specialization of
`exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_continuousAt_priorDensity_comp_sourceChart_upper`:
the chart piece is `sourceChart '' V` itself, whose measurability and p.13
support are returned by the local source-image package. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_sourceChart_image_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                  (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                    (originalEdgeFamilyPrior
                      (V := reverseVertex W₂)
                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                      density).restrict (sourceChart '' V)) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet residualIntegrand
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_continuousAt_priorDensity_comp_sourceChart_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) ht hcrit
        (density := density) (Kprior := Kprior) hprior_cont hprior_lt
        G hGopen hz₀G with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V, hsource_contOn_V,
      hsource_image_meas_V, himage_p13_V, hfinite_package⟩
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hsource_image_meas_V, himage_p13_V, ?_⟩
  intro rawHaar _instRawHaar
  exact
    hfinite_package rawHaar (sourceChart '' V) hsource_image_meas_V
      (fun E hE ↦ hE)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Use the whole local p.13/readback-preimage chart piece as the chart piece.
/-- With-following readback product-residual finite integrability over the
full local p.13/readback-preimage chart piece.

This is the p.13/readback-preimage specialization of
`exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_p13SourceSet_readback_preimage_continuousAt_priorDensity_comp_sourceChart_upper`:
the chart piece is `p13SourceSet ∩ readback ⁻¹' V`.  The local image equality
identifies this piece with `sourceChart '' V`, but the statement exposes the
p.13/readback-preimage support directly. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                  (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                    (originalEdgeFamilyPrior
                      (V := reverseVertex W₂)
                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                      density).restrict (p13SourceSet ∩ readback ⁻¹' V)) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet residualIntegrand
  rcases
      exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_p13SourceSet_readback_preimage_continuousAt_priorDensity_comp_sourceChart_upper
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) ht hcrit
        (density := density) (Kprior := Kprior) hprior_cont hprior_lt
        G hGopen hz₀G with
    ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V, hsource_contOn_V,
      hsource_image_meas_V, himage_eq_V, hfinite_package⟩
  have hpiece_meas : MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) := by
    rw [← himage_eq_V]
    exact hsource_image_meas_V
  refine ⟨V, hV_open, hz₀V, hVG, hleft_V, hsource_inj_V,
    hsource_contOn_V, hpiece_meas, himage_eq_V, ?_⟩
  intro rawHaar _instRawHaar
  exact
    hfinite_package rawHaar (p13SourceSet ∩ readback ⁻¹' V) hpiece_meas
      (fun E hE ↦ hE.1) (fun E hE ↦ hE.2)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Reuses the high-heartbeat finite-integral package while adding open-patch bookkeeping.
/-- With-following readback product-residual finite integrability over an
open local p.13/readback-preimage chart piece.

This strengthens
`exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper`
only by shrinking inside the selected-pivot-nonzero locus and exposing that
the same p.13/readback-preimage support is open.  It does not prove global
p.13 source coverage, determinant-chart Haar transport, raw-order Haar
transport, original source-prior transport, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ}
    (hprior_cont :
      ContinuousAt
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          density
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hprior_lt :
      density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                    (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                      (originalEdgeFamilyPrior
                        (V := reverseVertex W₂)
                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                        density).restrict (p13SourceSet ∩ readback ⁻¹' V)) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet residualIntegrand
  let pivotSet : Set Θ :=
    {z | case2PassiveThetaPivotNonzero
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous
          (fun z : Θ ↦
            z.1.yNext (case2PassiveThetaPivotNext n hS hnext)) := by
      simpa [Θ, Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd.comp
            (continuous_fst : Continuous (fun z : Θ ↦ z.1))))
    simpa [pivotSet, case2PassiveThetaPivotNonzero] using
      (isOpen_ne.preimage hpivot_cont)
  let Gpivot : Set Θ := G ∩ pivotSet
  have hGpivot_open : IsOpen Gpivot := hGopen.inter hpivotSet_open
  have hz₀Gpivot : z₀ ∈ Gpivot := by
    exact ⟨hz₀G, by simpa [pivotSet] using hpivot₀⟩
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback, p13SourceSet,
          residualIntegrand, Gpivot] using
          exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) ht hcrit
            (density := density) (Kprior := Kprior) hprior_cont hprior_lt
            Gpivot hGpivot_open hz₀Gpivot) with
    ⟨V, hVopen, hz₀V, hVGpivot, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, himage_eq, hfinite⟩
  have hVG : V ⊆ G := fun z hz ↦ hVGpivot.1 hz
  have hVpivot : ∀ z ∈ V,
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1 := by
    intro z hz
    exact hVGpivot.2 hz
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hpatch_open : IsOpen (p13SourceSet ∩ readback ⁻¹' V) := by
    simpa [EdgeFamily, readback, p13SourceSet] using
      isOpen_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet_inter_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_preimage_of_subset_pivotNonzero
        W₂ B₂ n hS hnext hU₀ e hVopen hVpivot
  exact
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpatch_open, himage_eq, hfinite⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Uses the open-patch finite-integral theorem after deriving the pullback density bound.
/-- With-following readback product-residual finite integrability over an
open local p.13/readback-preimage chart piece, assuming only continuity of
the supplied edge-family prior density at the charted base point.

This is the local prior-regularity adapter for
`exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper`:
continuity of `density` at `sourceChart z₀`, together with local continuity
of `sourceChart`, supplies the required pullback-continuity and local upper
bound.  It still does not define Aoyagi's statistical prior, prove global
source coverage, source-rank coverage, source-prior transport, Haar/Jacobian
transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_of_continuousAt_priorDensity
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt density
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let residualIntegrand : EdgeFamily → ℝ≥0∞ :=
      fun E ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                    (∫⁻ E : EdgeFamily, residualIntegrand E ∂
                      (originalEdgeFamilyPrior
                        (V := reverseVertex W₂)
                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                        density).restrict (p13SourceSet ∩ readback ⁻¹' V)) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet residualIntegrand
  have hsource_cont : ContinuousAt sourceChart z₀ := by
    simpa [Θ, EdgeFamily, sourceChart] using
      continuousAt_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_detSector_pivotNonzero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀
  have hprior_pullback :
      ContinuousAt (fun z : Θ ↦ density (sourceChart z)) z₀ := by
    exact
      ContinuousAt.comp
        (x := z₀) (f := sourceChart) (g := density)
        (by simpa [sourceChart] using hprior_cont) hsource_cont
  have hprior_lt :
      density (sourceChart z₀) < density (sourceChart z₀) + 1 := by
    linarith
  simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback, p13SourceSet,
    residualIntegrand] using
    exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
      (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      eNext e z₀ hdet₀ hpivot₀ hF₀det (t := t) ht hcrit
      (density := density) (Kprior := density (sourceChart z₀) + 1)
      hprior_pullback hprior_lt G hGopen hz₀G

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper composes the endpoint-density volume wrapper with the prior-density handoff.
/-- Same-shrink with-following original-prior readback domination from a
localized endpoint-image weighted-Haar identity, a lower endpoint density bound,
a lower source-density bound, and a local upper bound for the original prior
density.

This is the prior analogue of
`exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower`.
The endpoint image identity, endpoint lower bound, source-density lower bound,
and prior-density upper bound remain explicit hypotheses.  This theorem does
not prove determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, finite-integral transfer, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      let P : Set RawTuple := rawSourceSet ∩ rawChart ⁻¹' chartPiece
                      let endpointReferenceImage : Measure RawTuple :=
                        case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                          n hS hcont hnext eNext e Rres V
                      endpointReferenceImage =
                          (rawHaar.restrict
                            (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict
                              (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂ originalVolume.restrict chartPiece,
                                      density E ≤ Kprior) →
                                      let cHaar :=
                                        (originalTupleVolumeHaarScalarOfMap d
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀) rawHaar)
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        AEMeasurable readback
                                          ((originalEdgeFamilyPrior
                                            (V := reverseVertex W₂)
                                            (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                            density).restrict chartPiece) ∧
                                          Measure.map readback
                                              ((originalEdgeFamilyPrior
                                                (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece) ≤
                                            Cprior • coordinateSourceMeasure.restrict G := by
  intro RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity, rawSourceSet,
          p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hvolume_package⟩
  have hleft_local : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz
  have himage_p13_local : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleft_local, hsource_inj, hsource_contOn,
    hsource_image, himage_p13_local, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image P endpointReferenceImage hendpoint hCdet
    hendpoint_lower hsource_lower hε_ne_zero hε_ne_top density Kprior
    hdensity cHaar Ddet Dvol Cprior
  rcases
      (by
        simpa [RawTuple, EdgeFamily, endpointReferenceImage,
          endpointJacobianDensity, d, originalVolume, cHaar, Ddet, Dvol, P] using
          hvolume_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
            hchartPiece hchartPiece_sub_image hendpoint hCdet
            hendpoint_lower hsource_lower hε_ne_zero hε_ne_top) with
    ⟨hDdet, hreadback_volume, hvolume_readback_dom⟩
  let originalPriorPiece :=
    (originalEdgeFamilyPrior (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀) density).restrict chartPiece
  have hprior_volume :
      originalPriorPiece ≤
        ENNReal.ofReal Kprior • originalVolume.restrict chartPiece := by
    simpa [originalPriorPiece, originalVolume] using
      originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        (s := chartPiece) (K := Kprior) hchartPiece hdensity
  have hprior_readback :
      AEMeasurable readback originalPriorPiece ∧
        Measure.map readback originalPriorPiece ≤
          (ENNReal.ofReal Kprior * Dvol) • coordinateSourceMeasure.restrict G :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
      (sourceRef := originalVolume.restrict chartPiece)
      (μ := originalPriorPiece)
      (thetaRef := coordinateSourceMeasure.restrict G)
      (C := ENNReal.ofReal Kprior) (Csource := Dvol)
      hreadback_volume hvolume_readback_dom hprior_volume
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  exact ⟨hCprior,
    by simpa [originalPriorPiece] using hprior_readback.1,
    by simpa [originalPriorPiece, Cprior] using hprior_readback.2⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This is the formal-product analogue of the determinant-domination source-reference bridge.
/-- Formal-product chart pieces are dominated by the coordinate source
reference under determinant-chart reverse domination and a lower
source-density bound.

This composes the same-shrink raw/source package with the conditional
formal-product source-reference domination theorem.  The determinant-side
reverse domination and source-density lower bound remain explicit hypotheses;
no determinant Haar transport, original source-prior transport, source
coverage, normal crossings, pole order, or RLCT extraction is proved. -/
theorem exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_coordinateSourceReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
        ∀ {Cdet ε : ℝ≥0∞},
          chartPiece ⊆ p13SourceSet →
            rawHaar.restrict rawDetChart ≤
              Cdet • Measure.map Y (passiveSource.restrict V) →
              Cdet < ∞ →
                (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                  ε ≠ 0 →
                    ε ≠ ∞ →
                      let Ddet := Cdet * ε⁻¹
                      let formalProductMeasure : Measure EdgeFamily :=
                        Measure.map
                          (fun z : RawTuple ↦
                            rawChart
                              (topologyTupleEdgeRawOrder
                                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                                (κ' := throughSubspaceEndpointComplementIndex
                                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                          ((rawHaar.restrict rawDetChart).withDensity
                            (fun z : RawTuple ↦
                              ENNReal.ofReal
                                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                                  (κ' := throughSubspaceEndpointComplementIndex
                                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                      let sourceRef := Measure.map sourceChart
                        (coordinateSourceMeasure.restrict V)
                      Ddet < ∞ ∧
                        formalProductMeasure.restrict chartPiece ≤ Ddet • sourceRef := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple
    EdgeFamily Y rawMap rawChart jacobianDensity baseJ sourceChart
    sourceDensity coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet] using
          exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vformal, hVformalopen, hz₀Vformal, hVformalG, hformal_dom⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet] using
          exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vformal
            hVformalopen hz₀Vformal) with
    ⟨V, hVopen, hz₀V, hV_formal, _hleftV, _hsource_injV,
      _hsource_contOnV, _hsource_imageV, _himage_p13V, _hraw_memV,
      _hrawMap_aemeas, _hmeasure_maps, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVformalG (hV_formal hz)
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece_sub hdet_dom
    hCdet hsource_lower hε_ne_zero hε_ne_top Ddet formalProductMeasure sourceRef
  rcases (hraw_dom_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
    hε_ne_top) with
    ⟨hDdet, hraw_dom⟩
  have hrestrict_formal :
      (coordinateSourceMeasure.restrict V).restrict Vformal =
        coordinateSourceMeasure.restrict V :=
    restrict_restrict_eq_self_of_subset hVopen.measurableSet hV_formal
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        Ddet •
          Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vformal) := by
    simpa [RawTuple, rawMap, rawSourceSet, coordinateSourceMeasure, Ddet,
      hrestrict_formal] using hraw_dom
  have hformal_piece :
      formalProductMeasure.restrict chartPiece ≤ Ddet • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, rawChart, coordinateSourceMeasure,
      formalProductMeasure, sourceRef, Ddet, hrestrict_formal] using
      hformal_dom (coordinateSourceMeasure.restrict V) rawHaar chartPiece
        (D := Ddet) hchartPiece_sub hraw_dom_bridge
  exact ⟨by simpa [Ddet] using hDdet, hformal_piece⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This consumes the reference-source formal-product bridge at the p.13
-- original-volume interface.
/-- With-following original-volume chart pieces are dominated by the reference
source under determinant-chart reverse domination.

This is a direct consumer of
`exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_referenceSource_of_detHaar_restrict_le_smul_endpointTopologyTuple`.
The determinant-side reverse domination, chart-piece measurability, and
p.13-support hypotheses remain explicit.  No exact raw-Haar pushforward,
determinant Haar transport, source-image coverage, source-rank coverage,
source-prior or original-prior transport, readback domination, normal
crossings, pole order, or RLCT extraction is proved. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_referenceSource_of_detHaar_restrict_le_smul_endpointTopologyTuple
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∃ CJ : ℝ≥0∞, CJ < ∞ ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
          ∀ chartPiece : Set EdgeFamily,
          ∀ {Cdet : ℝ≥0∞},
            MeasurableSet chartPiece →
              chartPiece ⊆ p13SourceSet →
                rawHaar.restrict rawDetChart ≤
                  Cdet • Measure.map Y (referenceSource.restrict V) →
                  Cdet < ∞ →
                    let Ddet := Cdet * CJ
                    let cHaar :=
                      originalTupleVolumeHaarScalarOfMap d
                        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                          W₂ B₂ U₀) rawHaar
                    let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                    let sourceRef :=
                      Measure.map sourceChart (referenceSource.restrict V)
                    Dvol < ∞ ∧
                      originalVolume.restrict chartPiece ≤ Dvol • sourceRef := by
  intro RawTuple EdgeFamily Y referenceSource sourceChart rawDetChart
    p13SourceSet d originalVolume
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  let rawMap :
      Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        RawTuple :=
    fun z ↦
      topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
  let rawSourceSet : Set RawTuple :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet, rawChart] using
          exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vformal, hVformalopen, hz₀Vformal, hVformalG, hformal_dom⟩
  rcases
      (by
        simpa [RawTuple, Y, referenceSource, rawMap, rawDetChart,
          rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_referenceSource_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ Rres Vformal hVformalopen hz₀Vformal) with
    ⟨V, hVopen, hz₀V, hV_formal, CJ, hCJ, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVformalG (hV_formal hz)
  refine ⟨V, hVopen, hz₀V, hVG, CJ, hCJ, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet hchartPiece hchartPiece_sub
    hdet_dom hCdet Ddet cHaar Dvol sourceRef
  rcases hraw_dom_package rawHaar hdet_dom hCdet with
    ⟨hDdet, hraw_dom⟩
  have hrestrict_formal :
      (referenceSource.restrict V).restrict Vformal =
        referenceSource.restrict V :=
    restrict_restrict_eq_self_of_subset hVopen.measurableSet hV_formal
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        Ddet •
          Measure.map rawMap ((referenceSource.restrict V).restrict Vformal) := by
    simpa [RawTuple, rawMap, rawSourceSet, referenceSource, Ddet,
      hrestrict_formal] using hraw_dom
  have hformal_piece :
      (Measure.map
          (fun z : RawTuple ↦
            rawChart
              (topologyTupleEdgeRawOrder
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
          ((rawHaar.restrict rawDetChart).withDensity
            (fun z : RawTuple ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))).restrict
        chartPiece ≤ Ddet • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, rawChart, referenceSource,
      sourceRef, Ddet, hrestrict_formal] using
      hformal_dom (referenceSource.restrict V) rawHaar chartPiece
        (D := Ddet) hchartPiece_sub hraw_dom_bridge
  have horiginal :
      originalVolume.restrict chartPiece ≤ Dvol • sourceRef := by
    simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, rawChart,
      d, originalVolume, Ddet, cHaar, Dvol, sourceRef,
      originalTupleVolumeHaarScalarOfMap] using
      originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
        (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
        rawHaar hchartPiece hchartPiece_sub (sourceRef := sourceRef)
        (D := Ddet) hformal_piece
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  exact ⟨hDvol, horiginal⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This is the with-following reference-source analogue of the formal-product
-- determinant-domination bridge.
/-- With-following formal-product chart pieces are dominated by the reference
source under determinant-chart reverse domination.

This composes the formal-product/source-reference socket with the raw
reference-source handoff.  The determinant-side reverse domination remains an
explicit hypothesis; the only extra scalar is the finite local upper bound for
the retained-passive raw-order Jacobian density.  No determinant Haar
transport, exact raw-Haar pushforward, original source-prior transport,
source coverage, normal crossings, pole order, or RLCT extraction is proved. -/
theorem exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_referenceSource_of_detHaar_restrict_le_smul_endpointTopologyTuple
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∃ CJ : ℝ≥0∞, CJ < ∞ ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
          ∀ chartPiece : Set EdgeFamily,
          ∀ {Cdet : ℝ≥0∞},
            chartPiece ⊆ p13SourceSet →
              rawHaar.restrict rawDetChart ≤
                Cdet • Measure.map Y (referenceSource.restrict V) →
                Cdet < ∞ →
                  let Ddet := Cdet * CJ
                  let formalProductMeasure : Measure EdgeFamily :=
                    Measure.map
                      (fun z : RawTuple ↦
                        rawChart
                          (topologyTupleEdgeRawOrder
                            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                            (κ' := throughSubspaceEndpointComplementIndex
                              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                      ((rawHaar.restrict rawDetChart).withDensity
                        (fun z : RawTuple ↦
                          ENNReal.ofReal
                            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                              (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                              (κ' := throughSubspaceEndpointComplementIndex
                                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                  let sourceRef := Measure.map sourceChart (referenceSource.restrict V)
                  Ddet < ∞ ∧
                    formalProductMeasure.restrict chartPiece ≤ Ddet • sourceRef := by
  intro RawTuple EdgeFamily Y referenceSource sourceChart rawDetChart
    p13SourceSet rawChart
  let rawMap :
      Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        RawTuple :=
    fun z ↦
      topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
  let rawSourceSet : Set RawTuple :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet, rawChart] using
          exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vformal, hVformalopen, hz₀Vformal, hVformalG, hformal_dom⟩
  rcases
      (by
        simpa [RawTuple, Y, referenceSource, rawMap, rawDetChart,
          rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_referenceSource_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ Rres Vformal hVformalopen hz₀Vformal) with
    ⟨V, hVopen, hz₀V, hV_formal, CJ, hCJ, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVformalG (hV_formal hz)
  refine ⟨V, hVopen, hz₀V, hVG, CJ, hCJ, ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet hchartPiece_sub hdet_dom hCdet
    Ddet formalProductMeasure sourceRef
  rcases hraw_dom_package rawHaar hdet_dom hCdet with
    ⟨hDdet, hraw_dom⟩
  have hrestrict_formal :
      (referenceSource.restrict V).restrict Vformal =
        referenceSource.restrict V :=
    restrict_restrict_eq_self_of_subset hVopen.measurableSet hV_formal
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        Ddet •
          Measure.map rawMap ((referenceSource.restrict V).restrict Vformal) := by
    simpa [RawTuple, rawMap, rawSourceSet, referenceSource, Ddet,
      hrestrict_formal] using hraw_dom
  have hformal_piece :
      formalProductMeasure.restrict chartPiece ≤ Ddet • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, rawChart, referenceSource,
      formalProductMeasure, sourceRef, Ddet, hrestrict_formal] using
      hformal_dom (referenceSource.restrict V) rawHaar chartPiece
        (D := Ddet) hchartPiece_sub hraw_dom_bridge
  exact ⟨by simpa [Ddet] using hDdet, hformal_piece⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This composes several large Case 2 local-measure packages through nested `let` binders.
/-- Same-shrink original-volume readback domination from determinant-chart
reverse domination and a lower source-density bound.

The theorem first chooses a readback bridge shrink, then chooses a smaller
same-shrink raw/source package inside it.  The returned `V` is the smaller
shrink.  The determinant-side domination and source-density lower bound are
still hypotheses on this returned `V`. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      rawHaar.restrict rawDetChart ≤
                        Cdet • Measure.map Y (passiveSource.restrict V) →
                        Cdet < ∞ →
                          (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                            ε ≠ 0 →
                              ε ≠ ∞ →
                                let c :=
                                  (originalTupleVolumeHaarScalarOfMap d
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀) rawHaar)
                                let D := Cdet * ε⁻¹
                                AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                                  Measure.map readback (originalVolume.restrict chartPiece) ≤
                                    ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                      coordinateSourceMeasure.restrict G) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [rawMap, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vrb, hVrbopen, hz₀Vrb, hVrbG, _hleft_rb, _hinj_rb, _hcont_rb,
      _himage_rb, _hp13_rb, hreadback_bridge⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet] using
          exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vrb
            hVrbopen hz₀Vrb) with
    ⟨V, hVopen, hz₀V, hV_vrb, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, _hraw_memV, _hrawMap_aemeas,
      _hmeasure_maps, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVrbG (hV_vrb hz)
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece hchartPiece_sub_image
    hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top c D
  rcases (hraw_dom_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
    hε_ne_top) with
    ⟨_hD, hraw_dom⟩
  have hchartPiece_sub_vrb : chartPiece ⊆ sourceChart '' Vrb := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hV_vrb hzV, rfl⟩
  have hrestrict_vrb :
      (coordinateSourceMeasure.restrict V).restrict Vrb =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hV_vrb hzV))
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        D • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vrb) := by
    simpa [RawTuple, rawMap, rawSourceSet, coordinateSourceMeasure, D, hrestrict_vrb] using
      hraw_dom
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
            (coordinateSourceMeasure.restrict V).restrict G) := by
    simpa [rawMap, rawSourceSet, d, originalVolume, c, D] using
      hreadback_bridge (coordinateSourceMeasure.restrict V) rawHaar chartPiece
        (D := D) hchartPiece hchartPiece_sub_vrb hraw_dom_bridge
  have hrestrict_G :
      (coordinateSourceMeasure.restrict V).restrict G =
        coordinateSourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hVG hzV))
  have hV_le_G :
      coordinateSourceMeasure.restrict V ≤
        (1 : ℝ≥0∞) • coordinateSourceMeasure.restrict G := by
    simpa using (Measure.restrict_mono hVG le_rfl)
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        (((c⁻¹ : NNReal) : ℝ≥0∞) * D) • coordinateSourceMeasure.restrict G := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) * (1 : ℝ≥0∞)) •
            coordinateSourceMeasure.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul
        (by simpa [hrestrict_G] using hreadback_volume.2) hV_le_G
    simpa [mul_one] using hstep
  exact ⟨hreadback_volume.1, hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper replaces the determinant-domination socket by a full endpoint-image density identity.
/-- Same-shrink original-volume readback domination from a full determinant-chart
endpoint-image weighted-Haar identity and a lower endpoint density bound.

The endpoint image is the actual image of the finite passive product source
used by the coordinate source measure:
`Measure.map Y (passiveSource.restrict V)`.  The weighted-Haar identity and
the lower bound for the endpoint density remain explicit hypotheses.  This
does not prove determinant-chart Haar transport, raw-order Haar transport,
source-image coverage, original source-prior transport, normal crossings, pole
order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointTopologyTupleImage_eq_withDensity_formalProductAbsDet_rawDetChart_of_one_le_mul_density_sourceDensity_lower
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                ∀ {Cdet ε : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      Measure.map Y (passiveSource.restrict V) =
                          (rawHaar.restrict rawDetChart).withDensity
                            endpointJacobianDensity →
                        Cdet < ∞ →
                          (∀ᵐ y ∂rawHaar.restrict rawDetChart,
                            1 ≤ Cdet * endpointJacobianDensity y) →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  let c :=
                                    (originalTupleVolumeHaarScalarOfMap d
                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                        W₂ B₂ U₀) rawHaar)
                                  let D := Cdet * ε⁻¹
                                  D < ∞ ∧
                                    AEMeasurable readback
                                      (originalVolume.restrict chartPiece) ∧
                                      Measure.map readback
                                          (originalVolume.restrict chartPiece) ≤
                                        ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                          coordinateSourceMeasure.restrict G) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G
            hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hreadback_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar chartPiece Cdet ε hchartPiece
    hchartPiece_sub_image hendpoint hCdet hendpoint_lower hsource_lower
    hε_ne_zero hε_ne_top c D
  have hdet_dom :
      rawHaar.restrict rawDetChart ≤
        Cdet • Measure.map Y (passiveSource.restrict V) :=
    restrict_le_smul_of_eq_withDensity_of_one_le_mul_density
      hendpoint hCdet hendpoint_lower
  have hDfinite : D < ∞ := by
    dsimp [D]
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε_ne_zero))
  rcases
      hreadback_package rawHaar chartPiece (Cdet := Cdet) (ε := ε)
        hchartPiece hchartPiece_sub_image hdet_dom hCdet hsource_lower
        hε_ne_zero hε_ne_top with
    ⟨hreadback_aemeas, hreadback_le⟩
  exact ⟨by simpa [D] using hDfinite, by simpa using hreadback_aemeas,
    by simpa [c, D] using hreadback_le⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This measure-level wrapper keeps the determinant and density inputs explicit.
/-- Original edge-family priors are dominated on the full local source-chart
image by the chart-produced coordinate source measure.

The determinant-side reverse domination, the lower bound for `sourceDensity`,
and the local upper bound for the original-prior density remain explicit
hypotheses.  This theorem does not prove determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_priorDensity_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ᵐ E ∂originalVolume.restrict
                                (sourceChart '' V), density E ≤ Kprior) →
                                let cHaar :=
                                  (originalTupleVolumeHaarScalarOfMap d
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀) rawHaar)
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vvol, hVvolopen, hz₀Vvol, hVvolG, hvolume_bridge⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet, p13SourceSet] using
          exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vvol
            hVvolopen hz₀Vvol) with
    ⟨V, hVopen, hz₀V, hV_vvol, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, _hraw_memV, _hrawMap_aemeas,
      _hmeasure_maps, hraw_dom_package⟩
  have hVG : V ⊆ G := fun z hz ↦ hVvolG (hV_vvol hz)
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_lower
    hε_ne_zero hε_ne_top density Kprior hdensity cHaar Ddet Dvol Cprior
  rcases (hraw_dom_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
    hε_ne_top) with
    ⟨hDdet, hraw_dom⟩
  have hrestrict_vvol :
      (coordinateSourceMeasure.restrict V).restrict Vvol =
        coordinateSourceMeasure.restrict V :=
    restrict_restrict_eq_self_of_subset hVopen.measurableSet hV_vvol
  have hraw_dom_bridge :
      rawHaar.restrict rawSourceSet ≤
        Ddet • Measure.map rawMap ((coordinateSourceMeasure.restrict V).restrict Vvol) := by
    simpa [RawTuple, rawMap, rawSourceSet, coordinateSourceMeasure, Ddet,
      hrestrict_vvol] using hraw_dom
  have himage_sub_p13 : sourceChart '' V ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V' E hE
  have hvolume_dom :
      originalVolume.restrict (sourceChart '' V) ≤
        Dvol • Measure.map sourceChart (coordinateSourceMeasure.restrict V) := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, Ddet, Dvol, cHaar, hrestrict_vvol] using
      hvolume_bridge (coordinateSourceMeasure.restrict V) rawHaar
        (sourceChart '' V) (D := Ddet) hsource_imageV himage_sub_p13
        hraw_dom_bridge
  have hvolume_dom_image :
      originalVolume.restrict (sourceChart '' V) ≤
        Dvol •
          (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
            (sourceChart '' V) :=
    restrict_le_smul_restrict_of_le_smul_of_subset
      (μ := originalVolume)
      (η := Measure.map sourceChart (coordinateSourceMeasure.restrict V))
      (s := sourceChart '' V) (t := sourceChart '' V) (c := Dvol)
      hsource_imageV (fun _ h ↦ h) hvolume_dom
  have hprior_dom :
      (originalEdgeFamilyPrior (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        density).restrict (sourceChart '' V) ≤
          Cprior •
            (Measure.map sourceChart (coordinateSourceMeasure.restrict V)).restrict
              (sourceChart '' V) := by
    simpa [originalEdgeFamilyPrior, originalVolume, Cprior] using
      restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
        (μ := originalVolume)
        (ν := (Measure.map sourceChart
          (coordinateSourceMeasure.restrict V)).restrict (sourceChart '' V))
        (density := density) (s := sourceChart '' V) (K := Kprior)
        (c := Dvol) hsource_imageV hvolume_dom_image hdensity
  have hDdet' : Ddet < ∞ := by
    simpa [Ddet] using hDdet
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet'
  have hCprior : Cprior < ∞ := by
    dsimp [Cprior]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDvol
  exact ⟨hCprior, hprior_dom⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper replaces two a.e. density sockets by pointwise bounds on the returned image.
/-- Full source-image prior domination using pointwise bounds on the returned
source-chart image.

The pointwise source-image lower bound and prior-density upper bound are only
stronger sufficient hypotheses for the existing a.e. density sockets.  This
theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ E ∈ sourceChart '' V, density E ≤ Kprior) →
                                let cHaar :=
                                  (originalTupleVolumeHaarScalarOfMap d
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀) rawHaar)
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_image_lower
    hε_ne_zero hε_ne_top density Kprior hprior_image_upper cHaar Ddet Dvol Cprior
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    simpa [sourceDensity] using
      ae_restrict_comp_lower_of_forall_image_lower
        (μ := baseJ) (V := V) (f := sourceChart)
        (g := sourceImageDensity) (ε := ε)
        hVopen.measurableSet hsource_image_lower
  have hprior_upper :
      ∀ᵐ E ∂originalVolume.restrict (sourceChart '' V),
        density E ≤ Kprior :=
    ae_restrict_upper_of_forall_mem
      (μ := originalVolume) (s := sourceChart '' V)
      (f := density) (K := Kprior) hsource_imageV hprior_image_upper
  simpa [cHaar, Ddet, Dvol, Cprior] using
    hprior_package rawHaar hdet_dom hCdet hsource_lower hε_ne_zero
      hε_ne_top (density := density) (Kprior := Kprior) hprior_upper

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper inherits returned-image bounds from the caller's larger input image.
/-- Full source-image prior domination using pointwise bounds on the input
source-chart image.

The returned shrink `V` is contained in the input neighborhood `G`, so bounds
on `sourceChart '' G` restrict to the returned image `sourceChart '' V`.  This
theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_input_image_lower_priorDensity_input_image_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ {Cdet ε : ℝ≥0∞},
                  rawHaar.restrict rawDetChart ≤
                    Cdet • Measure.map Y (passiveSource.restrict V) →
                    Cdet < ∞ →
                      (∀ E ∈ sourceChart '' G, ε ≤ sourceImageDensity E) →
                        ε ≠ 0 →
                          ε ≠ ∞ →
                            ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                              (∀ E ∈ sourceChart '' G, density E ≤ Kprior) →
                                let cHaar :=
                                  (originalTupleVolumeHaarScalarOfMap d
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀) rawHaar)
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                    density).restrict (sourceChart '' V) ≤
                                      Cprior •
                                        (Measure.map sourceChart
                                          (coordinateSourceMeasure.restrict V)).restrict
                                            (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_priorDensity_image_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hsource_input_lower
    hε_ne_zero hε_ne_top density Kprior hprior_input_upper cHaar Ddet Dvol Cprior
  have hsource_image_lower :
      ∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hsource_input_lower (sourceChart z) ⟨z, hVG hzV, rfl⟩
  have hprior_image_upper :
      ∀ E ∈ sourceChart '' V, density E ≤ Kprior := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hprior_input_upper (sourceChart z) ⟨z, hVG hzV, rfl⟩
  have hsource_image_lower' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ V →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            ε ≤ sourceImageDensity E := by
    intro E a a_1 a_2 a_3 b b_1 hzV hEq
    exact hsource_image_lower E ⟨((a, a_1, a_2, a_3, b), b_1), hzV, hEq⟩
  have hprior_image_upper' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ V →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            density E ≤ Kprior := by
    intro E a a_1 a_2 a_3 b b_1 hzV hEq
    exact hprior_image_upper E ⟨((a, a_1, a_2, a_3, b), b_1), hzV, hEq⟩
  simpa [cHaar, Ddet, Dvol, Cprior] using
    hprior_package rawHaar hdet_dom hCdet hsource_image_lower' hε_ne_zero
      hε_ne_top (density := density) (Kprior := Kprior) hprior_image_upper'

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper chooses the input neighborhood from local pullback density bounds.
/-- Full source-image prior domination using eventual pullback bounds near the
base passive-theta point.

The shrink `V` is chosen after `ε`, `density`, `Kprior`, and the two eventual
pullback-bound hypotheses are fixed.  This theorem does not prove
determinant-chart Haar transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image coverage, source-rank coverage, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    {ε : ℝ≥0∞}
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {Kprior : ℝ} :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    (∀ᶠ z in nhds z₀, ε ≤ sourceImageDensity (sourceChart z)) →
      (∀ᶠ z in nhds z₀, density (sourceChart z) ≤ Kprior) →
        ∃ V :
          Set
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          IsOpen V ∧ z₀ ∈ V ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (sourceChart '' V) ∧
                  (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                    ∀ {Cdet : ℝ≥0∞},
                      rawHaar.restrict rawDetChart ≤
                        Cdet • Measure.map Y (passiveSource.restrict V) →
                        Cdet < ∞ →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              let cHaar :=
                                (originalTupleVolumeHaarScalarOfMap d
                                  (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                    W₂ B₂ U₀) rawHaar)
                              let Ddet := Cdet * ε⁻¹
                              let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                              let Cprior := ENNReal.ofReal Kprior * Dvol
                              Cprior < ∞ ∧
                                (originalEdgeFamilyPrior (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density).restrict (sourceChart '' V) ≤
                                    Cprior •
                                      (Measure.map sourceChart
                                        (coordinateSourceMeasure.restrict V)).restrict
                                          (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d originalVolume
    hsource_eventually hprior_eventually
  rcases eventually_nhds_iff.mp (hsource_eventually.and hprior_eventually) with
    ⟨G, hGbounds, hGopen, hz₀G⟩
  have hsource_input_lower :
      ∀ E ∈ sourceChart '' G, ε ≤ sourceImageDensity E := by
    intro E hE
    rcases hE with ⟨z, hzG, rfl⟩
    exact (hGbounds z hzG).1
  have hprior_input_upper :
      ∀ E ∈ sourceChart '' G, density E ≤ Kprior := by
    intro E hE
    rcases hE with ⟨z, hzG, rfl⟩
    exact (hGbounds z hzG).2
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_input_image_lower_priorDensity_input_image_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, _hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  have hsource_input_lower' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ G →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            ε ≤ sourceImageDensity E := by
    intro E a a_1 a_2 a_3 b b_1 hzG hEq
    exact hsource_input_lower E ⟨((a, a_1, a_2, a_3, b), b_1), hzG, hEq⟩
  have hprior_input_upper' :
      ∀ E a a_1 a_2 a_3 b b_1,
        ((a, a_1, a_2, a_3, b), b_1) ∈ G →
          sourceChart ((a, a_1, a_2, a_3, b), b_1) = E →
            density E ≤ Kprior := by
    intro E a a_1 a_2 a_3 b b_1 hzG hEq
    exact hprior_input_upper E ⟨((a, a_1, a_2, a_3, b), b_1), hzG, hEq⟩
  refine ⟨V, hVopen, hz₀V, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet hdet_dom hCdet hε_ne_zero hε_ne_top
    cHaar Ddet Dvol Cprior
  simpa [cHaar, Ddet, Dvol, Cprior] using
    hprior_package rawHaar hdet_dom hCdet hsource_input_lower' hε_ne_zero
      hε_ne_top (density := density) (Kprior := Kprior) hprior_input_upper'

/-- Continuity of the two density pullbacks plus strict basepoint inequalities
produces the eventual hypotheses consumed by the full prior-domination wrapper. -/
theorem eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt
    {α β : Type*} [TopologicalSpace α] {sourceChart : α → β}
    {sourceImageDensity : β → ℝ≥0∞} {density : β → ℝ}
    {z₀ : α} {ε : ℝ≥0∞} {Kprior : ℝ}
    (hsource_cont : ContinuousAt (fun z ↦ sourceImageDensity (sourceChart z)) z₀)
    (hsource_lt : ε < sourceImageDensity (sourceChart z₀))
    (hprior_cont : ContinuousAt (fun z ↦ density (sourceChart z)) z₀)
    (hprior_lt : density (sourceChart z₀) < Kprior) :
    (∀ᶠ z in nhds z₀, ε ≤ sourceImageDensity (sourceChart z)) ∧
      (∀ᶠ z in nhds z₀, density (sourceChart z) ≤ Kprior) :=
  ⟨eventually_const_le_of_continuousAt_lt hsource_cont hsource_lt,
    eventually_le_const_of_continuousAt_lt hprior_cont hprior_lt⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This final wrapper elaborates the direct finite-integral socket plus the same-shrink bridge.
/-- Original edge-family priors feed into the Case 2 finite-integral socket
from determinant-chart reverse domination and a lower source-density bound.

This is the determinant-side analogue of the raw-source domination wrapper:
for chart pieces inside the actual source-chart image, determinant domination
plus a same-shrink lower bound for the source density supplies the
original-volume readback domination required by the direct finite-integral
front end.

The determinant-side domination and source-density lower bound remain
chart-piece hypotheses.  This theorem does not prove determinant-chart Haar
transport, raw-order Haar transport, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      (originalTupleVolumeHaarScalarOfMap d
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W₂ B₂ U₀) m)
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {chartPiece : Set EdgeFamily},
                        MeasurableSet chartPiece →
                          chartPiece ⊆ sourceLocal →
                            chartPiece ⊆ sourceChart '' V →
                              ∀ {Cdet ε : ℝ≥0∞},
                                m.restrict rawDetChart ≤
                                  Cdet • Measure.map Y (passiveSource.restrict V) →
                                  Cdet < ∞ →
                                    (∀ᵐ z ∂baseJ.restrict V,
                                      ε ≤ sourceDensity z) →
                                      ε ≠ 0 →
                                        ε ≠ ∞ →
                                          ∀ {density : EdgeFamily → ℝ}
                                            {Kprior : ℝ},
                                            (∀ᵐ E ∂(originalEdgeFamilyVolume
                                              (V := reverseVertex W₂)
                                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                                chartPiece,
                                                density E ≤ Kprior) →
                                                    (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                                      ENNReal.ofReal
                                                        ((Metric.ball
                                                          (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                          (fun u ↦
                                                            (loss (z.1, u)) ^
                                                              (-(t +
                                                                (aoyagiTheorem2RegularVariableCount
                                                                    2 H r : ℝ) /
                                                                  2))) z.2) ∂
                                                      ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                        density).restrict chartPiece).prod ν) <
                                                        ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases
      hsocket hsourceChart' hsourceImageDensity'
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, rawDetChart, p13SourceSet,
          d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres W
            hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hreadback_bridge⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV,
    hsource_inj, hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, ?_⟩
  intro chartPiece hchartPiece_meas hchartPiece_sub_local hchartPiece_sub_image
    Cdet ε hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top density
    Kprior hdensity
  let Ddet : ℝ≥0∞ := Cdet * ε⁻¹
  let Dvol : ℝ≥0∞ := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
  have hpiece_U : chartPiece ⊆ U := fun E hE ↦
    (hchartPiece_sub_local hE).1
  have hpiece_sourceStratum : chartPiece ⊆ sourceStratum := fun E hE ↦
    (hchartPiece_sub_local hE).2
  have hpiece_p13 : chartPiece ⊆ p13SourceSet := fun E hE ↦
    himage_p13V E (hchartPiece_sub_image hE)
  have hright : ∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    constructor
    · rw [hleftV z hzV]
      exact hVW hzV
    · rw [hleftV z hzV]
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Dvol • coordinateSourceMeasure.restrict W := by
    simpa [rawDetChart, d, originalVolume, cHaar, Ddet, Dvol] using
      hreadback_bridge m chartPiece (Cdet := Cdet) (ε := ε)
        hchartPiece_meas hchartPiece_sub_image hdet_dom hCdet
        hsource_lower hε_ne_zero hε_ne_top
  have hDdet : Ddet < ∞ := by
    dsimp [Ddet]
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε_ne_zero))
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hDdet
  simpa [originalVolume, Dvol] using
    hfinite.2 hchartPiece_meas hpiece_U hpiece_sourceStratum
      (by simpa [p13SourceSet] using hpiece_p13)
      (by simpa [sourceChart, readback] using hright)
      (density := density) (Kprior := Kprior) hdensity
      (Csource := Dvol)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.1)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.2)
      hDvol

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This corollary replays the large determinant-domination finite-integral wrapper through dependent lets.
/-- Canonical-chart-piece version of the determinant-domination finite-integral wrapper.

The chart piece is fixed to `(U ∩ sourceStratum) ∩ sourceChart '' V`, the natural
p.13 local piece produced by the source neighborhood and the same-shrink
passive-theta chart image.  The determinant-side domination and source-density
lower bound remain explicit hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      (originalTupleVolumeHaarScalarOfMap d
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W₂ B₂ U₀) m)
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    let chartPiece : Set EdgeFamily := sourceLocal ∩ sourceChart '' V
                    MeasurableSet sourceLocal ∧ MeasurableSet chartPiece ∧
                      ∀ {Cdet ε : ℝ≥0∞},
                        m.restrict rawDetChart ≤
                          Cdet • Measure.map Y (passiveSource.restrict V) →
                          Cdet < ∞ →
                            (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂(originalEdgeFamilyVolume
                                      (V := reverseVertex W₂)
                                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                        chartPiece,
                                        density E ≤ Kprior) →
                                            (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                              ENNReal.ofReal
                                                ((Metric.ball
                                                  (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                  (fun u ↦
                                                    (loss (z.1, u)) ^
                                                      (-(t +
                                                        (aoyagiTheorem2RegularVariableCount
                                                            2 H r : ℝ) /
                                                          2))) z.2) ∂
                                              ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece).prod ν) <
                                                ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases hsocket hsourceChart' hsourceImageDensity'
      (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleft, hsource_inj,
      hsource_contOn, hsource_image, himage_p13, hfinite⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV, hsource_inj,
    hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at ⊢
  have hchartPiece_meas :
      MeasurableSet ((U ∩ sourceStratum) ∩ sourceChart '' V) :=
    by simpa using hfinite.1.inter hsource_image
  refine ⟨by simpa using hfinite.1, hchartPiece_meas, ?_⟩
  intro Cdet ε hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  have hpiece_U : ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ U := fun E hE ↦
    hE.1.1
  have hpiece_sourceStratum :
      ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ sourceStratum := fun E hE ↦
    hE.1.2
  have hpiece_image :
      ((U ∩ sourceStratum) ∩ sourceChart '' V) ⊆ sourceChart '' V := fun E hE ↦
    hE.2
  simpa [EdgeFamily, ρreg, neg_add, add_comm, add_left_comm, add_assoc] using
    hfinite.2 hchartPiece_meas
      hpiece_U hpiece_sourceStratum hpiece_image
      (Cdet := Cdet) (ε := ε) hdet_dom hCdet hsource_lower
      hε_ne_zero hε_ne_top (density := density) (Kprior := Kprior) hdensity

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper replays the canonical determinant theorem and converts an image lower bound to an a.e. bound.
/-- Canonical-chart-piece determinant wrapper using a source-image lower bound.

The source-density lower bound is stated pointwise on the returned image
`sourceChart '' V`; support of `baseJ.restrict V` converts this to the a.e.
lower bound needed by the determinant-domination wrapper. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceImageDensity_image_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      (originalTupleVolumeHaarScalarOfMap d
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W₂ B₂ U₀) m)
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    let chartPiece : Set EdgeFamily := sourceLocal ∩ sourceChart '' V
                    MeasurableSet sourceLocal ∧ MeasurableSet chartPiece ∧
                      ∀ {Cdet ε : ℝ≥0∞},
                        m.restrict rawDetChart ≤
                          Cdet • Measure.map Y (passiveSource.restrict V) →
                          Cdet < ∞ →
                            (∀ E ∈ sourceChart '' V, ε ≤ sourceImageDensity E) →
                              ε ≠ 0 →
                                ε ≠ ∞ →
                                  ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                    (∀ᵐ E ∂(originalEdgeFamilyVolume
                                      (V := reverseVertex W₂)
                                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                        chartPiece,
                                        density E ≤ Kprior) →
                                            (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                              ENNReal.ofReal
                                                ((Metric.ball
                                                  (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                  (fun u ↦
                                                    (loss (z.1, u)) ^
                                                      (-(t +
                                                        (aoyagiTheorem2RegularVariableCount
                                                            2 H r : ℝ) /
                                                          2))) z.2) ∂
                                              ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                density).restrict chartPiece).prod ν) <
                                                ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum rawDetChart p13SourceSet p13SourceChart d
    originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_sourceLocal_inter_sourceChart_image_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases hsocket hsourceChart' hsourceImageDensity'
      (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleft, hsource_inj,
      hsource_contOn, hsource_image, himage_p13, hfinite⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV, hsource_inj,
    hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, hfinite.2.1, ?_⟩
  intro Cdet ε hdet_dom hCdet hsource_image_lower hε_ne_zero hε_ne_top
    density Kprior hdensity
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    simpa [sourceDensity] using
      ae_restrict_comp_lower_of_forall_image_lower
        (μ := baseJ) (V := V) (f := sourceChart)
        (g := sourceImageDensity) (ε := ε)
        hVopen.measurableSet hsource_image_lower
  simpa [EdgeFamily, ρreg, sourceStratum, sourceChart, neg_add,
    add_comm, add_left_comm, add_assoc] using
    hfinite.2.2 hdet_dom hCdet hsource_lower hε_ne_zero hε_ne_top
      (density := density) (Kprior := Kprior) hdensity

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre
