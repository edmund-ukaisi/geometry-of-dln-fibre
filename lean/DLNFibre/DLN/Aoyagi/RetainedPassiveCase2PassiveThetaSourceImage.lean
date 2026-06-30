import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

/-!
# Case 2 passive theta source-chart image

This file records the source-side image measurability package for the concrete
full `Case2PassiveTheta` coordinate domain.  It complements the endpoint
topology-tuple sector measurability theorem by making the actual fixed-base
p.13 source-chart image `sourceChart '' V` measurable on a local injective
theta sector.

This is only a source-side chart-image prerequisite.  It does not prove
source-rank coverage, source-image equality beyond this local chart image,
source-prior transport, determinant-chart Haar transport, normal crossings,
pole order, or RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open MeasureTheory
open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

set_option linter.style.longLine false in
/-- A pushed-forward restricted measure is supported on the actual image of
the restricting set, provided the map is a.e. measurable and the image is
measurable. -/
theorem measure_map_restrict_image_eq_self_of_aemeasurable
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (f : Θ → E) (m : Measure Θ) (Ω : Set Θ)
    (hΩ : MeasurableSet Ω)
    (himage : MeasurableSet (f '' Ω))
    (hf : AEMeasurable f (m.restrict Ω)) :
    (Measure.map f (m.restrict Ω)).restrict (f '' Ω) =
      Measure.map f (m.restrict Ω) := by
  have hmem : ∀ᵐ theta ∂ m.restrict Ω, f theta ∈ f '' Ω := by
    filter_upwards [ae_restrict_mem hΩ] with theta htheta
    exact ⟨theta, htheta, rfl⟩
  have hmap_mem : ∀ᵐ y ∂ Measure.map f (m.restrict Ω), y ∈ f '' Ω :=
    (ae_map_iff hf himage).2 hmem
  exact Measure.restrict_eq_self_of_ae_mem hmap_mem

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Relative local source-chart image measurability and continuity for the
concrete passive-theta endpoint chart.

Inside any prescribed open theta-neighborhood `G` of a determinant-sector,
nonzero-pivot base point, there is a smaller open `V` on which the endpoint
source-chart readback is a left inverse, the source chart is injective, and
the source chart is continuous with measurable image `sourceChart '' V`.

This is a local chart-image theorem only.  It does not state that source-rank
points are covered by the image, does not identify an original source prior,
and does not provide Haar/Jacobian transport, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          (∀ z ∈ V, readback (sourceChart z) = z) ∧
            Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
              MeasurableSet (sourceChart '' V) := by
  intro EdgeFamily retainedData sourceChart readback
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  obtain ⟨Vread, hVread_open, hz₀Vread, hleft⟩ :=
    (by
      simpa [EdgeFamily, sourceChart, readback, ρ, κ'] using
        exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let D : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    Y ⁻¹' detSet
  have hYcont : Continuous Y := by
    simpa [Y, ρ, κ'] using
      continuous_case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hDopen : IsOpen D :=
    hYcont.isOpen_preimage detSet
      (by
        simpa [detSet, ρ, κ'] using
          isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
  have hz₀D : z₀ ∈ D := by
    have hY₀ :
        Y z₀ ∈ detSet := by
      simpa [Y, detSet, ρ, κ'] using
        case2PassiveThetaEndpointTopologyTuple_mem_detChartSet
          (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
    simpa [D] using hY₀
  let V :
      Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    G ∩ (Vread ∩ D)
  have hVopen : IsOpen V := hGopen.inter (hVread_open.inter hDopen)
  have hz₀V : z₀ ∈ V := ⟨hz₀G, ⟨hz₀Vread, hz₀D⟩⟩
  have hVG : V ⊆ G := Set.inter_subset_left
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          Vread := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz.2.1
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
        hzread_fields
  have hdetV : ∀ z ∈ V, (retainedData z).detChart := by
    intro z hz
    have hzD : z ∈ D := hz.2.2
    have hYz : Y z ∈ detSet := by
      simpa [D] using hzD
    exact
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
        (by simpa [Y, detSet, retainedData, κ'] using hYz)
  have hsource_inj : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    calc
      z = readback (sourceChart z) := (hleftV z hz).symm
      _ = readback (sourceChart z') := by rw [hsrc]
      _ = z' := hleftV z' hz'
  have hretained_cont : Continuous retainedData := by
    simpa [retainedData, ρ, κ'] using
      continuous_case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext eNext e
  have hsource_contOn : ContinuousOn sourceChart V := by
    rw [continuousOn_iff_continuous_restrict]
    let DetData :=
      {data : RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
        data.detChart}
    let toDetData : V → DetData := fun z ↦
      ⟨retainedData z.1, by
        have hzD : z.1 ∈ D := z.2.2.2
        have hYz : Y z.1 ∈ detSet := by
          simpa [D] using hzD
        exact
          (topologyTuple_mem_topologyTupleDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z.1)).1
            (by simpa [Y, detSet] using hYz)⟩
    have htoDetData : Continuous toDetData := by
      have hval : Continuous (fun z : V ↦ retainedData z.1) :=
        hretained_cont.comp continuous_subtype_val
      exact hval.subtype_mk _
    have hsource :
        Continuous
          (fun data : DetData ↦
            paperEndpointFixedBaseRetainedPassiveP13SourceChart W₂ B₂ U₀ hU₀ data) :=
      continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    simpa [sourceChart, case2PassiveThetaEndpointSourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData,
      toDetData, retainedData, DetData, ρ, κ'] using
      hsource.comp htoDetData
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hsource_image : MeasurableSet (sourceChart '' V) :=
    hVmeas.image_of_continuousOn_injOn hsource_contOn hsource_inj
  exact
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Relative local source-chart image measurability for the concrete
passive-theta endpoint chart.

Inside any prescribed open theta-neighborhood `G` of a determinant-sector,
nonzero-pivot base point, there is a smaller open `V` on which the endpoint
source-chart readback is a left inverse, the source chart is injective, and
the source-side image `sourceChart '' V` is measurable.

This is a local chart-image theorem only.  It does not state that source-rank
points are covered by the image, does not identify an original source prior,
and does not provide Haar/Jacobian transport, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ MeasurableSet (sourceChart '' V) := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, _hdetV, hleftV, hsource_inj, _hsource_contOn,
      hsource_image⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  exact ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj, hsource_image⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On the local measurable source-chart image, the readback is a right
inverse to the source chart.

This is a two-sided inverse package only for the already produced local image
`sourceChart '' V`.  It does not assert that this image covers a source-rank
stratum, identify a source prior, or provide Haar/Jacobian transport, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_rightInverse
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ MeasurableSet (sourceChart '' V) ∧
            ∀ E ∈ sourceChart '' V,
              readback E ∈ V ∧ sourceChart (readback E) = E := by
  intro EdgeFamily sourceChart readback
  rcases
      exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_image⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z hz
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  have hright : ∀ E ∈ sourceChart '' V,
      readback E ∈ V ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    constructor
    · simpa [hleftV' z hzV] using hzV
    · rw [hleftV' z hzV]
  exact ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_image', hright⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Relative local source-chart image support for pushed-forward theta-domain
measures.

After shrinking inside any prescribed open theta-neighborhood `G`, every
pushforward `Measure.map sourceChart (thetaMeasure.restrict V)` is supported
on the actual measurable image `sourceChart '' V`.

This is image-support bookkeeping only.  It does not prove source-rank
coverage, equality with a larger source image, original source-prior transport,
Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_restrict_image_eq_self_readback_leftInverse
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ MeasurableSet (sourceChart '' V) ∧
            ∀ thetaMeasure :
              Measure
                (Case2PassiveTheta
                  (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              let μ := Measure.map sourceChart (thetaMeasure.restrict V)
              μ.restrict (sourceChart '' V) = μ := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, _hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  refine ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj, hsource_image, ?_⟩
  intro thetaMeasure μ
  have hsource_aemeas : AEMeasurable sourceChart (thetaMeasure.restrict V) :=
    ContinuousOn.aemeasurable hsource_contOn hVopen.measurableSet
  simpa [μ] using
    measure_map_restrict_image_eq_self_of_aemeasurable
      sourceChart thetaMeasure V hVopen.measurableSet hsource_image hsource_aemeas

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A concrete passive-theta endpoint source-chart point lies in the named
source-rank stratum under the explicit product-rank and successor-rank
equations.

This is pointwise one-way source-stratum membership for a chart-produced
point.  It does not prove source-rank coverage, exact-rank openness,
source-image equality, source-prior transport, Haar/Jacobian transport,
normal crossings, pole order, or RLCT extraction. -/
theorem case2PassiveThetaEndpointSourceChart_mem_sourceRankStratum
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
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hdet :
      (case2PassiveThetaEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e).detChart)
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0)
    (hr1 :
      r + (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank =
        rEdge 1) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    case2PassiveThetaEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e theta ∈
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂
        (fun E : EdgeFamily ↦ E) r rEdge := by
  intro EdgeFamily
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let rawData :
      RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
    case2PassiveThetaRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext
  let data :
      RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' :=
    case2PassiveThetaEndpointRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext e
  have hC0raw : (rawData.C (0 : Fin 2)).rank = Fintype.card τ := by
    simpa [rawData, case2PassiveThetaRetainedData,
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
      case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceCprime] using
      rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext) eNext
  have hC1raw :
      (rawData.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank := by
    simpa [rawData, case2PassiveThetaRetainedData,
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
      case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceResidual] using
      rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext) eNext
  have hC0 : (data.C (0 : Fin 2)).rank = Fintype.card τ := by
    calc
      (data.C (0 : Fin 2)).rank = (rawData.C (0 : Fin 2)).rank := by
        simpa [data, rawData, case2PassiveThetaEndpointRetainedData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := ρ) e rawData (0 : Fin 2)
      _ = Fintype.card τ := hC0raw
  have hC1 :
      (data.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank := by
    calc
      (data.C (1 : Fin 2)).rank = (rawData.C (1 : Fin 2)).rank := by
        simpa [data, rawData, case2PassiveThetaEndpointRetainedData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := ρ) e rawData (1 : Fin 2)
      _ = (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank := hC1raw
  have hmem :
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ data ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E)
          r rEdge := by
    refine
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq
        (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) data
        (by simpa [data, ρ, κ'] using hdet) hprod ?_
    intro p
    fin_cases p
    · calc
        r + (data.C (0 : Fin 2)).rank = r + Fintype.card τ := by rw [hC0]
        _ = rEdge 0 := hr0
    · calc
        r + (data.C (1 : Fin 2)).rank =
            r + (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank := by
          rw [hC1]
        _ = rEdge 1 := hr1
  simpa [case2PassiveThetaEndpointSourceChart, data, EdgeFamily, ρ, κ'] using hmem

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The local passive-theta source-chart image is contained in the named
source-rank stratum under an explicit successor-rank hypothesis on the chosen
local theta domain.

This is one-way support for chart-produced source points.  It does not prove
source-rank coverage, source-image equality with a stratum, source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_sourceRankStratum
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          (∀ z ∈ V, readback (sourceChart z) = z) ∧
            Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
              MeasurableSet (sourceChart '' V) ∧
                (∀ z ∈ V,
                  r + (case2SuccessorSelectedEntryMatrix
                    n hS hnext z.yNext eNext).rank = rEdge 1 →
                  sourceChart z ∈ sourceStratum) ∧
                  ((∀ z ∈ V,
                    r + (case2SuccessorSelectedEntryMatrix
                      n hS hnext z.yNext eNext).rank = rEdge 1) →
                    ∀ E ∈ sourceChart '' V, E ∈ sourceStratum) := by
  intro EdgeFamily retainedData sourceChart readback sourceStratum
  rcases
      (by
        simpa [EdgeFamily, retainedData, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  have hdetV' : ∀ z ∈ V, (retainedData z).detChart := by
    intro z hz
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈ V := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [retainedData, Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hdetV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz_fields
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈ V := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz_fields
  have hpoint : ∀ z ∈ V,
      r + (case2SuccessorSelectedEntryMatrix n hS hnext z.yNext eNext).rank =
        rEdge 1 →
      sourceChart z ∈ sourceStratum := by
    intro z hzV hzrank
    simpa [sourceChart, sourceStratum, retainedData] using
      case2PassiveThetaEndpointSourceChart_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z (hdetV' z hzV) hprod hr0 hzrank
  have himage_subset :
      (∀ z ∈ V,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext z.yNext eNext).rank =
          rEdge 1) →
        ∀ E ∈ sourceChart '' V, E ∈ sourceStratum := by
    intro hsucc E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hpoint z hzV (hsucc z hzV)
  exact
    ⟨V, hVopen, hz₀V, hVG, hdetV', hleftV', hsource_inj, hsource_contOn,
      hsource_image, hpoint, himage_subset⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A pushed-forward passive-theta source-chart measure is supported on the
named source-rank stratum under an a.e. successor-rank hypothesis on the
restricted theta domain.

This is one-way source-rank support for chart-produced measures.  It does not
prove source-rank coverage, source-image equality with a stratum, source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_restrict_sourceRankStratum_eq_self
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          (∀ z ∈ V, readback (sourceChart z) = z) ∧
            Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
              MeasurableSet (sourceChart '' V) ∧
                (∀ z ∈ V,
                  r + (case2SuccessorSelectedEntryMatrix
                    n hS hnext z.yNext eNext).rank = rEdge 1 →
                  sourceChart z ∈ sourceStratum) ∧
                  ∀ thetaMeasure :
                    Measure
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                    (∀ᵐ z ∂ thetaMeasure.restrict V,
                      r + (case2SuccessorSelectedEntryMatrix
                        n hS hnext z.yNext eNext).rank = rEdge 1) →
                    let μ := Measure.map sourceChart (thetaMeasure.restrict V)
                    μ.restrict sourceStratum = μ := by
  intro EdgeFamily retainedData sourceChart readback sourceStratum
  rcases
      exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G hprod hr0 with
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image, hpoint, _himage_subset⟩
  refine
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image, hpoint, ?_⟩
  intro thetaMeasure hrank_ae μ
  have hsource_aemeas : AEMeasurable sourceChart (thetaMeasure.restrict V) :=
    ContinuousOn.aemeasurable hsource_contOn hVopen.measurableSet
  have hchart_mem :
      ∀ᵐ z ∂ thetaMeasure.restrict V, sourceChart z ∈ sourceStratum := by
    filter_upwards [hrank_ae, ae_restrict_mem hVopen.measurableSet] with z hzrank hzV
    exact hpoint z hzV hzrank
  simpa [μ, sourceStratum] using
    measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
      (W := W₂) (B := B₂)
      (Cedge := fun E : EdgeFamily ↦ E) (r := r) (rEdge := rEdge)
      (η := thetaMeasure.restrict V) (sourceChart := sourceChart)
      (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      hsource_aemeas hchart_mem

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre

end
