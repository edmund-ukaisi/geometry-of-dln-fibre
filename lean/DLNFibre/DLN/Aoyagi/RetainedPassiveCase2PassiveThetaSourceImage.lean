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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) := by
  intro EdgeFamily sourceChart readback
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let retainedData :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' :=
    fun theta ↦
      case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext theta eNext e
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
  exact ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn, hsource_image⟩

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
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, _hsource_contOn, hsource_image⟩
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
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn, hsource_image⟩
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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre

end
