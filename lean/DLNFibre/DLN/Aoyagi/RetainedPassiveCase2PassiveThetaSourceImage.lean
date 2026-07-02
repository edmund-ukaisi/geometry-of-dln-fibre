import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RegularSuspensionSourceReadback
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

set_option linter.style.longLine false in
/-- If `sourceChart` is a right inverse to `readback` on a measurable image
set, then pushing the restricted external measure through `readback` and back
through `sourceChart` recovers that restricted external measure.

This is pure measure bookkeeping for a chosen measurable chart image.  It does
not assert that an original prior is supported in the image, prove any density
comparison, or provide Haar transport, normal crossings, pole order, or RLCT
extraction. -/
theorem measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (imageSet : Set E)
    (himage : MeasurableSet imageSet)
    (hreadback : AEMeasurable readback (externalMeasure.restrict imageSet))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.map readback (externalMeasure.restrict imageSet)))
    (hright : ∀ E ∈ imageSet, sourceChart (readback E) = E) :
    Measure.map sourceChart
        (Measure.map readback (externalMeasure.restrict imageSet)) =
      externalMeasure.restrict imageSet := by
  calc
    Measure.map sourceChart
        (Measure.map readback (externalMeasure.restrict imageSet)) =
        Measure.map (fun E ↦ sourceChart (readback E))
          (externalMeasure.restrict imageSet) := by
          exact AEMeasurable.map_map_of_aemeasurable hsourceChart hreadback
    _ = Measure.map id (externalMeasure.restrict imageSet) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem himage] with E hE
      exact hright E hE
    _ = externalMeasure.restrict imageSet := by
      rw [Measure.map_id]

set_option linter.style.longLine false in
/-- The pullback of a measure restricted to a chart image is supported on the
coordinate set if the readback sends every image point into that set. -/
theorem measure_map_readback_restrict_image_restrict_eq_self_of_aemeasurable
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (readback : E → Θ)
    (externalMeasure : Measure E) (imageSet : Set E) (V : Set Θ)
    (himage : MeasurableSet imageSet)
    (hV : MeasurableSet V)
    (hreadback : AEMeasurable readback (externalMeasure.restrict imageSet))
    (hmem : ∀ E ∈ imageSet, readback E ∈ V) :
    (Measure.map readback (externalMeasure.restrict imageSet)).restrict V =
      Measure.map readback (externalMeasure.restrict imageSet) := by
  have hpre : ∀ᵐ E ∂ externalMeasure.restrict imageSet, readback E ∈ V := by
    filter_upwards [ae_restrict_mem himage] with E hE
    exact hmem E hE
  have hmap : ∀ᵐ theta ∂ Measure.map readback (externalMeasure.restrict imageSet),
      theta ∈ V :=
    (ae_map_iff hreadback hV).2 hpre
  exact Measure.restrict_eq_self_of_ae_mem hmap

set_option linter.style.longLine false in
/-- A map continuous on a measurable carrier is a.e. measurable for any
measure supported on that carrier. -/
theorem aemeasurable_of_continuousOn_of_measure_restrict_eq_self
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [OpensMeasurableSpace Θ] [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    {sourceChart : Θ → E} {μ : Measure Θ} {V : Set Θ}
    (hcont : ContinuousOn sourceChart V)
    (hV : MeasurableSet V)
    (hsupport : μ.restrict V = μ) :
    AEMeasurable sourceChart μ := by
  have hsource_restrict : AEMeasurable sourceChart (μ.restrict V) :=
    hcont.aemeasurable hV
  have hac : μ ≪ μ.restrict V := by
    rw [hsupport]
  exact hsource_restrict.mono_ac hac

set_option linter.style.longLine false in
/-- On a Polish measurable coordinate domain, a continuous injective local
source chart with a pointwise readback left inverse makes the readback
a.e.-measurable for the chart-produced source-image measure.

This is only inverse-measurability bookkeeping for the actual local image.  It
does not identify an external source prior, prove source-rank coverage, or
provide Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (thetaReference : Measure Θ) (V : Set Θ)
    (hV : MeasurableSet V)
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta) :
    AEMeasurable readback
      (Measure.map sourceChart (thetaReference.restrict V)) := by
  let sourceChartV : V → E := V.restrict sourceChart
  let thetaReferenceV : Measure V :=
    Measure.comap ((↑) : V → Θ) thetaReference
  have hsource_emb : MeasurableEmbedding sourceChartV :=
    hsource_contOn.measurableEmbedding hV hsource_inj
  have hcomp :
      AEMeasurable (readback ∘ sourceChartV) thetaReferenceV := by
    have hval : Measurable ((↑) : V → Θ) := measurable_subtype_coe
    have heq : readback ∘ sourceChartV = ((↑) : V → Θ) := by
      funext theta
      exact hleft theta.1 theta.2
    rw [heq]
    exact hval.aemeasurable
  have hreadbackV :
      AEMeasurable readback (Measure.map sourceChartV thetaReferenceV) :=
    (hsource_emb.aemeasurable_map_iff).2 hcomp
  have hval :
      AEMeasurable ((↑) : V → Θ) thetaReferenceV :=
    measurable_subtype_coe.aemeasurable
  have hsource :
      AEMeasurable sourceChart
        (Measure.map ((↑) : V → Θ) thetaReferenceV) := by
    rw [map_comap_subtype_coe hV]
    exact hsource_contOn.aemeasurable hV
  have hmap_eq :
      Measure.map sourceChartV thetaReferenceV =
        Measure.map sourceChart (thetaReference.restrict V) := by
    calc
      Measure.map sourceChartV thetaReferenceV =
          Measure.map (sourceChart ∘ ((↑) : V → Θ)) thetaReferenceV := by
            rfl
      _ = Measure.map sourceChart (Measure.map ((↑) : V → Θ) thetaReferenceV) := by
            exact (AEMeasurable.map_map_of_aemeasurable hsource hval).symm
      _ = Measure.map sourceChart (thetaReference.restrict V) := by
            rw [map_comap_subtype_coe hV]
  simpa [hmap_eq] using hreadbackV

set_option linter.style.longLine false in
/-- Conditional domination handoff from a pulled-back external image measure to
the source image.

If the portion of an external source measure on a measurable chart image is
pulled back by `readback`, and that pulled-back measure is dominated by a
theta-domain reference measure on `V`, then the restricted external source
measure is dominated by the source-chart pushforward of the reference measure.

This theorem assumes the domination; it does not prove source-prior density
comparison, source-image coverage, Haar transport, normal crossings, pole
order, or RLCT extraction. -/
theorem measure_restrict_image_le_smul_map_of_map_readback_restrict_image_le_smul
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [OpensMeasurableSpace Θ] [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (c : ENNReal)
    (hV : MeasurableSet V)
    (himage : MeasurableSet (sourceChart '' V))
    (hsource_contOn : ContinuousOn sourceChart V)
    (hreadback : AEMeasurable readback (externalMeasure.restrict (sourceChart '' V)))
    (hright : ∀ E ∈ sourceChart '' V, readback E ∈ V ∧ sourceChart (readback E) = E)
    (hdom :
      Measure.map readback (externalMeasure.restrict (sourceChart '' V)) ≤
        c • thetaReference.restrict V) :
    externalMeasure.restrict (sourceChart '' V) ≤
      c • Measure.map sourceChart (thetaReference.restrict V) := by
  let candidateMeasure : Measure Θ :=
    Measure.map readback (externalMeasure.restrict (sourceChart '' V))
  have hsupport : candidateMeasure.restrict V = candidateMeasure :=
    measure_map_readback_restrict_image_restrict_eq_self_of_aemeasurable
      readback externalMeasure (sourceChart '' V) V himage hV hreadback
      (fun E hE ↦ (hright E hE).1)
  have hsource_candidate :
      AEMeasurable sourceChart candidateMeasure :=
    aemeasurable_of_continuousOn_of_measure_restrict_eq_self
      hsource_contOn hV hsupport
  have hmap :
      Measure.map sourceChart candidateMeasure =
        externalMeasure.restrict (sourceChart '' V) :=
    measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
      sourceChart readback externalMeasure (sourceChart '' V) himage hreadback
      hsource_candidate (fun E hE ↦ (hright E hE).2)
  have hsource_ref :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hpush :
      Measure.map sourceChart candidateMeasure ≤
        c • Measure.map sourceChart (thetaReference.restrict V) :=
    map_le_smul_map_of_le_smul_aemeasurable hsource_ref hdom
  simpa [candidateMeasure, hmap] using hpush

set_option linter.style.longLine false in
/-- If the readback of a measurable source-side piece is dominated by a
coordinate-side reference measure and the source chart is a right inverse to
the readback on that piece, then the source-side piece is dominated by the
chart-produced reference measure restricted to any larger local source set.

This is a chart-piece version of
`measure_restrict_image_le_smul_map_of_map_readback_restrict_image_le_smul`.
It assumes the readback domination and the pointwise right-inverse property on
the chosen piece.  It does not prove original-prior transport, source-image
coverage, Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem measure_restrict_piece_le_smul_map_restrict_of_map_readback_restrict_piece_le_smul
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (chartPiece sourceLocal : Set E) (c : ENNReal)
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub : chartPiece ⊆ sourceLocal)
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback : AEMeasurable readback (externalMeasure.restrict chartPiece))
    (hright : ∀ E ∈ chartPiece, sourceChart (readback E) = E)
    (hdom :
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        c • thetaReference.restrict V) :
    externalMeasure.restrict chartPiece ≤
      c • (Measure.map sourceChart (thetaReference.restrict V)).restrict sourceLocal := by
  let candidateMeasure : Measure Θ :=
    Measure.map readback (externalMeasure.restrict chartPiece)
  have hcandidate_ac :
      candidateMeasure ≪ thetaReference.restrict V :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hsource_candidate :
      AEMeasurable sourceChart candidateMeasure :=
    hsource.mono_ac hcandidate_ac
  have hmap :
      Measure.map sourceChart candidateMeasure =
        externalMeasure.restrict chartPiece :=
    measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
      sourceChart readback externalMeasure chartPiece hchartPiece hreadback
      hsource_candidate hright
  have hpush :
      externalMeasure.restrict chartPiece ≤
        c • Measure.map sourceChart (thetaReference.restrict V) := by
    have hpush' :
        Measure.map sourceChart candidateMeasure ≤
          c • Measure.map sourceChart (thetaReference.restrict V) :=
      map_le_smul_map_of_le_smul_aemeasurable hsource hdom
    simpa [candidateMeasure, hmap] using hpush'
  exact
    restrict_le_smul_restrict_of_le_smul_of_subset
      (μ := externalMeasure) (η := Measure.map sourceChart (thetaReference.restrict V))
      (s := chartPiece) (t := sourceLocal) (c := c)
      hchartPiece hchartPiece_sub hpush

set_option linter.style.longLine false in
/-- Pulling back the chart-produced source-image reference measure by the
readback recovers the theta-domain reference measure on `V`.

This is only the exact inverse statement for the already produced chart image.
It does not identify an external or original source prior, prove a density
comparison, or provide Haar transport, normal crossings, pole order, or RLCT
extraction. -/
theorem measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (thetaReference : Measure Θ) (V : Set Θ)
    (hV : MeasurableSet V)
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)))
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta) :
    Measure.map readback
        (Measure.map sourceChart (thetaReference.restrict V)) =
      thetaReference.restrict V := by
  calc
    Measure.map readback
        (Measure.map sourceChart (thetaReference.restrict V)) =
        Measure.map (fun theta ↦ readback (sourceChart theta))
          (thetaReference.restrict V) := by
          exact AEMeasurable.map_map_of_aemeasurable hreadback hsource
    _ = Measure.map id (thetaReference.restrict V) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hV] with theta htheta
      exact hleft theta htheta
    _ = thetaReference.restrict V := by
      rw [Measure.map_id]

set_option linter.style.longLine false in
/-- A bounded source-image density pulls back to theta-domain scalar
domination.

If the source-image measure is a bounded-density perturbation of the
chart-produced source-image reference measure
`Measure.map sourceChart (thetaReference.restrict V)`, then its readback
pullback is dominated by the same scalar multiple of `thetaReference.restrict
V`.

This is the honest density-comparison socket for an external/source prior: the
bounded-density hypothesis is assumed explicitly.  The theorem does not prove
that an original prior has this density, does not prove source-image coverage
or Haar transport, and does not extract normal crossings, pole order, or
RLCT. -/
theorem measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (thetaReference : Measure Θ) (V : Set Θ)
    (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (himage : MeasurableSet (sourceChart '' V))
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)))
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          (sourceChart '' V),
        density E ≤ c) :
    Measure.map readback
        (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          (sourceChart '' V)) ≤
      c • thetaReference.restrict V := by
  let sourceBase : Measure E :=
    Measure.map sourceChart (thetaReference.restrict V)
  have hsource_dom :
      (sourceBase.withDensity density).restrict (sourceChart '' V) ≤
        c • sourceBase := by
    exact restrict_withDensity_le_smul_of_ae_le (μ := sourceBase)
      (s := sourceChart '' V) (f := density) (c := c) himage hdensity_le
  have hpush :
      Measure.map readback
          ((sourceBase.withDensity density).restrict (sourceChart '' V)) ≤
        c • Measure.map readback sourceBase :=
    map_le_smul_map_of_le_smul_aemeasurable
      (μ := sourceBase)
      (ν := (sourceBase.withDensity density).restrict (sourceChart '' V))
      (c := c) hreadback hsource_dom
  have hbase_pull :
      Measure.map readback sourceBase = thetaReference.restrict V := by
    simpa [sourceBase] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hV hsource hreadback hleft
  simpa [sourceBase, hbase_pull] using hpush

set_option linter.style.longLine false in
/-- A bounded source-image density pulls back to theta-domain scalar
domination, with readback a.e. measurability discharged from a continuous
injective local source chart and its pointwise left inverse.

This is the same bounded-density socket as
`measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le`, but the
readback measurability hypothesis is derived from Lusin-Souslin-style
measurable embedding infrastructure.  It still does not identify an external
or original source prior, prove source-image coverage or Haar transport, or
extract normal crossings, pole order, or RLCT. -/
theorem measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le_of_continuousOn_injOn
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (thetaReference : Measure Θ) (V : Set Θ)
    (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (himage : MeasurableSet (sourceChart '' V))
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          (sourceChart '' V),
        density E ≤ c) :
    Measure.map readback
        (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          (sourceChart '' V)) ≤
      c • thetaReference.restrict V := by
  have hsource :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)) :=
    aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
      sourceChart readback thetaReference V hV hsource_contOn hsource_inj hleft
  exact
    measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
      sourceChart readback thetaReference V density c hV himage hsource hreadback
      hleft hdensity_le

set_option linter.style.longLine false in
/-- If an external source-image measure is identified as a bounded-density
perturbation of the chart-produced source-image reference, then its readback
pullback is dominated on theta coordinates.

The density identity and boundedness are explicit hypotheses.  This theorem
does not prove that an original prior satisfies those hypotheses, nor does it
prove source-image coverage, Haar transport, normal crossings, pole order, or
RLCT extraction. -/
theorem measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (himage : MeasurableSet (sourceChart '' V))
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)))
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict (sourceChart '' V) =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          (sourceChart '' V))
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          (sourceChart '' V),
        density E ≤ c) :
    Measure.map readback
        (externalMeasure.restrict (sourceChart '' V)) ≤
      c • thetaReference.restrict V := by
  calc
    Measure.map readback
        (externalMeasure.restrict (sourceChart '' V)) =
        Measure.map readback
          (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
            (sourceChart '' V)) := by
          rw [heq]
    _ ≤ c • thetaReference.restrict V :=
      measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
        sourceChart readback thetaReference V density c hV himage hsource
        hreadback hleft hdensity_le

set_option linter.style.longLine false in
/-- External source-image bounded-density domination, with readback
a.e. measurability discharged from a continuous injective local chart.

This is the external-measure equality version of
`measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le_of_continuousOn_injOn`.
It is generic in the coordinate domain, so the domain may later be the full
p.13 product-coordinate space `(theta,u)`, not only a passive-theta space.

The theorem still assumes the restricted external measure is identified with a
bounded-density perturbation of the chart-produced source-image reference.
It does not prove original-prior transport, source-image coverage, Haar
transport, normal crossings, pole order, or RLCT extraction. -/
theorem measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (himage : MeasurableSet (sourceChart '' V))
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict (sourceChart '' V) =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          (sourceChart '' V))
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          (sourceChart '' V),
        density E ≤ c) :
    Measure.map readback
        (externalMeasure.restrict (sourceChart '' V)) ≤
      c • thetaReference.restrict V := by
  have hsource :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)) :=
    aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
      sourceChart readback thetaReference V hV hsource_contOn hsource_inj hleft
  exact
    measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity
      sourceChart readback externalMeasure thetaReference V density c hV himage
      hsource hreadback hleft heq hdensity_le

set_option linter.style.longLine false in
/-- If an external measure restricted to a measurable chart piece is identified
as a bounded-density perturbation of the chart-produced source-image reference,
then its readback pullback is dominated on theta coordinates.

This is the chart-piece version of
`measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity`.  It
is useful for Aoyagi chart-piece sockets, where the source-side integration
piece is usually a measurable subset of the actual local image rather than the
whole image.  The theorem does not prove that the external measure satisfies
the density identity or bound, does not prove image coverage, and does not
provide Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (chartPiece : Set E) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (hchartPiece : MeasurableSet chartPiece)
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)))
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict chartPiece =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          chartPiece)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
        density E ≤ c) :
    Measure.map readback (externalMeasure.restrict chartPiece) ≤
      c • thetaReference.restrict V := by
  let sourceBase : Measure E :=
    Measure.map sourceChart (thetaReference.restrict V)
  have hsource_dom :
      (sourceBase.withDensity density).restrict chartPiece ≤ c • sourceBase := by
    exact restrict_withDensity_le_smul_of_ae_le (μ := sourceBase)
      (s := chartPiece) (f := density) (c := c) hchartPiece
      (by simpa [sourceBase] using hdensity_le)
  have hpush :
      Measure.map readback ((sourceBase.withDensity density).restrict chartPiece) ≤
        c • Measure.map readback sourceBase := by
    exact map_le_smul_map_of_le_smul_aemeasurable
      (μ := sourceBase) (ν := (sourceBase.withDensity density).restrict chartPiece)
      (c := c) hreadback hsource_dom
  have hbase_pull :
      Measure.map readback sourceBase = thetaReference.restrict V := by
    simpa [sourceBase] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hV hsource hreadback hleft
  calc
    Measure.map readback (externalMeasure.restrict chartPiece) =
        Measure.map readback ((sourceBase.withDensity density).restrict chartPiece) := by
          rw [heq]
    _ ≤ c • Measure.map readback sourceBase := hpush
    _ = c • thetaReference.restrict V := by rw [hbase_pull]

set_option linter.style.longLine false in
/-- Chart-piece bounded-density readback domination, with readback
a.e. measurability discharged from a continuous injective local source chart.

This is the chart-piece version of
`measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn`.
It still assumes the restricted external measure is identified with a
bounded-density perturbation of the chart-produced source-image reference.
It does not prove original-prior transport, source-image coverage, Haar
transport, normal crossings, pole order, or RLCT extraction. -/
theorem measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V : Set Θ) (chartPiece : Set E) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (hchartPiece : MeasurableSet chartPiece)
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict chartPiece =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          chartPiece)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
        density E ≤ c) :
    Measure.map readback (externalMeasure.restrict chartPiece) ≤
      c • thetaReference.restrict V := by
  have hsource :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)) :=
    aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
      sourceChart readback thetaReference V hV hsource_contOn hsource_inj hleft
  exact
    measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity
      sourceChart readback externalMeasure thetaReference V chartPiece density c
      hV hchartPiece hsource hreadback hleft heq hdensity_le

set_option linter.style.longLine false in
/-- A chart-piece bounded-density identity gives both readback
a.e. measurability and readback domination by a larger theta-reference
restriction.

This extends
`measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity` from
`thetaReference.restrict V` to `thetaReference.restrict W` when `V ⊆ W`.  The
a.e. measurability conclusion follows because the restricted external piece is
absolutely continuous with respect to the chart-produced source-image reference.
The theorem does not prove the density identity or bound, image coverage, Haar
transport, normal crossings, pole order, or RLCT extraction. -/
theorem aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V W : Set Θ) (chartPiece : Set E) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (hchartPiece : MeasurableSet chartPiece)
    (hVW : V ⊆ W)
    (hsource : AEMeasurable sourceChart (thetaReference.restrict V))
    (hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)))
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict chartPiece =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          chartPiece)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
        density E ≤ c) :
    AEMeasurable readback (externalMeasure.restrict chartPiece) ∧
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        c • thetaReference.restrict W := by
  let sourceBase : Measure E :=
    Measure.map sourceChart (thetaReference.restrict V)
  have hsource_dom :
      (sourceBase.withDensity density).restrict chartPiece ≤ c • sourceBase := by
    exact restrict_withDensity_le_smul_of_ae_le (μ := sourceBase)
      (s := chartPiece) (f := density) (c := c) hchartPiece
      (by simpa [sourceBase] using hdensity_le)
  have hpiece_ac : externalMeasure.restrict chartPiece ≪ sourceBase := by
    rw [heq]
    exact Measure.absolutelyContinuous_of_le_smul hsource_dom
  have hreadback_piece :
      AEMeasurable readback (externalMeasure.restrict chartPiece) :=
    hreadback.mono_ac hpiece_ac
  have hpullV :
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        c • thetaReference.restrict V :=
    measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity
      sourceChart readback externalMeasure thetaReference V chartPiece density c
      hV hchartPiece hsource hreadback hleft heq hdensity_le
  have hrestrict : thetaReference.restrict V ≤ thetaReference.restrict W :=
    Measure.restrict_mono hVW le_rfl
  have hscale : c • thetaReference.restrict V ≤ c • thetaReference.restrict W := by
    exact Measure.le_iff.2 fun s _hs ↦ by
      rw [Measure.smul_apply, Measure.smul_apply]
      exact mul_le_mul_right (hrestrict s) c
  exact ⟨hreadback_piece, hpullV.trans hscale⟩

set_option linter.style.longLine false in
/-- A chart-piece bounded-density identity gives readback a.e. measurability
and readback domination by a larger theta-reference restriction, with readback
a.e. measurability over the chart-produced source-image reference generated
from a continuous injective local chart.

This is the `V ⊆ W` version of
`measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn`.
It still assumes the bounded-density identity and bound. -/
theorem aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (externalMeasure : Measure E) (thetaReference : Measure Θ)
    (V W : Set Θ) (chartPiece : Set E) (density : E → ENNReal) (c : ENNReal)
    (hV : MeasurableSet V)
    (hchartPiece : MeasurableSet chartPiece)
    (hVW : V ⊆ W)
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (heq :
      externalMeasure.restrict chartPiece =
        ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
          chartPiece)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
        density E ≤ c) :
    AEMeasurable readback (externalMeasure.restrict chartPiece) ∧
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        c • thetaReference.restrict W := by
  have hsource :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)) :=
    aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
      sourceChart readback thetaReference V hV hsource_contOn hsource_inj hleft
  exact
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity
      sourceChart readback externalMeasure thetaReference V W chartPiece density c
      hV hchartPiece hVW hsource hreadback hleft heq hdensity_le

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Case 2 specialization of the p.13 source-dependent product-coordinate
readout.

For the full product chart built from the passive-theta endpoint source chart,
the p.13 regular-coordinate readout is the supplied Euclidean vector `u`, and
the residual-coordinate readout is the residual readout of the underlying
passive-theta source chart at `theta`.

This names the full `(theta,u)` chart input.  It is only a coordinate readout:
it does not construct a full inverse to `(theta,u)`, identify an original
prior, prove source-image coverage, Haar transport, normal crossings, pole
order, or RLCT extraction. -/
theorem case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
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
    (u :
      EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let productSourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
          EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) →
          EdgeFamily :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ sourceChart
    (paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
          fun c ↦ u c) ∧
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta := by
  intro EdgeFamily sourceChart productSourceChart
  simpa [EdgeFamily, sourceChart, productSourceChart] using
    paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
      (M := 0) (V := W₂) (Bv := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := sourceChart) (x := theta) (u := u) hCtop

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Read back only the p.13 regular Euclidean block from an edge family. -/
def case2PassiveThetaEndpointProductSourceChartRegularReadback
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) :=
  fun X ↦
    (EuclideanSpace.equiv
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) ℝ).symm
      (paperEndpointFixedBaseRegularBlockCoordinateMap
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E) X)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The regular-block readback recovers the supplied p.13 regular variable. -/
theorem case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
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
    (u :
      EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let Coord :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let productSourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
          EuclideanSpace ℝ Coord →
          EdgeFamily :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ sourceChart
    case2PassiveThetaEndpointProductSourceChartRegularReadback W₂ B₂ hU₀
      (productSourceChart (theta, u)) = u := by
  intro Coord EdgeFamily sourceChart productSourceChart
  have hchart :
      paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
        fun c ↦ u c := by
    simpa [EdgeFamily, sourceChart, productSourceChart] using
      (case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta u hCtop).1
  have hregular :
      paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E) (productSourceChart (theta, u)) =
        fun c ↦ u c := by
    exact
      (paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ rfl).trans hchart
  rw [case2PassiveThetaEndpointProductSourceChartRegularReadback]
  change
    (EuclideanSpace.equiv Coord ℝ).symm
        (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E) (productSourceChart (theta, u))) = u
  rw [hregular]
  exact ContinuousLinearEquiv.symm_apply_apply (EuclideanSpace.equiv Coord ℝ) u

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The p.13 product source chart preserves the selected residual inverse
readout of the underlying passive-theta source chart. -/
theorem case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
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
    (u :
      EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let Coord :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let productSourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
          EuclideanSpace ℝ Coord →
          EdgeFamily :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ sourceChart
    case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
        (productSourceChart (theta, u)) =
      case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
        (sourceChart theta) := by
  intro Coord EdgeFamily sourceChart productSourceChart
  have hresidual :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta := by
    simpa [EdgeFamily, sourceChart, productSourceChart] using
      (case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta u hCtop).2
  have hprod_id :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E) (productSourceChart (theta, u)) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) := by
    exact
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ rfl
  have hbase_id :
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E) (sourceChart theta) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta := by
    exact
      paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ rfl
  rw [case2PassiveThetaEndpointInverseReadout]
  apply congrArg
    (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
      (case2PassiveThetaPivotNext n hS hnext))
  funext i
  exact congrFun (hprod_id.trans (hresidual.trans hbase_id.symm))
    ((case2PassiveThetaEndpointResidualCoordEquiv W₂ B₂ n eNext e).symm i)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-readback fields of the Case 2 endpoint p.13 product source chart.

This is the concrete fixed-base instantiation of the raw p.13 product-coordinate
source-readback formula.  The product chart keeps the regular fields decoded
from `u` and the residual factors extracted from the passive-theta base source
family, while the retained passive fields read back as the canonical values
`A1passive = 1` and `A3passive = 0`.

This is only pointwise finite block algebra.  It is not a full inverse theorem
for `(theta,u)`, source-prior transport, source-image coverage, Haar transport,
normal crossings, pole order, or RLCT extraction. -/
theorem case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields
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
    (u :
      EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ := throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let Coord :=
      AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let productSourceChart :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
          EuclideanSpace ℝ Coord →
          EdgeFamily :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ sourceChart
    let Ebase : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p ↦
          (sourceChart theta p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let Eprod : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p ↦
          (productSourceChart (theta, u) p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
    let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
    let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
    let C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ :=
      fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last 2) p p.succ.le_last
    let data := sourceReadback (K := ℝ) (ρ := ρ) (M := 1) (κ' := κ) Eprod
    data.A1passive = (fun _ : Fin 1 ↦ 1) ∧
      data.F2 = Fin.cases F2 (fun _ : Fin 1 ↦ 0) ∧
      data.A3passive = (fun _ : Fin 1 ↦ 0) ∧
      data.C = C ∧
      data.Ctop = Ctop ∧
      data.F3 = F3 := by
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart Ebase Eprod F2 F3 Ctop C data
  simpa [ρ, κ, Coord, sourceChart, productSourceChart, Ebase, Eprod, F2, F3,
    Ctop, C, data] using
    (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
      (M := 0) W₂ B₂ U₀ hU₀ sourceChart theta u hCtop)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball version of the Case 2 endpoint p.13 product source chart
source-readback field formula.

After shrinking the p.13 regular Euclidean variables around `0`, the
determinant-unit hypothesis for the decoded `Ctop` block is automatic, so the
product chart has the stated source-readback fields for every passive-theta
base point.  This is only a local coordinate/readback statement: no source
coverage, prior transport, Haar transport, normal crossings, pole order, or
RLCT extraction is proved. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_sourceReadback_fields
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
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      ∀ theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            let Ebase : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (sourceChart theta p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let Eprod : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (productSourceChart (theta, u) p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
            let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
            let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
            let C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ :=
              fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last 2) p p.succ.le_last
            let data := sourceReadback (K := ℝ) (ρ := ρ) (M := 1) (κ' := κ) Eprod
            data.A1passive = (fun _ : Fin 1 ↦ 1) ∧
              data.F2 = Fin.cases F2 (fun _ : Fin 1 ↦ 0) ∧
              data.A3passive = (fun _ : Fin 1 ↦ 0) ∧
              data.C = C ∧
              data.Ctop = Ctop ∧
              data.F3 = F3 := by
  rcases
      Aoyagi.exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
        (M := 0) W₂ B₂ U₀ hU₀
        (case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e)
        hRmax with
    ⟨R, hR, hRle, hfields⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart theta u hu
    Ebase Eprod F2 F3 Ctop C data
  simpa [ρ, κ, Coord, sourceChart, productSourceChart, Ebase, Eprod, F2, F3,
    Ctop, C, data] using hfields theta u hu

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball package of Case 2 endpoint p.13 product-source-chart readouts.

After shrinking the p.13 regular Euclidean variables around `0`, the same
radius supplies the determinant-unit hypothesis needed for raw coordinate-map
readout, regular readback, selected residual inverse-readout preservation, and
source-readback field canonicalization.  This is only local coordinate/readback
algebra: it is not full passive-theta recovery, source-image coverage, prior
transport, Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package
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
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      ∀ theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
                  (fun c ↦ u c)) ∧
            (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta) ∧
            (case2PassiveThetaEndpointProductSourceChartRegularReadback W₂ B₂ hU₀
                (productSourceChart (theta, u)) = u) ∧
            (case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (productSourceChart (theta, u)) =
              case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (sourceChart theta)) ∧
            let Ebase : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (sourceChart theta p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let Eprod : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (productSourceChart (theta, u) p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
            let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
            let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
            let C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ :=
              fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last 2) p p.succ.le_last
            let data := sourceReadback (K := ℝ) (ρ := ρ) (M := 1) (κ' := κ) Eprod
            data.A1passive = (fun _ : Fin 1 ↦ 1) ∧
              data.F2 = Fin.cases F2 (fun _ : Fin 1 ↦ 0) ∧
              data.A3passive = (fun _ : Fin 1 ↦ 0) ∧
              data.C = C ∧
              data.Ctop = Ctop ∧
              data.F3 = F3 := by
  rcases
      exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readout_package
        (M := 0) W₂ B₂ U₀ hU₀
        (case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e)
        hRmax with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart theta u hu
  have hgeneric := hpackage theta u hu
  have hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)).det :=
    by simpa [ρ, κ, Coord] using hgeneric.1
  have hcoord :
      (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
            (fun c ↦ u c)) ∧
      (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta) := by
    exact
      ⟨by
        simpa [ρ, κ, Coord, sourceChart, productSourceChart] using hgeneric.2.1,
       by
        simpa [ρ, κ, Coord, sourceChart, productSourceChart] using hgeneric.2.2.1⟩
  constructor
  · exact hcoord.1
  constructor
  · exact hcoord.2
  constructor
  · simpa [ρ, κ, Coord, sourceChart, productSourceChart] using
      case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta u hCtop
  constructor
  · simpa [ρ, κ, Coord, sourceChart, productSourceChart] using
      case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta u hCtop
  · intro Ebase Eprod F2 F3 Ctop C data
    simpa [ρ, κ, Coord, sourceChart, productSourceChart, Ebase, Eprod, F2, F3,
      Ctop, C, data] using hgeneric.2.2.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-rank-neighborhood version of the Case 2 endpoint p.13 product
source-chart product-reduction certificate.

For the same concrete product chart used by the readout package, a sufficiently
small regular-coordinate ball gives the fixed-base p.13 product-reduction
certificate eventually along any base source-rank filter.  This is a
constructed-product-chart certificate, not source-rank coverage, source-image
equality, source-prior transport, Haar/Jacobian transport, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_productReductionCertificate_nhdsWithin_source
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            PaperEndpointFixedBaseProductReductionCertificate
              (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart rEdge
              (theta, u) := by
  rcases
      exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
        (M := 0) W₂ B₂
        (α := Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
        (x₀ := theta₀) U₀ hU₀
        (case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (r := r) rEdge hRmax with
    ⟨R, hR, hRle, hcert⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart sourceStratum
  simpa [ρ, κ, Coord, EdgeFamily, sourceChart, productSourceChart, sourceStratum]
    using hcert

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The explicit multi-edge p.13 product-coordinate edge family lands in the
named retained-passive p.13 local source, provided the decoded `Ctop(u)` block
has unit determinant.

This is pointwise support for the constructed product-coordinate family.  It
does not prove source-rank coverage, source-image equality, source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, or RLCT
extraction. -/
theorem paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_retainedPassiveP13LocalSource
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    (x, u) ∈
      paperEndpointFixedBaseRetainedPassiveP13LocalSource
        (K := ℝ) (M := M + 1) V Bv U₀ hU₀ CedgeProd := by
  intro CedgeProd
  have hcert :
      PaperEndpointFixedBaseProductReductionCertificate
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd
        (fun _ : Fin (M + 2) ↦ 0) (x, u) := by
    simpa [CedgeProd] using
      paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        (M := M) V Bv U₀ hU₀ CedgeBase x u (fun _ : Fin (M + 2) ↦ 0) hCtop
  exact
    (mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
      (K := ℝ) (M := M + 1) V Bv U₀ hU₀ CedgeProd (x, u)).2 hcert.detCharts

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Concrete Case 2 specialization: the endpoint product source chart lands
in the named retained-passive p.13 local source when `Ctop(u)` is invertible.

This is one-way support for the constructed product source point.  It does
not prove source-rank coverage, source-image equality, source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction. -/
theorem case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource
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
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let productSourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
          EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) →
          EdgeFamily :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ sourceChart
    productSourceChart (theta, u) ∈
      paperEndpointFixedBaseRetainedPassiveP13LocalSource
        (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
  intro EdgeFamily sourceChart productSourceChart
  have hmem :
      (theta, u) ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource
          (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ productSourceChart := by
    simpa [sourceChart, productSourceChart] using
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_retainedPassiveP13LocalSource
        (M := 0) W₂ B₂ U₀ hU₀ sourceChart theta u hCtop
  simpa [productSourceChart, paperEndpointFixedBaseRetainedPassiveP13LocalSource] using hmem

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball source-filter support theorem for the concrete Case 2 endpoint
product source chart.

After shrinking the p.13 regular variables, the constructed product source
point lies in the named retained-passive p.13 local source, eventually along
any base source-rank filter.  This does not prove source-rank coverage,
source-image equality, source-prior transport, Haar/Jacobian transport,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            productSourceChart (theta, u) ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart sourceStratum
  exact Filter.Eventually.of_forall fun theta ↦ by
    intro u hu
    simpa [ρ, κ, Coord, EdgeFamily, sourceChart, productSourceChart] using
      case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta u (by simpa [ρ, κ, Coord] using hunit u hu)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball source-filter support theorem for the concrete Case 2 endpoint
product source chart, stated in the ambient named p.13 source edge-family set.

This is the source-edge-family-set version of
`exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source`.
It only unfolds the retained-passive local source as the preimage of the named
p.13 source edge-family set for the identity edge-family map.  It does not
prove source-rank coverage, source-image equality, source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_p13SourceEdgeFamilySet_nhdsWithin_source
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
      let p13SourceSet : Set EdgeFamily :=
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
          (K := ℝ) W₂ B₂ U₀ hU₀
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            productSourceChart (theta, u) ∈ p13SourceSet := by
  rcases
      exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e theta₀
        (r := r) (rEdge := rEdge) hRmax with
    ⟨R, hR, hRle, hsupport⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart sourceStratum p13SourceSet
  have hsupport' :
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            productSourceChart (theta, u) ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
    simpa [ρ, κ, Coord, EdgeFamily, sourceChart, productSourceChart, sourceStratum] using
      hsupport
  exact hsupport'.mono fun theta htheta u hu ↦ by
    have hlocal := htheta u hu
    simpa [p13SourceSet,
      paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet]
      using hlocal

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball product source-chart measures are supported on the named
retained-passive p.13 local source.

This is the measure-support wrapper for
`exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source`.
After choosing a sufficiently small regular-coordinate ball and an open
ambient base neighborhood `V`, used through `V ∩ sourceStratum`, the
pushforward of any product-domain measure restricted to that source-rank
carrier slice and the ball restricts to the retained-passive local source as
itself.

The theorem assumes the source-rank carrier is measurable and the product
source chart is a.e. measurable for the chosen restricted product measure.
It does not prove source-rank coverage, source-image equality, original
source-prior transport, Haar/Jacobian transport, normal crossings, pole order,
or RLCT extraction. -/
theorem exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      0 < R ∧ R ≤ Rmax ∧ IsOpen V ∧ theta₀ ∈ V ∧
        let ρ := Fin (Module.finrank ℝ U₀)
        let κ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
        let Coord :=
          AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
        let EdgeFamily :=
          ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
        let sourceChart :
            Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
          case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
        let productSourceChart :
            Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
              EuclideanSpace ℝ Coord →
              EdgeFamily :=
          paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
            W₂ B₂ U₀ hU₀ sourceChart
        let sourceStratum :=
          paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
        let regularBall := Metric.ball (0 : EuclideanSpace ℝ Coord) R
        let localSource :=
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
        MeasurableSet sourceStratum →
          V ∩ sourceStratum ⊆
            {theta |
              ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
                productSourceChart (theta, u) ∈ localSource} ∧
            ∀ thetaMeasure :
              Measure
                (Case2PassiveTheta
                  (ρ := ρ) (τ := τ) n S J),
            ∀ regularMeasure : Measure (EuclideanSpace ℝ Coord),
              let productDomainMeasure :=
                (thetaMeasure.restrict (V ∩ sourceStratum)).prod
                  (regularMeasure.restrict regularBall)
              AEMeasurable productSourceChart productDomainMeasure →
                let μ := Measure.map productSourceChart productDomainMeasure
                μ.restrict localSource = μ := by
  rcases
      exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e theta₀
        (r := r) (rEdge := rEdge) hRmax with
    ⟨R, hR, hRle, hsupport_eventually⟩
  refine ⟨R, ?_⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Coord :=
    AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let sourceChart :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
    case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
  let productSourceChart :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
        EuclideanSpace ℝ Coord →
        EdgeFamily :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      W₂ B₂ U₀ hU₀ sourceChart
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
  let regularBall := Metric.ball (0 : EuclideanSpace ℝ Coord) R
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource
      (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
  have hsupport_eventually' :
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
          productSourceChart (theta, u) ∈ localSource := by
    simpa [ρ, κ, Coord, EdgeFamily, sourceChart, productSourceChart,
      sourceStratum, regularBall, localSource] using hsupport_eventually
  rcases mem_nhdsWithin.1 hsupport_eventually' with
    ⟨V, hVopen, htheta₀V, hVsub⟩
  refine ⟨V, hR, hRle, hVopen, htheta₀V, ?_⟩
  change
    MeasurableSet sourceStratum →
      V ∩ sourceStratum ⊆
        {theta |
          ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
            productSourceChart (theta, u) ∈ localSource} ∧
        ∀ thetaMeasure :
          Measure
            (Case2PassiveTheta
              (ρ := ρ) (τ := τ) n S J),
        ∀ regularMeasure : Measure (EuclideanSpace ℝ Coord),
          let productDomainMeasure :=
            (thetaMeasure.restrict (V ∩ sourceStratum)).prod
              (regularMeasure.restrict regularBall)
          AEMeasurable productSourceChart productDomainMeasure →
            let μ := Measure.map productSourceChart productDomainMeasure
            μ.restrict localSource = μ
  intro hsourceStratum_meas
  constructor
  · exact hVsub
  · intro thetaMeasure regularMeasure productDomainMeasure hproduct_aemeas μ
    let thetaDomain :
        Set
          (Case2PassiveTheta
            (ρ := ρ) (τ := τ) n S J) :=
      V ∩ sourceStratum
    have hthetaDomain_meas : MeasurableSet thetaDomain :=
      hVopen.measurableSet.inter hsourceStratum_meas
    have htheta_support :
        ∀ᵐ theta ∂ thetaMeasure.restrict thetaDomain,
          ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
            productSourceChart (theta, u) ∈ localSource := by
      filter_upwards [ae_restrict_mem hthetaDomain_meas] with theta htheta
      exact hVsub htheta
    have htheta_support_prod :
        ∀ᵐ z ∂ productDomainMeasure,
          ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
            productSourceChart (z.1, u) ∈ localSource := by
      simpa [productDomainMeasure, thetaDomain] using
        (Measure.quasiMeasurePreserving_fst
          (μ := thetaMeasure.restrict thetaDomain)
          (ν := regularMeasure.restrict regularBall)).ae htheta_support
    have hregular_mem :
        ∀ᵐ u ∂ regularMeasure.restrict regularBall,
          u ∈ regularBall :=
      ae_restrict_mem Metric.isOpen_ball.measurableSet
    have hregular_mem_prod :
        ∀ᵐ z ∂ productDomainMeasure, z.2 ∈ regularBall := by
      simpa [productDomainMeasure, thetaDomain] using
        (Measure.quasiMeasurePreserving_snd
          (μ := thetaMeasure.restrict thetaDomain)
          (ν := regularMeasure.restrict regularBall)).ae hregular_mem
    have hchart_mem :
        ∀ᵐ z ∂ productDomainMeasure,
          productSourceChart z ∈ localSource := by
      filter_upwards [htheta_support_prod, hregular_mem_prod] with z hzsupport hzball
      exact hzsupport z.2 hzball
    simpa [μ, localSource, productDomainMeasure, thetaDomain] using
      measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
        (M := 1) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EdgeFamily ↦ E)
        (η := productDomainMeasure) (sourceChart := productSourceChart)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
        hproduct_aemeas hchart_mem

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball product source-chart measures are supported on the named p.13
source edge-family set.

This is the ambient source-edge-family-set version of
`exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self`.
It only rewrites the retained-passive local source for the identity edge-family
map as the named p.13 source edge-family set.  It does not prove source-rank
coverage, source-image equality, original source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_p13SourceEdgeFamilySet_eq_self
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      0 < R ∧ R ≤ Rmax ∧ IsOpen V ∧ theta₀ ∈ V ∧
        let ρ := Fin (Module.finrank ℝ U₀)
        let κ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
        let Coord :=
          AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
        let EdgeFamily :=
          ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
        let sourceChart :
            Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
          case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
        let productSourceChart :
            Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
              EuclideanSpace ℝ Coord →
              EdgeFamily :=
          paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
            W₂ B₂ U₀ hU₀ sourceChart
        let sourceStratum :=
          paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
        let regularBall := Metric.ball (0 : EuclideanSpace ℝ Coord) R
        let p13SourceSet : Set EdgeFamily :=
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
            (K := ℝ) W₂ B₂ U₀ hU₀
        MeasurableSet sourceStratum →
          V ∩ sourceStratum ⊆
            {theta |
              ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
                productSourceChart (theta, u) ∈ p13SourceSet} ∧
            ∀ thetaMeasure :
              Measure
                (Case2PassiveTheta
                  (ρ := ρ) (τ := τ) n S J),
            ∀ regularMeasure : Measure (EuclideanSpace ℝ Coord),
              let productDomainMeasure :=
                (thetaMeasure.restrict (V ∩ sourceStratum)).prod
                  (regularMeasure.restrict regularBall)
              AEMeasurable productSourceChart productDomainMeasure →
                let μ := Measure.map productSourceChart productDomainMeasure
                μ.restrict p13SourceSet = μ := by
  rcases
      exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e theta₀
        (r := r) (rEdge := rEdge) hRmax with
    ⟨R, V, hR, hRle, hVopen, htheta₀V, hsupport⟩
  refine ⟨R, V, hR, hRle, hVopen, htheta₀V, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart sourceStratum regularBall
    p13SourceSet hsourceStratum_meas
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource
      (K := ℝ) (M := 1) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
  have hsupport' :=
    hsupport hsourceStratum_meas
  change
    V ∩ sourceStratum ⊆
        {theta |
          ∀ u : EuclideanSpace ℝ Coord, u ∈ regularBall →
            productSourceChart (theta, u) ∈ p13SourceSet} ∧
      ∀ thetaMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := ρ) (τ := τ) n S J),
      ∀ regularMeasure : Measure (EuclideanSpace ℝ Coord),
        let productDomainMeasure :=
          (thetaMeasure.restrict (V ∩ sourceStratum)).prod
            (regularMeasure.restrict regularBall)
        AEMeasurable productSourceChart productDomainMeasure →
          let μ := Measure.map productSourceChart productDomainMeasure
          μ.restrict p13SourceSet = μ
  constructor
  · intro theta htheta u hu
    have hlocal : productSourceChart (theta, u) ∈ localSource := by
      simpa [localSource] using hsupport'.1 htheta u hu
    simpa [p13SourceSet, localSource,
      paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet]
      using hlocal
  · intro thetaMeasure regularMeasure productDomainMeasure hproduct_aemeas μ
    have hlocal_eq : μ.restrict localSource = μ := by
      simpa [localSource, productDomainMeasure, μ] using
        hsupport'.2 thetaMeasure regularMeasure hproduct_aemeas
    simpa [p13SourceSet, localSource,
      paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet]
      using hlocal_eq

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-rank-neighborhood version of the Case 2 endpoint p.13 product
source-chart readout package.

The small-ball readout package is uniform in the passive-theta base point, so
it holds eventually along any fixed-base source-rank stratum.  This is only a
filter-shaped coordinate/readback wrapper: no source-rank coverage,
source-image equality, source-prior transport, Haar/Jacobian transport, normal
crossings, pole order, or RLCT extraction is proved. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package_nhdsWithin_source
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
                  (fun c ↦ u c)) ∧
            (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta) ∧
            (case2PassiveThetaEndpointProductSourceChartRegularReadback W₂ B₂ hU₀
                (productSourceChart (theta, u)) = u) ∧
            (case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (productSourceChart (theta, u)) =
              case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (sourceChart theta)) ∧
            let Ebase : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (sourceChart theta p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let Eprod : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (productSourceChart (theta, u) p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
            let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
            let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
            let C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ :=
              fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last 2) p p.succ.le_last
            let data := sourceReadback (K := ℝ) (ρ := ρ) (M := 1) (κ' := κ) Eprod
            data.A1passive = (fun _ : Fin 1 ↦ 1) ∧
              data.F2 = Fin.cases F2 (fun _ : Fin 1 ↦ 0) ∧
              data.A3passive = (fun _ : Fin 1 ↦ 0) ∧
              data.C = C ∧
              data.Ctop = Ctop ∧
              data.F3 = F3 := by
  rcases
      exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e hRmax with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart sourceStratum
  exact Filter.Eventually.of_forall fun theta ↦ by
    intro u hu
    simpa [ρ, κ, Coord, sourceChart, productSourceChart] using hpackage theta u hu

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball version of the Case 2 p.13 product-source-chart coordinate
readout.

After shrinking the p.13 regular Euclidean variables around `0`, the full
product chart built from the passive-theta endpoint source chart has regular
coordinate readout `u` and residual-coordinate readout equal to the underlying
passive-theta source residual readout, eventually along the base source-rank
stratum.

This packages the `ctopMatrix u` unit-determinant condition by a local radius.
It is still only a coordinate readout theorem: no full inverse to `(theta,u)`,
source-image coverage, original prior transport, Haar transport, normal
crossings, pole order, or RLCT extraction is proved. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq_nhdsWithin_source
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
    [TopologicalSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let Coord :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
            EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge
      (∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
                fun i ↦ u i) ∧
      (∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta) := by
  rcases
      exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package_nhdsWithin_source
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e theta₀
        (r := r) (rEdge := rEdge) hRmax with
    ⟨R, hR, hRle, hpackage⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro Coord EdgeFamily sourceChart productSourceChart sourceStratum
  have hfull :
      ∀ᶠ theta in nhdsWithin theta₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ Coord,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
            (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
                  (fun c ↦ u c)) ∧
            (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ productSourceChart (theta, u) =
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart theta) ∧
            (case2PassiveThetaEndpointProductSourceChartRegularReadback W₂ B₂ hU₀
                (productSourceChart (theta, u)) = u) ∧
            (case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (productSourceChart (theta, u)) =
              case2PassiveThetaEndpointInverseReadout W₂ B₂ n hS hnext hU₀ eNext e
                (sourceChart theta)) ∧
            let ρ := Fin (Module.finrank ℝ U₀)
            let κ := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
            let Ebase : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (sourceChart theta p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let Eprod : ∀ p : Fin 2, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p ↦
                  (productSourceChart (theta, u) p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
            let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
            let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
            let C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ :=
              fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last 2) p p.succ.le_last
            let data := sourceReadback (K := ℝ) (ρ := ρ) (M := 1) (κ' := κ) Eprod
            data.A1passive = (fun _ : Fin 1 ↦ 1) ∧
              data.F2 = Fin.cases F2 (fun _ : Fin 1 ↦ 0) ∧
              data.A3passive = (fun _ : Fin 1 ↦ 0) ∧
              data.C = C ∧
              data.Ctop = Ctop ∧
              data.F3 = F3 := by
    simpa [Coord, sourceChart, productSourceChart, sourceStratum] using hpackage
  constructor
  · exact hfull.mono fun theta htheta u hu ↦ (htheta u hu).1
  · exact hfull.mono fun theta htheta u hu ↦ (htheta u hu).2.1

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
/-- Relative local source-chart image measurability and continuity for the
enlarged following-factor endpoint chart.

Inside any prescribed open enlarged theta-neighborhood `G` of a
determinant-sector, nonzero-pivot base point, there is a smaller open `V` on
which the enlarged endpoint source-chart readback is a left inverse, the
source chart is injective, and the source chart is continuous with measurable
image `sourceChart '' V`.

This is a local chart-image theorem only.  It does not state source-rank
coverage, source-image equality beyond this local chart image, source-prior
transport, Haar/Jacobian transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  obtain ⟨Vread, hVread_open, hz₀Vread, hleft⟩ :=
    (by
      simpa [EdgeFamily, sourceChart, readback, ρ, κ'] using
        exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let D : Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    Y ⁻¹' detSet
  have hYcont : Continuous Y := by
    simpa [Y, ρ, κ'] using
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_mem_detChartSet
          (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
    simpa [D] using hY₀
  let V :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    G ∩ (Vread ∩ D)
  have hVopen : IsOpen V := hGopen.inter (hVread_open.inter hDopen)
  have hz₀V : z₀ ∈ V := ⟨hz₀G, ⟨hz₀Vread, hz₀D⟩⟩
  have hVG : V ⊆ G := Set.inter_subset_left
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ Vread := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz.2.1
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzread_fields
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
      continuous_case2PassiveThetaWithFollowingFactorEndpointRetainedData
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
    simpa [sourceChart, case2PassiveThetaWithFollowingFactorEndpointSourceChart,
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
/-- The local enlarged following-factor endpoint source-chart image is
contained in the named p.13 retained-passive source edge-family set.

This is one-way support for chart-produced source points.  It does not prove
source coverage, source-image equality with the p.13 source set, source-rank
coverage, source-prior transport, Haar/Jacobian transport, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          (∀ z ∈ V, readback (sourceChart z) = z) ∧
            Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
              MeasurableSet (sourceChart '' V) ∧
                (∀ z ∈ V, sourceChart z ∈ p13SourceSet) ∧
                  ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
  intro EdgeFamily retainedData sourceChart readback p13SourceSet
  rcases
      (by
        simpa [EdgeFamily, retainedData, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  have hdetV' : ∀ z ∈ V, (retainedData z).detChart := by
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
    simpa [retainedData, Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hdetV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hpoint : ∀ z ∈ V, sourceChart z ∈ p13SourceSet := by
    intro z hzV
    let detData :
        {data :
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) // data.detChart} :=
      ⟨retainedData z, hdetV' z hzV⟩
    have hmem :
        paperEndpointFixedBaseRetainedPassiveP13SourceChart
            W₂ B₂ U₀ hU₀ detData ∈
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
            (K := ℝ) W₂ B₂ U₀ hU₀ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
        (K := ℝ) W₂ B₂ detData
    simpa [sourceChart, p13SourceSet, retainedData,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData, detData] using hmem
  have himage_subset : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hpoint z hzV
  exact
    ⟨V, hVopen, hz₀V, hVG, hdetV', hleftV', hsource_inj, hsource_contOn,
      hsource_image, hpoint, himage_subset⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Pulling back the chart-produced enlarged following-factor endpoint
source-image reference recovers the restricted enlarged theta-domain reference
measure.

This is the concrete source-reference version of the local with-following
source-chart left-inverse calculation.  It identifies only the measure
produced by pushing `thetaReference.restrict V` through the chart.  It does
not identify an original source prior, prove source-image coverage or density
comparison, transport Haar measure, prove normal crossings, compute pole
order, or extract an RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_map_readback_sourceReference_eq_self
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaReference :
                Measure
                  (Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                let sourceRef :=
                  Measure.map sourceChart (thetaReference.restrict V)
                AEMeasurable readback sourceRef ∧
                  Measure.map readback sourceRef =
                    thetaReference.restrict V := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, _hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzread_fields
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_contOn' : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_contOn',
      hsource_image', ?_⟩
  intro thetaReference
  let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
  have hsource_aemeas : AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn'.aemeasurable hVmeas
  have hreadback : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOn'
        hsource_inj' hleftV'
  have hmap : Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        (by simpa [sourceRef] using hreadback) hleftV'
  exact ⟨hreadback, hmap⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The chart-produced enlarged following-factor endpoint source-image
reference is supported on the actual local source-chart image.

After shrinking inside any prescribed open enlarged theta-neighborhood `G`,
every pushforward `Measure.map sourceChart (thetaMeasure.restrict V)` is
already supported on the measurable image `sourceChart '' V`.

This is image-support bookkeeping for chart-produced measures only.  It does
not prove source-image coverage beyond this local image, identify an original
source prior, compare densities, transport Haar measure, prove normal
crossings, compute pole order, or extract an RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_restrict_image_eq_self_readback_leftInverse
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaMeasure :
                Measure
                  (Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              let μ := Measure.map sourceChart (thetaMeasure.restrict V)
              μ.restrict (sourceChart '' V) = μ := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, _hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzread_fields
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_contOn' : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_contOn',
      hsource_image', ?_⟩
  intro thetaMeasure μ
  have hsource_aemeas : AEMeasurable sourceChart (thetaMeasure.restrict V) :=
    ContinuousOn.aemeasurable hsource_contOn' hVopen.measurableSet
  simpa [μ] using
    measure_map_restrict_image_eq_self_of_aemeasurable
      sourceChart thetaMeasure V hVopen.measurableSet hsource_image'
      hsource_aemeas

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Local bounded-density source-image pullback for the enlarged
with-following endpoint source chart, with readback a.e. measurability
generated internally.

After shrinking inside any prescribed open enlarged theta-neighborhood `G`,
any bounded-density perturbation of the chart-produced source-image reference
measure pulls back by the readback to a measure dominated by the corresponding
theta-domain reference measure on `V`.  The readback a.e. measurability is
derived from the local continuous injective source chart and its pointwise
readback left inverse.

This remains a density-comparison socket.  It does not construct or identify
an original source prior, prove source-image coverage, prove Haar transport,
construct normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul_of_continuousOn_injOn
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaReference :
                Measure
                  (Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              ∀ density : EdgeFamily → ENNReal,
              ∀ c : ENNReal,
                (∀ᵐ E ∂(Measure.map sourceChart
                    (thetaReference.restrict V)).restrict (sourceChart '' V),
                  density E ≤ c) →
                Measure.map readback
                    (((Measure.map sourceChart
                      (thetaReference.restrict V)).withDensity density).restrict
                      (sourceChart '' V)) ≤
                  c • thetaReference.restrict V := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_restrict_image_eq_self_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, _hsupport⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzread_fields
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_contOn' : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_contOn',
      hsource_image', ?_⟩
  intro thetaReference density c hdensity_le
  exact
    measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le_of_continuousOn_injOn
      sourceChart readback thetaReference V density c hVopen.measurableSet
      hsource_image' hsource_contOn' hsource_inj' hleftV' hdensity_le

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
/-- Pull back an external source-side measure restricted to the concrete local
passive-theta source-chart image, and push it forward back to the same
restricted external measure.

The returned measure identity is only for the portion of `externalMeasure`
already restricted to the actual measurable image `sourceChart '' V`.  It does
not prove that an original source prior is supported in one chart image, nor
does it prove a density domination by the passive-theta Jacobian measure,
Haar transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_image_eq_self
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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V,
                readback E ∈ V ∧ sourceChart (readback E) = E) ∧
                ∀ externalMeasure : Measure EdgeFamily,
                  AEMeasurable readback
                    (externalMeasure.restrict (sourceChart '' V)) →
                    let candidateMeasure :=
                      Measure.map readback
                        (externalMeasure.restrict (sourceChart '' V))
                    candidateMeasure.restrict V = candidateMeasure ∧
                      Measure.map sourceChart candidateMeasure =
                        externalMeasure.restrict (sourceChart '' V) := by
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
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_contOn' : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  have hright : ∀ E ∈ sourceChart '' V,
      readback E ∈ V ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    constructor
    · simpa [hleftV' z hzV] using hzV
    · rw [hleftV' z hzV]
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_contOn',
      hsource_image', hright, ?_⟩
  intro externalMeasure hreadback
  let candidateMeasure : Measure
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    Measure.map readback (externalMeasure.restrict (sourceChart '' V))
  have hsupport : candidateMeasure.restrict V = candidateMeasure :=
    measure_map_readback_restrict_image_restrict_eq_self_of_aemeasurable
      readback externalMeasure (sourceChart '' V) V hsource_image' hVmeas
      hreadback (fun E hE ↦ (hright E hE).1)
  have hsourceChart :
      AEMeasurable sourceChart candidateMeasure :=
    aemeasurable_of_continuousOn_of_measure_restrict_eq_self
      hsource_contOn' hVmeas hsupport
  have hmap :
      Measure.map sourceChart candidateMeasure =
        externalMeasure.restrict (sourceChart '' V) :=
    measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
      sourceChart readback externalMeasure (sourceChart '' V) hsource_image'
      hreadback hsourceChart (fun E hE ↦ (hright E hE).2)
  exact ⟨hsupport, hmap⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 specialization unfolds several large endpoint chart types.
/-- Conditional local density transport from the raw-order p.13 chart to the
concrete passive-theta source chart.

On a sufficiently small determinant/pivot sector, the raw-order p.13 source
chart agrees pointwise with the concrete passive-theta endpoint source chart.
Consequently any raw density on the `rawMap` pushforward of
`thetaReference.restrict V` transports to the same source-side measure as the
composed theta-domain density.

This theorem does not identify determinant-chart Haar measure, raw-order Haar
measure, an original source prior, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpoint_rawOrderSourceChart_withDensity_eq_sourceChart_withDensity
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
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, rawChart (rawMap z) = sourceChart z) ∧
          ∀ [BorelSpace EdgeFamily],
          ∀ thetaReference :
            Measure
              (Case2PassiveTheta
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          ∀ rawDensity : RawTuple → ENNReal,
            AEMeasurable rawMap (thetaReference.restrict V) →
              AEMeasurable rawDensity
                (Measure.map rawMap (thetaReference.restrict V)) →
                Measure.map rawChart
                  ((Measure.map rawMap
                    (thetaReference.restrict V)).withDensity rawDensity) =
                  Measure.map sourceChart
                    ((thetaReference.withDensity
                      (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawChart
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmeasure_maps⟩
  have hraw_source : ∀ z ∈ V, rawChart (rawMap z) = sourceChart z := by
    intro z hz
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using
      (hpoint z hz).2.2.1
  refine ⟨V, hVopen, hz₀V, hVG, hraw_source, ?_⟩
  intro _instBorel thetaReference rawDensity hrawMap hrawDensity
  have htwoStage :
      Measure.map rawChart
          (Measure.map rawMap
            ((thetaReference.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V)) =
        Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
    have hmaps :=
      hmeasure_maps
        (sourceMeasure :=
          thetaReference.withDensity
            (fun theta ↦ rawDensity (rawMap theta)))
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  exact
    DLNFibre.DLN.Aoyagi.measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
      (hV := hVopen.measurableSet) hrawMap hrawDensity htwoStage

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The with-following specialization has the same proof shape as the
-- passive-theta handoff but unfolds the enlarged endpoint tuple types.
/-- Conditional local density transport from the raw-order p.13 chart to the
enlarged with-following endpoint source chart.

On a sufficiently small determinant/pivot sector, the raw-order p.13 source
chart agrees pointwise with the enlarged with-following endpoint source chart.
Consequently any raw density on the `rawMap` pushforward of
`thetaReference.restrict V` transports to the same source-side measure as the
composed theta-domain density.

This theorem does not identify determinant-chart Haar measure, raw-order Haar
measure, an original source prior, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpoint_rawOrderSourceChart_withDensity_eq_sourceChart_withDensity
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, rawChart (rawMap z) = sourceChart z) ∧
          ∀ [BorelSpace EdgeFamily],
          ∀ thetaReference :
            Measure
              (Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          ∀ rawDensity : RawTuple → ENNReal,
            AEMeasurable rawMap (thetaReference.restrict V) →
              AEMeasurable rawDensity
                (Measure.map rawMap (thetaReference.restrict V)) →
                Measure.map rawChart
                  ((Measure.map rawMap
                    (thetaReference.restrict V)).withDensity rawDensity) =
                  Measure.map sourceChart
                    ((thetaReference.withDensity
                      (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawChart
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, hmeasure_maps⟩
  have hraw_source : ∀ z ∈ V, rawChart (rawMap z) = sourceChart z := by
    intro z hz
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using
      (hpoint z hz).2.2.1
  refine ⟨V, hVopen, hz₀V, hVG, hraw_source, ?_⟩
  intro _instBorel thetaReference rawDensity hrawMap hrawDensity
  have htwoStage :
      Measure.map rawChart
          (Measure.map rawMap
            ((thetaReference.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V)) =
        Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
    have hmaps :=
      hmeasure_maps
        (sourceMeasure :=
          thetaReference.withDensity
            (fun theta ↦ rawDensity (rawMap theta)))
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  exact
    DLNFibre.DLN.Aoyagi.measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
      (hV := hVopen.measurableSet) hrawMap hrawDensity htwoStage

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Pulling back the chart-produced passive-theta endpoint source-image
reference recovers the restricted theta-domain reference measure.

This is the concrete source-reference version of the local source-chart
left-inverse calculation.  It identifies only the measure produced by pushing
`thetaReference.restrict V` through the chart.  It does not identify an
original source prior, prove source-image coverage or density comparison,
transport Haar measure, prove normal crossings, compute pole order, or extract
an RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_sourceReference_eq_self
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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaReference :
                Measure
                  (Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                let sourceRef :=
                  Measure.map sourceChart (thetaReference.restrict V)
                AEMeasurable readback sourceRef ∧
                  Measure.map readback sourceRef =
                    thetaReference.restrict V := by
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
  have hsource_inj' : Set.InjOn sourceChart V := by
    simpa [sourceChart] using hsource_inj
  have hsource_contOn' : ContinuousOn sourceChart V := by
    simpa [sourceChart] using hsource_contOn
  have hsource_image' : MeasurableSet (sourceChart '' V) := by
    simpa [sourceChart] using hsource_image
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj', hsource_contOn',
      hsource_image', ?_⟩
  intro thetaReference
  let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
  have hsource_aemeas : AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn'.aemeasurable hVmeas
  have hreadback : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOn'
        hsource_inj' hleftV'
  have hmap : Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        (by simpa [sourceRef] using hreadback) hleftV'
  exact ⟨hreadback, hmap⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Concrete chart-piece bounded-density readback domination for the
passive-theta endpoint source chart.

On the local source-chart image, if a measurable chart piece of an external
source measure is identified as a bounded-density perturbation of the
chart-produced source reference, then its readback pullback is dominated by the
corresponding theta reference on any supplied theta superset.  The bounded
density identity and bound remain hypotheses. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaSuperset :
                Set
                  (Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              ∀ chartPiece : Set EdgeFamily,
              ∀ externalMeasure : Measure EdgeFamily,
              ∀ thetaReference :
                Measure
                  (Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              ∀ density : EdgeFamily → ENNReal,
              ∀ c : ENNReal,
                V ⊆ thetaSuperset →
                  MeasurableSet chartPiece →
                    externalMeasure.restrict chartPiece =
                      ((Measure.map sourceChart
                        (thetaReference.restrict V)).withDensity density).restrict
                        chartPiece →
                      (∀ᵐ E ∂(Measure.map sourceChart
                        (thetaReference.restrict V)).restrict chartPiece,
                        density E ≤ c) →
                        AEMeasurable readback
                          (externalMeasure.restrict chartPiece) ∧
                          Measure.map readback
                            (externalMeasure.restrict chartPiece) ≤
                            c • thetaReference.restrict thetaSuperset := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_sourceReference_eq_self
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, _hsource_ref⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj, hsource_contOn,
      hsource_image, ?_⟩
  intro thetaSuperset chartPiece externalMeasure thetaReference density c
    hVW hchartPiece heq hdensity_le
  exact
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
      sourceChart readback externalMeasure thetaReference V thetaSuperset
      chartPiece density c hVmeas hchartPiece hVW hsource_contOn hsource_inj
      hleftV' heq hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Local bounded-density source-image pullback for the concrete passive-theta
endpoint source chart.

After shrinking inside any prescribed open theta-neighborhood `G`, any
bounded-density perturbation of the chart-produced source-image reference
measure pulls back by the readback to a measure dominated by the corresponding
theta-domain reference measure on `V`.

This is a density-comparison socket.  It assumes the source-image density
bound and readback a.e. measurability for the chart-produced source-image
reference measure; it does not construct or identify an original source prior,
prove source-rank coverage, prove Haar transport, construct normal crossings,
compute pole order, or extract RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul
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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaReference :
                Measure
                  (Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              ∀ density : EdgeFamily → ENNReal,
              ∀ c : ENNReal,
                AEMeasurable readback
                  (Measure.map sourceChart (thetaReference.restrict V)) →
                (∀ᵐ E ∂ (Measure.map sourceChart
                    (thetaReference.restrict V)).restrict (sourceChart '' V),
                  density E ≤ c) →
                Measure.map readback
                    (((Measure.map sourceChart
                      (thetaReference.restrict V)).withDensity density).restrict
                      (sourceChart '' V)) ≤
                  c • thetaReference.restrict V := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_image_eq_self
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, _hright, _hpullback⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj, hsource_contOn,
      hsource_image, ?_⟩
  intro thetaReference density c hreadback hdensity_le
  have hsource :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hVopen.measurableSet
  exact
    measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
      sourceChart readback thetaReference V density c hVopen.measurableSet
      hsource_image hsource hreadback hleftV' hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Local bounded-density source-image pullback for the concrete passive-theta
endpoint source chart, with readback a.e. measurability generated internally.

After shrinking inside any prescribed open theta-neighborhood `G`, any
bounded-density perturbation of the chart-produced source-image reference
measure pulls back by the readback to a measure dominated by the corresponding
theta-domain reference measure on `V`.  Unlike
`exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul`,
this version derives readback a.e. measurability from the local continuous
injective source chart and its pointwise readback left inverse.

This remains a density-comparison socket.  It does not construct or identify
an original source prior, prove source-rank coverage, prove Haar transport,
construct normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul_of_continuousOn_injOn
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
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              ∀ thetaReference :
                Measure
                  (Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
              ∀ density : EdgeFamily → ENNReal,
              ∀ c : ENNReal,
                (∀ᵐ E ∂ (Measure.map sourceChart
                    (thetaReference.restrict V)).restrict (sourceChart '' V),
                  density E ≤ c) →
                Measure.map readback
                    (((Measure.map sourceChart
                      (thetaReference.restrict V)).withDensity density).restrict
                      (sourceChart '' V)) ≤
                  c • thetaReference.restrict V := by
  intro EdgeFamily sourceChart readback
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, hbounded⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV', hsource_inj, hsource_contOn,
      hsource_image, ?_⟩
  intro thetaReference density c hdensity_le
  have hreadback :
      AEMeasurable readback
        (Measure.map sourceChart (thetaReference.restrict V)) :=
    aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
      sourceChart readback thetaReference V hVopen.measurableSet
      hsource_contOn hsource_inj hleftV'
  exact hbounded thetaReference density c hreadback hdensity_le

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
/-- A concrete passive-theta endpoint source-chart point carries the fixed-base
product-reduction certificate as soon as its retained endpoint datum is in the
determinant chart.

This is certificate bookkeeping for the chart-produced source point.  It does
not prove source-rank coverage, source-image equality, source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction. -/
theorem case2PassiveThetaEndpointSourceChart_productReductionCertificate
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
    (rEdge : Fin 2 → ℕ)
    (hdet :
      (case2PassiveThetaEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e).detChart) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    PaperEndpointFixedBaseProductReductionCertificate
      (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart rEdge theta := by
  intro EdgeFamily sourceChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let data :
      RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' :=
    case2PassiveThetaEndpointRetainedData
      (ρ := ρ) n hS hcont hnext theta eNext e
  have hlocal_sub :
      (⟨data, by simpa [data, ρ, κ'] using hdet⟩ :
        {data :
          RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
          data.detChart}) ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource
          W₂ B₂ U₀ hU₀
          (paperEndpointFixedBaseRetainedPassiveP13SourceChart
            (K := ℝ) W₂ B₂ U₀ hU₀) := by
    exact
      paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_localSource
        (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
        ⟨data, by simpa [data, ρ, κ'] using hdet⟩
  have hlocal :
      theta ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource
          W₂ B₂ U₀ hU₀ sourceChart := by
    simpa [sourceChart, case2PassiveThetaEndpointSourceChart, data, ρ, κ'] using
      hlocal_sub
  have hcharts :
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts
        W₂ B₂ U₀ hU₀ sourceChart theta :=
    (mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
      (K := ℝ) W₂ B₂ U₀ hU₀ sourceChart theta).1 hlocal
  exact
    paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts
      (K := ℝ) W₂ B₂ U₀ hU₀ sourceChart rEdge theta hcharts

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Small-ball source-rank preservation for the concrete Case 2 endpoint p.13
product source chart.

Under the explicit Case 2 source-rank equations for the passive-theta base
point, adding sufficiently small p.13 regular coordinates keeps the product
source chart in the same named source-rank stratum.  This is one-way
chart-produced source-rank membership, not source-rank coverage or source-image
equality. -/
theorem exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_sourceRankStratum_of_base_rank
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
    {r : ℕ} {rEdge : Fin 2 → ℕ} {Rmax : ℝ}
    (hRmax : 0 < Rmax)
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last 2)) (κ 0)
      let EdgeFamily :=
        ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
      let sourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
        case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
      let productSourceChart :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            EuclideanSpace ℝ Coord →
            EdgeFamily :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          W₂ B₂ U₀ hU₀ sourceChart
      ∀ theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J,
        (case2PassiveThetaEndpointRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext e).detChart →
          r + Fintype.card τ = rEdge 0 →
          r + (case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).rank =
            rEdge 1 →
          ∀ u : EuclideanSpace ℝ Coord,
            u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
              (theta, u) ∈
                paperEndpointFixedBaseSourceRankStratum
                  (K := ℝ) (N := 2) W₂ B₂ productSourceChart r rEdge := by
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro ρ κ Coord EdgeFamily sourceChart productSourceChart theta hdet hr0 hr1 u hu
  have hbase_cert :
      PaperEndpointFixedBaseProductReductionCertificate
        (K := ℝ) (N := 2) W₂ B₂ U₀ hU₀ sourceChart rEdge theta := by
    simpa [ρ, κ, Coord, sourceChart] using
      case2PassiveThetaEndpointSourceChart_productReductionCertificate
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta rEdge hdet
  have hbase_src :
      theta ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ sourceChart r rEdge := by
    simpa [ρ, κ, Coord, sourceChart] using
      case2PassiveThetaEndpointSourceChart_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        theta hdet hprod hr0 hr1
  simpa [ρ, κ, Coord, sourceChart, productSourceChart] using
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum
      (V := W₂) (Bv := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := sourceChart) (x := theta) (u := u)
      (r := r) (rEdge := rEdge) hbase_cert hbase_src
      (by simpa [ρ, κ, Coord] using hunit u hu)

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
/-- The local passive-theta endpoint source-chart image is contained in the
named p.13 retained-passive source edge-family set.

This is one-way support for chart-produced source points.  It does not prove
source coverage, source-image equality with the p.13 source set, source-rank
coverage, source-prior transport, Haar/Jacobian transport, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          (∀ z ∈ V, readback (sourceChart z) = z) ∧
            Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
              MeasurableSet (sourceChart '' V) ∧
                (∀ z ∈ V, sourceChart z ∈ p13SourceSet) ∧
                  ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
  intro EdgeFamily retainedData sourceChart readback p13SourceSet
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
  have hpoint : ∀ z ∈ V, sourceChart z ∈ p13SourceSet := by
    intro z hzV
    let detData :
        {data :
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) // data.detChart} :=
      ⟨retainedData z, hdetV' z hzV⟩
    have hmem :
        paperEndpointFixedBaseRetainedPassiveP13SourceChart
            W₂ B₂ U₀ hU₀ detData ∈
          paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
            (K := ℝ) W₂ B₂ U₀ hU₀ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet
        (K := ℝ) W₂ B₂ detData
    simpa [sourceChart, p13SourceSet, retainedData,
      case2PassiveThetaEndpointSourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData, detData] using hmem
  have himage_subset : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    exact hpoint z hzV
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
