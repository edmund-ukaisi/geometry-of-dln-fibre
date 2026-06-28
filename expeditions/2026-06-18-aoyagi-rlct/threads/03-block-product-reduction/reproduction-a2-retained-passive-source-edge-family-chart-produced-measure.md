# Reproduction - A2 retained-passive source-edge-family chart-produced measure

## Shape

The existing chart-produced selected-entry retained-passive handoff takes an
arbitrary source chart

```text
sourceChart : (center -> R) -> alpha
```

and requires three source-side inputs:

```text
hsourceChart : AEMeasurable sourceChart signedBox
hchart_mem   : forall y, sourceChart y in retainedPassiveP13LocalSource
hfactor      : forall y, sourceReadback(sourceChart y) has selected-entry residual factor
```

The target fixes `alpha` to the fixed-base p.13 edge-family type and fixes

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (retainedData y).
```

It replaces the three source-side inputs by retained-passive coordinate data:

```text
retainedData : (center -> R) -> RetainedPassiveNonredundantCoordinateData
hdet         : forall y, (retainedData y).detChart
hretainedData:
  AEMeasurable (fun y => <retainedData y, hdet y>) signedBox
hdataFactor  :
  forall y, residualFactorProduct (retainedData y).C last 0 =
    selected-entry matrix read from y
```

At the Lean boundary, the determinant-chart subtype also needs measurable and
open-measurable structure so the continuous p.13 source chart is measurable
out of it.  All regular-coordinate hypotheses, residual radii, critical
selected-entry inequality, local loss lower bound, and density bounds remain
explicit.

## Calculation

Let

```text
EdgeFamily :=
  forall p : Fin (M + 1),
    reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ

base p := LinearMap.toContinuousLinearMap (reverseEdge W B p)

DetData := {data : RetainedPassiveNonredundantCoordinateData // data.detChart}

signedBox :=
  Measure.pi (fun i : center => volume.restrict (Ioo (-(Rres i)) (Rres i)))

sourceMeasure :=
  signedBox.withDensity
    (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))
```

and define

```text
sourceChart y :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (retainedData y).
```

The source map is a composition through the determinant-chart subtype:

```text
y |-> <retainedData y, hdet y>
      |-> paperEndpointFixedBaseRetainedPassiveP13SourceChart W B U0 hU0
```

The first arrow is `hretainedData`.  The second arrow is continuous by

```text
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
```

and therefore measurable once `DetData` is open-measurable and `EdgeFamily` is
Borel.  Hence `sourceChart` is a.e. measurable with respect to `signedBox`.
After unfolding `paperEndpointFixedBaseRetainedPassiveP13SourceChart`, this is
precisely the `hsourceChart` required by the existing chart-produced theorem.

Next apply

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
```

to `retainedData`, `hdet`, `residualCoordEquiv`, and `hdataFactor`.  This
returns both:

```text
forall y, sourceChart y in
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 (fun E => E)
```

and the source-readback residual-factor matrix identity for the same
`sourceChart`.  These are the `hchart_mem` and `hfactor` inputs required by the
existing chart-produced theorem.

Finally invoke

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
```

with

```text
alpha  := EdgeFamily
Cedge  := fun E : EdgeFamily => E
x0     := base
mu     := Measure.map sourceChart sourceMeasure
```

The identity edge-family map is continuous and sends `base` to the fixed-base
edge family by reflexivity.  The existing theorem then gives the open
neighborhood and finite integral conclusion for the chart-produced measure.

## Boundary

This removes real retained-passive p.13 source-chart plumbing: a caller no
longer supplies a separate source-chart measurability proof, local-source
membership proof, or source-readback selected-entry factor proof.  The caller
must still supply the retained-data determinant chart, retained-data
measurability, retained-data selected-entry residual-factor identity, and the
measurable/open-measurable structure for the determinant-chart subtype.

It does not construct endpoint equivalences, prove label-preserving endpoint
provenance, identify an original source prior, compare Jacobians for an
external prior, prove source-rank coverage, prove normal crossings, compute
pole order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** A determinant-chart retained-passive data path
with the selected-entry residual-factor identity supplies the chart-produced
p.13 source-measure finite-integral handoff.

**Assumed.** The retained-data determinant proof and a.e. measurability,
determinant-subtype measurability/open-measurability, the retained-data
residual-factor matrix identity, positive residual radii, the selected-entry
critical inequality, regular-coordinate Haar measure, local loss lower bound,
and local density bounds.

**Deferred.** Endpoint provenance, original prior/source measure
identification, Jacobian comparison, source-rank coverage, normal crossings,
pole order, and RLCT extraction.
