# Source Audit - A2 source-prior density and determinant-Haar frontier

Date: 2026-07-02.

Status: controller source/API audit with xhigh read-only scouts `Dalton` and
`Hegel`.  No Lean theorem is proposed from this audit.

## Question

After the formal-product determinant-domination wrapper, is there a current
Aoyagi-only route to remove either of the two remaining source-prior inputs?

1. The source-density lower bound:

```text
forall-a.e. z with respect to baseJ.restrict V,
  epsilon <= sourceImageDensity (sourceChart z).
```

2. The determinant-side reverse domination:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V).
```

## Source Check

Aoyagi pp. 10-13 prove the elementary block algebra:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4,
```

then iterate it to get regular endpoint factors and a reduced product
`prod_s C^(s)`.  The printed calculation also gives the loss split:

```text
lambda_w*(prod_s A^(s) - prod_s A*^(s))
  = regular contribution + lambda_w*(prod_s C^(s)).
```

This supports the retained-passive chart, raw-order map, p.13 source chart,
and Jacobian/local-coordinate infrastructure already formalized.  It does not
state a transport theorem identifying the original ambient DLN prior with a
chart-produced passive-theta image measure.  It also does not state that the
Case 2 endpoint topology-tuple image of the selected-entry passive-theta
domain is full determinant-chart Haar.

## Density Frontier

The selected-entry residual density is real Lean infrastructure:

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity
```

and it is already folded into the Case 2 weighted residual box:

```text
weightedBox =
  signedBox.withDensity
    (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext).
```

This is only the residual-center signed-box density.  It is not the later
edge-family source-image density socket:

```text
sourceImageDensity : EdgeFamily -> ENNReal
sourceDensity z = sourceImageDensity (sourceChart z).
```

The current consumers still require either the a.e. lower bound on
`sourceDensity` or the stronger pointwise image lower bound on
`sourceChart '' V`.  The continuity helper only says that, if this density is
already continuous at the base point and strictly positive there, then the
eventual lower bound follows.  It does not construct the density or prove
continuity/positivity.

Therefore the exact missing density input is a source-measure identification
or bounded-density theorem of the form:

```text
external/original source measure on sourceChart '' V
  = (Measure.map sourceChart (coordinate theta measure)).withDensity concreteDensity
```

with `concreteDensity` positive and locally bounded below at the base point.
Defining the external source measure to be the right-hand side is not progress.

## Determinant-Haar Frontier

There is honest Haar transport for the ambient retained-passive raw-order map
once the source measure is already additive Haar on the full topology-tuple
space.  The relevant APIs start from an additive Haar measure `rawHaar` and
push it through raw-order maps.

The missing direction for the A2 wrappers is different:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V).
```

The endpoint reference layer names legitimate image-reference measures such
as:

```text
case2PassiveThetaEndpointReferenceImageMeasure
  = Measure.map Y (referenceSource.restrict Omega).
```

It also proves support inside the determinant chart and domination by that
image reference under passive-field domination.  This is not determinant Haar
transport.  The image reference is the actual pushforward of the selected
Case 2 passive-theta domain; it is not unrestricted additive Haar on
`rawDetChart`.

The obstruction is dimensional/coverage in the present Lean API: the target
`TopologyTuple` carries the full retained-passive determinant-chart tuple,
whereas the Case 2 selected-entry passive-theta map fills part of the data
through selected residual coordinates.  Current files do not prove that
`Y(V)` covers the determinant chart up to Haar-null sets, nor do they provide
a local inverse/open-image theorem and Jacobian density proving equivalence
with restricted additive Haar.

## Consequence

No current non-circular Lean theorem removes either frontier field.  Further
wrappers from pointwise or eventual density lower bounds into formal-product
or prior domination would be conditional hardening only; they would not be
source-prior progress.

The next genuine construction target must be one of:

1. A source-backed density-identification theorem for the original/external
   source measure over the Case 2 source-chart image, with positive bounded
   density.
2. A determinant-chart transport theorem for the endpoint map `Y`, proving
   bounded positive density or domination relative to additive Haar on
   `rawDetChart`.
3. A full local image/coverage theorem plus Jacobian comparison strong enough
   to imply one of the two statements above.

Until one of these is proved, the determinant-side reverse domination and
source-density lower bound must remain explicit hypotheses in downstream A2
finite-integral/prior wrappers.

## Nonclaims

This audit proves no Lean theorem.  It does not construct the original source
prior, identify `sourceImageDensity`, prove positivity or continuity of that
density, prove determinant Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image/source-rank coverage, normal crossings,
pole order, or RLCT extraction.
