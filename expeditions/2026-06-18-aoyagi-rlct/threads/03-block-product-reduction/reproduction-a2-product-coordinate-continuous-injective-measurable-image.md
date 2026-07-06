# A2 product-coordinate continuous/injective measurable-image package

Date: 2026-07-06

Status: Lean proved and verified.

## Claim

For the reduced p.13 fixed-base product-coordinate edge-family map

```text
CedgeProd(x,u),
```

the existing pointwise continuity theorem can be promoted to a product-domain
`ContinuousOn` statement.  It is enough to assume, for every `x` in the base
source set:

```text
ContinuousAt CedgeBase x
```

and the recursive determinant-chart hypotheses for the fixed-base matrix
family obtained from `CedgeBase x`.

Then for any regular-coordinate domain `regularDomain`,

```text
ContinuousOn CedgeProd (source x regularDomain).
```

Combining this with the already-proved residual-readback small-ball injectivity
theorem and Lusin-Souslin gives a local chart package: for every `Rmax > 0`,
there is `R` with `0 < R <= Rmax` such that, on

```text
domain = source x ball(0,R),
```

the map `CedgeProd` is continuous on `domain`, injective on `domain`, and
`CedgeProd '' domain` is measurable.

The same shrink also supports the explicit product readback:

```text
productReadback(E) =
  (baseReadback(residual(E)), regularReadback(E)).
```

On `domain`, `productReadback(CedgeProd z) = z`; on the image
`CedgeProd '' domain`, `productReadback E` lies back in `domain` and
`CedgeProd(productReadback E) = E`.  The continuous-on/measurable-domain
package also gives

```text
AEMeasurable CedgeProd (thetaMeasure.restrict domain)
```

for every source-side measure `thetaMeasure`.

## Calculation

Fix `(x,u)` in `source x regularDomain`.  The existing pointwise theorem gives

```text
ContinuousAt CedgeProd (x,u)
```

from:

```text
ContinuousAt CedgeBase x
```

and the determinant-chart hypotheses at `x`.  Therefore

```text
ContinuousWithinAt CedgeProd (source x regularDomain) (x,u),
```

and hence `ContinuousOn CedgeProd (source x regularDomain)`.

For the small-ball package, the previous residual-readback theorem supplies
`R` with `0 < R <= Rmax` and

```text
Set.InjOn CedgeProd (source x ball(0,R)).
```

The ball is open, hence measurable.  If `source` is measurable and the domain
is Polish/Borel, then

```text
source x ball(0,R)
```

is measurable.  Lusin-Souslin then applies to the continuous injective
restriction:

```text
MeasurableSet (CedgeProd '' (source x ball(0,R))).
```

The pointwise product-readback theorem gives the left inverse on the same
domain because the chosen radius makes `det Ctop(u)` a unit for every
`u in ball(0,R)`.  The right inverse on the image is formal: if
`E = CedgeProd z` with `z in domain`, then

```text
productReadback E = z
```

and therefore `CedgeProd(productReadback E) = E`.

## Lean targets

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_continuousOn_of_forall_continuousAt_base

exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_continuousOn_injOn_measurable_image_of_residualReadback

exists_pos_radius_le_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceChart_readback_package_of_residualReadback
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSourceReadback.lean
```

## Boundary

This is a chart-hypothesis package only.  It does not prove a pushforward
identity, readback domination for an original prior, source/product-coordinate
measure transport, normal crossings, pole order, or RLCT extraction.  It also
does not construct the residual readback or the determinant-chart hypotheses;
those remain explicit inputs.

## Verification

Focused Lean check, focused module build, full local `lake build DLNFibre`,
`scripts/sorries`, `git diff --check`, touched-file marker scan, and direct
axiom probes passed.  The three new declarations report:

```text
[propext, Classical.choice, Quot.sound]
```
