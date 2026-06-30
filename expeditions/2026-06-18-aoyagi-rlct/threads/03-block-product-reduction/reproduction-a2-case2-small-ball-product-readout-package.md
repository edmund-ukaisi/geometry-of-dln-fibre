# A2 Case 2 small-ball product readout package

This note records the finite-coordinate calculation behind the Case 2
small-ball product-readout package.  The setting is only Aoyagi's p.13
regular-suspension chart, specialized to the two-edge retained-passive Case 2
endpoint source chart.  No quiver-paper input is used.

Fix the endpoint source chart

```text
sourceChart theta =
  case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e theta
```

and form the source-dependent p.13 product-coordinate family

```text
productSourceChart(theta,u) =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    W₂ B₂ U₀ hU₀ sourceChart (theta,u).
```

The regular Euclidean variable `u` decodes the three p.13 blocks

```text
F2(u), Ctop(u), F3(u)
```

where `Ctop(0) = I`.  Since determinant is continuous, there is a radius
`0 < R <= Rmax` such that every `u` in the Euclidean ball `ball(0,R)` has
`IsUnit det(Ctop(u))`.  This single determinant-unit witness is exactly the
hypothesis needed by all pointwise readout lemmas already proved.

For any passive-theta base point `theta` and any such `u`, the pointwise
raw coordinate-map readout lemma first gives

```text
regularCoordinateMap(productSourceChart(theta,u)) = u
residualCoordinateMap(productSourceChart(theta,u))
  =
residualCoordinateMap(sourceChart theta).
```

The pointwise regular readback lemma then gives

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback(productSourceChart(theta,u)) = u.
```

The pointwise selected inverse-readout lemma gives

```text
case2PassiveThetaEndpointInverseReadout(productSourceChart(theta,u))
  =
case2PassiveThetaEndpointInverseReadout(sourceChart theta).
```

Finally, the pointwise source-readback field theorem gives the retained-passive
canonicalization formula.  If `Ebase` and `Eprod` are the fixed-base matrix
families associated to `sourceChart theta` and `productSourceChart(theta,u)`,
and if

```text
C(p) = residualBlock(Ebase, last, p),
data = sourceReadback(Eprod),
```

then

```text
data.A1passive = 1
data.F2        = first F2(u), then 0
data.A3passive = 0
data.C         = C
data.Ctop      = Ctop(u)
data.F3        = F3(u).
```

The package is useful because downstream callers no longer have to choose
separate determinant neighborhoods for the raw coordinate-map readouts,
regular readback, selected inverse readout, and source-readback field facts.

Boundary.  The package does not recover the full passive-theta point from
`productSourceChart(theta,u)`.  The selected inverse readout is only the
selected residual readout, and `sourceReadback` deliberately resets retained
passive fields to canonical values.  The package proves no source-image
coverage, source-prior transport, Haar/Jacobian density identity, normal
crossings, pole order, or RLCT extraction.
