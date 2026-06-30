# Statement Card - A2 Case 2 small-ball product readout package

## Claim

For the concrete Case 2 endpoint p.13 product source chart, there is a positive
regular-coordinate radius `R <= Rmax` such that every passive-theta base point
`theta` and every `u in ball 0 R` satisfy one shared readout package:

```text
regularCoordinateMap(productSourceChart(theta,u)) = u
residualCoordinateMap(productSourceChart(theta,u))
  =
residualCoordinateMap(sourceChart theta)
regularReadback(productSourceChart(theta,u)) = u
selectedInverseReadout(productSourceChart(theta,u))
  =
selectedInverseReadout(sourceChart theta)
sourceReadback(productSourceChart(theta,u)) has the p.13 product fields
```

Public Lean name:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- the p.13 product-coordinate source-dependent family over that chart;
- a positive radius cap `Rmax`;
- the generic fixed-base small-ball product readout package;
- the pointwise regular-readback and selected inverse-readout theorems.

## Output

Lean returns `R > 0`, `R <= Rmax`, and for every `theta` and every
`u in ball 0 R` the five facts above.  The source-readback field component is

```text
A1passive = 1
F2        = first decoded F2(u), then 0
A3passive = 0
C         = residualBlock(fixedBase(sourceChart theta))
Ctop      = decoded Ctop(u)
F3        = decoded F3(u)
```

## Proof Shape

Specialize

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readout_package
```

at `M := 0` and the concrete passive-theta endpoint source chart.  This gives
the determinant-unit certificate, raw coordinate-map readouts, and
source-readback field equalities.  The same `hCtop` then feeds the two
Case 2-specific pointwise APIs:

```text
case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
```

## Nonclaims

This does not recover the full passive-theta point from
`productSourceChart(theta,u)`.  The inverse readout is only the selected
residual readout, and source-readback resets retained passive fields to
canonical values.  The theorem proves no source-image coverage, source-prior
transport, Haar/Jacobian density identity, normal crossings, pole order, or
RLCT extraction.

## Status

Focused direct Lean check passed for
`DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`;
focused module build and full local `lake build DLNFibre` passed;
`scripts/sorries` reports `0 sorry, 0 #exit, 0 native_decide, 0 axiom`;
`git diff --check` passed; direct axiom probe reports only
`[propext, Classical.choice, Quot.sound]`.
