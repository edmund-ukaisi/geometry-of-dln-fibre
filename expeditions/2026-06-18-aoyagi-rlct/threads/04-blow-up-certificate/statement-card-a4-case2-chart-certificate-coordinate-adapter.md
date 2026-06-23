# Statement card - A4 Case 2 chart-certificate coordinate adapter

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`

Name:

- `Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`

## Claim

If a supplied chart certificate `Cnc` has a coordinate `p` whose exponent
arrays match the displayed continuing Case 2 local calculation, then the
A0-facing wrapper around the generic Case 2 exponent-coordinate bridge holds
for `Cnc.exponentData` at `p`.

## Inputs Kept Explicit

- a supplied `Cnc : AoyagiNormalCrossingChartCertificate Param R`;
- a supplied coordinate `p : Fin Cnc.numCharts x Fin Cnc.numCoords`;
- a displayed continuing Case 2 local certificate `cert`;
- the equalities

```text
Cnc.lossExp p.1 p.2 = 1
Cnc.jacobianPriorExp p.1 p.2 =
  card ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1))
```

## Proved

The theorem returns:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge cert Cnc.exponentData p
```

The wrapper delegates to the generic bridge, which provides the active-pair
and finite-ratio consequences.

## Not Proved

No construction of `Cnc`, no construction of `p`, no global A0 chart family,
no chart coverage, no transition regularity, no active-ratio lower bound, no
chart-count theorem, no analytic Jacobian/volume-form theorem, no pole order,
and no RLCT extraction.

## Verification

Initial focused check passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge
```

The focused downstream build passed through the shared-store `scripts/lb`
workflow.  Full build verification is recorded in the review artifact.

## Review

Xhigh reviewer `Boyle` passed the slice with no findings.  Durable review
artifact:
`review-case2-chart-certificate-coordinate-adapter-a4.md`.
