# Statement card - A4 Case 2 local chart-certificate contribution

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`

## Claim

For the displayed continuing Case 2 source certificate, the local
selected-entry one-chart certificate contributes a coordinate with ratio

```text
card(case2ResidualBlockPivotEntries n S J) / 2.
```

For this local microcertificate's own finite exponent data, the local minimum
is the same ratio, the unique chart has count `1` at that ratio, the
minimum-coordinate count is `1`, and the local finite exponent order is `1`.

## Inputs Kept Explicit

- the displayed continuation hypotheses `hS` and `hcont`;
- the source-side finite certificate
  `Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate`;
- the local selected-entry microcertificate
  `case2DisplayedCenterSqFormalJacobianChartCertificate n hS hcont`.

## Proved

The theorem bundles:

```text
Case2DisplayedContinuingExponentCoordinateBridge cert Cnc.exponentData ((0),(0))
Cnc.exponentData.ratioAt ((0),(0)) = q
Cnc.exponentData.exponentMinimum = q
Cnc.exponentData.countInChartAtRatio q 0 = 1
Cnc.exponentData.minCountInChart 0 = 1
Cnc.exponentData.exponentOrder = 1
```

where

```text
Cnc = case2DisplayedCenterSqFormalJacobianChartCertificate n hS hcont
q = card(case2ResidualBlockPivotEntries n S J) / 2.
```

## Not Proved

No global A0 chart family, no chart coverage, no analytic
Jacobian/volume-form theorem, no source production of successor charts or
suffixes, no global active-ratio lower bound, no global chart-count theorem,
no pole order, and no RLCT extraction.

## Verification

Focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Full verification passed:

```text
lean/scripts/lb
lean/scripts/sorries
git diff --check
```

The full build completed successfully with only pre-existing Core/style
warnings.  The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`.

## Review

Xhigh Lean/API scout `Gauss` and xhigh source/fidelity scout `Heisenberg`
passed the local finite contribution claim.  Durable review artifact:
`review-case2-local-chart-certificate-contribution-a4.md`.
