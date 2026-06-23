# Statement card - A4 Case 1 local chart-certificate contributions

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`

Names:

- `case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`

## Claim

The two displayed Case 1 local selected-entry microcertificates each
contribute a single active coordinate with local ratio

```text
(1 + J1 * (n(S+1)-J)) / 2.
```

For each microcertificate's own finite exponent data, the local finite
minimum is that ratio, the unique chart has count `1` at that ratio, the
minimum-coordinate count is `1`, and the local finite exponent order is `1`.

## Inputs Kept Explicit

- selected-old local certificate:
  `case1SelectedOldCenterSqFormalJacobianChartCertificate n S J J1`;
- displayed row-strip local certificate:
  `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate n S hJ1 hcol`;
- the displayed row-strip assumptions `hJ1 : 1 <= J1` and
  `hcol : J + 1 <= n(S+1)`.

## Proved

Each theorem bundles:

```text
Case1SelectedEntryExponentCoordinateBridge ... Cnc.exponentData ((0),(0))
Cnc.exponentData.ratioAt ((0),(0)) = q
Cnc.exponentData.exponentMinimum = q
Cnc.exponentData.countInChartAtRatio q 0 = 1
Cnc.exponentData.minCountInChart 0 = 1
Cnc.exponentData.exponentOrder = 1
```

where

```text
q = (1 + J1 * (n(S+1)-J)) / 2.
```

## Not Proved

No global A0 chart family, no chart coverage, no selected-entry atlas, no
construction of the hidden selected-old source label, no source-produced
recurrence or exponent post-data, no Case 1 transition theorem, no analytic
Jacobian/volume-form theorem, no global active-ratio lower bound, no global
chart-count/order theorem, no pole order, no `theta`, and no RLCT extraction.

## Verification

Focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
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

Xhigh Lean/API scout `Hooke` and xhigh source/fidelity scout `Bernoulli`
recommended this as the next safe local slice.  Durable review artifact
`review-case1-local-chart-certificate-contribution-a4.md`.
