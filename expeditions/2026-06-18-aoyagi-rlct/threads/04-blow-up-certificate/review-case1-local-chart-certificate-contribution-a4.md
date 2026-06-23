# Review - Case 1 local chart-certificate contributions

Date: 2026-06-23.

Reviewers: xhigh Lean/API scout `Hooke`; xhigh source/fidelity scout
`Bernoulli`; controller check.

Status: passed for the local finite contribution claim.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`;
- `reproduction-case1-local-chart-certificate-contribution-a4.md`;
- `statement-card-a4-case1-local-chart-certificate-contribution.md`.

Lean names reviewed:

```text
case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary
```

## Findings

No mathematical or source-fidelity issue remains for the local claim.

Both scouts recommended this slice as the safe Case 1 analogue of the Case 2
local summary.  The theorem pair uses the generic
`Case1SelectedEntryExponentCoordinateBridge`, not the A0-facing wrappers, so
the summaries are about each one-chart microcertificate's own exponent data.

The selected-old theorem does not construct the hidden source label behind the
finite `Unit` token.  Any A0-facing use that needs selected-old source
provenance must still use `Case1SelectedOldUnitA0ExponentCoordinateBridge`
and its carried `Case1SelectedOldUnitSuppliedChartFamilyBoundary`.

## Nonclaims Checked

The theorem pair does not construct a global A0 chart family, chart coverage,
a selected-entry atlas, the hidden selected-old source label, source-produced
recurrence/exponent post-data, a Case 1 transition theorem, analytic
Jacobian/volume-form data, analytic unit neighbourhoods, global active-ratio
lower bounds, global chart-count/order data, Aoyagi Theorem 2 pole order,
`theta`, or RLCT extraction.

The local finite order `1` is stated only for each one-chart
microcertificate's own exponent data.  It must not be used as the global pole
order.

## Verification

Controller focused check:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
```

The focused build passed through the shared-store workflow.

Full build, sorry audit, and diff hygiene are recorded in the statement card
and passed:

```text
lean/scripts/lb
lean/scripts/sorries
git diff --check
```

The full build completed successfully with only pre-existing Core/style
warnings.  The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`.
