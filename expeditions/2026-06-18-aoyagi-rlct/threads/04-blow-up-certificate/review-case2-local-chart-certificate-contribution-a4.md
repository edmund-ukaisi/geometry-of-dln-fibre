# Review - Case 2 local chart-certificate contribution

Date: 2026-06-23.

Reviewers: xhigh Lean/API scout `Gauss`; xhigh source/fidelity scout
`Heisenberg`; controller check.

Status: passed for the local finite contribution claim.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-local-chart-certificate-contribution-a4.md`;
- `statement-card-a4-case2-local-chart-certificate-contribution.md`.

Lean name reviewed:

```text
case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary
```

## Findings

No mathematical or formalisation issue remains for the local claim.

`Gauss` observed that the minimal bridge was already present as
`case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
The new summary theorem is therefore acceptable only because it bundles
nearby local facts without changing the scope: the bridge, the local ratio,
the local minimum, the local ratio-count, the local minimum-count, and the
local finite order.

`Heisenberg` confirmed that the theorem uses the generic
`Case2DisplayedContinuingExponentCoordinateBridge`, not the A0-facing wrapper,
and so does not present this one-chart microcertificate as the full A0 data.
The source certificate carries the finite determinant/cardinality equality
used by the bridge.  The direct ratio conjunct is proved through
`B.ratioAt_eq_centerCard_div_two`, so the proof path points back to the
source-certificate bridge rather than only to the local ratio lemma.

## Nonclaims Checked

The theorem does not construct a global A0 chart family, selected-entry atlas,
chart coverage, source-produced successor charts or suffixes, analytic
Jacobian/volume-form data, transition regularity, global active-ratio lower
bounds, global chart-count/order data, pole order, or RLCT extraction.

The local finite minimum and local order are stated only for
`case2DisplayedCenterSqFormalJacobianChartCertificate`'s own exponent data.
They must not be used as Aoyagi Theorem 2's global minimum or pole order.

## Verification

Controller focused check:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
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
