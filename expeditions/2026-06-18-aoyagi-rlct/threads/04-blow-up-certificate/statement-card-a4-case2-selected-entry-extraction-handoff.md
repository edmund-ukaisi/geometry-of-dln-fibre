# Statement card - A4 Case 2 selected-entry extraction handoff

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis`

## Claim

For the concrete Case 2 residual-block all-pivot finite selected-entry
certificate, if the chart-level normal-crossing extraction hypothesis is
supplied, then the external `lambda` and local `poleOrder` reported by that
hypothesis are

```text
lambda =
  (((prefixMinNat n S - J) * (n(S+1) - J)) : Q) / 2,

poleOrder = 1.
```

## Inputs Kept Explicit

- Case 2 continuation assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- ordered-field hypotheses inherited from the selected-entry certificate;
- the chart-level extraction hypothesis
  `C.ExtractionHypothesis lambda poleOrder`.

## Not Proved

The theorem does not construct the extraction hypothesis, analytic chart
coverage, transition regularity, source production for arbitrary pivots,
successor matrix data, global A0 active-ratio lower bounds, global chart
counts, Aoyagi Theorem 2's pole-order formula, or a global DLN RLCT theorem.

## Verification

Focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Full verification passed:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

## Review

Xhigh independent review passed with no blocking findings.  Durable artifact:
`review-case2-selected-entry-extraction-handoff-a4.md`.
