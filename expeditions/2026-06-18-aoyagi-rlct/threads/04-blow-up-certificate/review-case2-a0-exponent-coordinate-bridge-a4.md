# Review - A4/A0 Case 2 exponent-coordinate bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API reviews passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`
- `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`
- `reproduction-case2-a0-exponent-coordinate-bridge-a4.md`
- `statement-card-a4-a0-case2-exponent-coordinate-bridge.md`

Lean names reviewed:

```text
AoyagiNormalCrossingExponentData.mem_activePairs_of_lossExp_eq_one
AoyagiNormalCrossingExponentData.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
Case2DisplayedContinuingExponentCoordinateBridge
Case2DisplayedContinuingExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two
Case2DisplayedContinuingExponentCoordinateBridge.activePair
Case2DisplayedContinuingExponentCoordinateBridge.ratioAt_eq_centerCard_div_two
Case2DisplayedContinuingA0ExponentCoordinateBridge
Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two
Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair
Case2DisplayedContinuingA0ExponentCoordinateBridge.ratioAt_eq_centerCard_div_two
```

Follow-up hardening split the generic finite bridge from the A0-facing wrapper:
`Case2DisplayedContinuingExponentCoordinateBridge` carries the exponent-array
calculation, while `Case2DisplayedContinuingA0ExponentCoordinateBridge` wraps
it for data intended to represent the full A0 problem.

## Source/Math Review

Reviewer: `Plato the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed that the helper matches Aoyagi PDF pp. 5-6 ratio
arithmetic `(h_j+1)/(2 k_j)` specialized to `k_j=1`, and that the bridge uses
only explicit assumptions on a supplied A0 coordinate:

```text
D.lossExp p = 1,
D.jacobianPriorExp p = erased-center cardinality.
```

The conclusion is only:

```text
p in D.activePairs,
D.ratioAt p = card(case2ResidualBlockPivotEntries n S J) / 2.
```

The review confirmed that no global minimum, order count, chart construction,
analytic Jacobian theorem, or RLCT extraction is claimed.

## Lean/API Review

Reviewer: `Franklin the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed:

- the bridge correctly avoids artificial one-coordinate exponent data;
- the API takes a supplied `D` and supplied coordinate `p`;
- statement strength is narrow and matches the names;
- proof structure delegates ratio arithmetic to A0 helpers and cardinality to
  the existing A4 certificate field;
- import impact is acceptable.

## Verification

Focused checks passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge
```

The focused builds passed through the shared-store `scripts/lb` workflow.

## Boundary

This review does not certify construction of the A0 exponent data `D`, a
coordinate-production theorem for `p`, a global finite minimum, exponent
order, chart production, analytic normal-crossing chart data, analytic
Jacobian/volume-form control, pole order, or RLCT extraction.
