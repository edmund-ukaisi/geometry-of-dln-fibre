# Statement card - A6 Case 2 chart-final boundary bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2ChartFinalBridge.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`

## Claim

A supplied continuing Case 2/A0 exponent-coordinate bridge can be carried into
the chart-final Theorem 2 boundary once the chart certificate, selected-width
provenance, chart-level A0 extraction hypothesis, Case 2/Theorem 2 lambda
equality, active-ratio lower bound, and ratio-count order witnesses are all
supplied.

## Proved

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc Lthm ell H r cuts m data lambda poleOrder
```

## Not Proved

No construction of `Cnc`, `cert`, `p`, or `c`; no chart production or coverage;
no unit nonvanishing; no active-ratio lower-bound proof; no chart-count proof;
no selected-width provenance proof; no analytic extraction theorem; no pole
order; and no RLCT extraction.

## Verification

Focused and full gates passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Case2Theorem2ChartFinalBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reported only pre-existing Core linter warnings.

## Review

Xhigh source/math reviewer `Epicurus the 2nd` passed the wrapper as
mathematically faithful but only a small API handoff.  Xhigh Lean/API reviewer
`Tesla the 2nd` passed the module placement, import shape, theorem statement,
and proof route with no required fixes.

Durable review artifact:
`review-case2-theorem2-chart-final-bridge-a6.md`.
