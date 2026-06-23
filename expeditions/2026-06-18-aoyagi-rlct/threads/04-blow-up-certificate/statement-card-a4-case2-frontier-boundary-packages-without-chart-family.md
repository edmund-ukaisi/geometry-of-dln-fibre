# Statement card - A4 Case 2 frontier packages without chart family

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData_withoutChartFamily`
- `sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`
- `sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`
- `sourceChartMap_frontierBoundaryPackages_withoutChartFamily`
- compatibility wrapper `sourceChartMap_frontierBoundaryPackages`

## Claim

The displayed Case 2 source-chart frontier implication package can be
constructed without a caller-supplied `ChartRegular`,
`TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary`.

The continuing fields use direct finite displayed-pivot algebra and corrected
post-data.  The stopped fields keep the already accepted branch implications;
the proof discharges the older stopped-helper chart-family API internally
using the canonical `True`-predicate boundary, so no chart-family data is
requested from callers.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- `J+1 <= prefixMinNat n (S+1)`;
- branch hypotheses for the package fields;
- old exponent certificates, level/least-value bridge, and least-value gap;
- source-chart variables `u` and `residual`;
- supplied following factors or suffix products in the stopped fields.

## Proved

- The unweighted continuing source-following product plus corrected
  exponent/level/gap post-data no longer needs a chart-family argument.
- The weighted continuing source-following payload plus finite residual-center
  principalization no longer needs a chart-family argument.
- The successor-following notation adapter has a chart-family-free constructor.
- The whole `SourceChartFrontierBoundaryPackages` bundle now has a
  chart-family-free constructor.
- `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` now
  consumes the chart-family-free package constructor.

## Not Proved

No affine atlas, chart coverage, transition regularity, source production of
`Csucc` or `C'^(S+1)`, suffix production, chart-produced corrected post-data,
analytic Jacobian theorem, normal crossings, pole order, RLCT extraction,
termination theorem, stopped-branch exclusivity, or repair of the printed
Case 2 vector mismatch.

In the row-exhausted branch, terminal rows remain transported prefix rows;
they are not original rows unless actual-width exhaustion is separately
supplied.

## Verification

Focused and full builds passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The no-sorry audit reported zero `sorry`, `#exit`, `native_decide`, and
`axiom` hits.

## Review

Xhigh math/fidelity scout and xhigh Lean API scout passed the boundary.  See
`review-case2-frontier-boundary-packages-without-chart-family-a4.md`.
