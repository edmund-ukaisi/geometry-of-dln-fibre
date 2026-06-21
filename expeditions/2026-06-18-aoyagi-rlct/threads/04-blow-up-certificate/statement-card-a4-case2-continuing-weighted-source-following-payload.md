# Statement Card - A4 Case 2 Continuing Weighted Source-Following Payload

## Lean Names

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.ContinuingWeightedSourceFollowingFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages.continuingWeighted`

## Claim

In the displayed Case 2 continuing branch, the source-chart frontier package
can expose the paper-`C'` weighted lower-row handoff together with next-center
nonemptiness and finite residual-center principalization.

## Proved

Lean combines:

- next residual-center nonemptiness under
  `J+2 <= prefixMinNat n (S+1)`;
- the existing paper-`C'` source-following weighted lower-row handoff with
  corrected supplied post-data;
- the finite center facts for the displayed source-coordinate chart map:
  pivot value membership, divisibility by `u`, and center ideal
  `Ideal.span {u}`;
- a new `continuingWeighted` field in the source-chart frontier package.

## Assumed

The common displayed Case 2 source-chart hypotheses remain explicit: pre
exponent certificates, level invariants, least-value gap, residual
chart-family boundary, and the continuing guard
`J+2 <= prefixMinNat n (S+1)`.

## Cited

None in Lean.  This is finite matrix algebra and finite center bookkeeping.

## Deferred

Full successor products including the pivot row, chart construction, chart
coverage, arbitrary-pivot coverage, source production of `C'^(S+1)`,
chart-produced post-data, successor chart-family construction, transition
invariance, termination, terminal relabeling, Jacobian arithmetic, normal
crossings, pole order, RLCT extraction, and repair of the printed Case 2 vector
mismatch.

## Review

- Focused Lean build passed for `DLNFibre.DLN.Aoyagi.BlowupArithmetic`.
- Independent xhigh reviewer `Boyle` found no formalisation or math issues.
  The documentation visibility risk he noted was addressed in this slice.
