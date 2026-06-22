# Statement Card - A4 Case 2 Source-Production Obligation Actual-Width Cterm Frontier

## Lean Names

```text
Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceSuffixSuppliedCtermPayload
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_frontier_suppliedCterm
```

## Claim

Given a supplied `SourceProductionObligation` and the actual-width stopped
branch hypothesis

```text
hwidth : n(S+1) = J+1,
```

the actual-width source-chart frontier can be restated with the supplied
terminal matrix `Cterm` on the terminal side:

```text
ActualWidthSourceSuffixSuppliedCtermPayload ... Cterm.
```

## Inputs Kept Explicit

- supplied `SourceProductionObligation`;
- actual-width exhaustion `hwidth`;
- source suffix data `κ`, `hSuffix`, `Ctail`;
- the old source following object `C`.

## Proved

Only the finite rewrite from
`case2DisplayedSourceTerminalOriginalRows C` to the supplied `Cterm`, consuming
the obligation field `actualWidth_Cterm_eq`.

## Not Proved

No construction of `Cterm`, `Csucc`, successor source data, suffixes, charts,
coverage, transition regularity, coordinate post-data, normal crossings, pole
order, termination, or RLCT.
