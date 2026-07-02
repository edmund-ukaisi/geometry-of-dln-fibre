# Reproduction - Theorem 2 Terminal And Regular Sockets Source-Data Rank-Width Removal

Date: 2026-07-02.

Status: controller reproduction; implemented and reviewed.

## Question

After the final-socket rank-width removal, three downstream A6 handoff families
still took an explicit source-range rank-width hypothesis:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The source-data rank-width lemmas can remove this field in the following
natural cases:

- `L=2` terminal counted-datum classifier handoff;
- `L=2` Eq5 terminal-order handoff;
- `L=2` and `ell=1` supplied regular-suspension chart-final handoff.

## Pen-and-paper Derivation

Each existing theorem has the same shape:

```text
Ssrc : AoyagiDefinition3SourceData L ell H r C
hr   : forall s in source range, r <= H s
payload obligations for produced m,data
------------------------------------------------
exists m data, supplied final/chart boundary plus selected-width side data
```

For `L=2`, the source-data classifier gives either repeated-positive or
triangle source data.  Both imply all three source-range reduced widths are
nonnegative, hence `r <= H s` for `s=1,2,3`.

For `ell=1`, every source-range reduced width lies in the selected value set,
and the two selected strict inequalities make the selected values positive.
Thus all source-range reduced widths are nonnegative, hence `r <= H s`.

Substituting the appropriate rank-width proof into the existing rank-width
handoff proves the new wrappers.

## Lean Shape

In `Theorem2TerminalOrderBridge.lean`, add the `L=2` wrappers:

```text
exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_terminalMinimumCountDatumClassifier
exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_terminalMinimumCountDatumClassifier
```

In `Theorem2Eq5TerminalOrderBridge.lean`, add the `L=2` wrappers:

```text
exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

In `Theorem2RegularSuspensionFinalBridge.lean`, add:

```text
exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_suppliedRegularSuspension
exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData_suppliedRegularSuspension
```

Do not add `ell=1` terminal/Eq5 wrappers: those APIs are parametrized by
`n+1`, so `ell=1` would force an awkward `n=0` special socket rather than
removing a natural field from the existing API surface.

## Nonclaims

- No construction of terminal counted-datum classifiers.
- No construction of Eq5 endpoint payloads.
- No construction of regular-suspension chart certificates.
- No branch selection or branch-independent formula.
- No normal-crossing production or RLCT extraction beyond supplied A0
  extraction hypotheses.
