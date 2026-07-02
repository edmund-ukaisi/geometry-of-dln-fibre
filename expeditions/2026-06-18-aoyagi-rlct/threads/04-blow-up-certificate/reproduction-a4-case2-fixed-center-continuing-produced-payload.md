# Reproduction - A4 Case 2 fixed-center continuing produced payload

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the existing all-pivot source-data layer be lifted one step to an actual
`SelectedEntryProducedBranchPayload` for the continuing Case 2 branch?

Answer: yes, for one fixed residual-block center and the displayed
continuing chart.  This is a local payload constructor, not the full
recurrence-wide `SelectedEntryAtlasProducedBranchData` field.

## Fixed Center

At a recurrence branch state `s : AoyagiRecurrenceBranchState L n R`, the
natural Case 2 all-pivot center is

```text
case2ResidualBlockPivotEntries n s.S s.J.
```

For the continuing branch we have the active-refined guard

```text
case2AllPivotContinuingGuard s.
```

This guard contains the active pivot condition

```text
s.J + 1 <= prefixMinNat n (s.S + 1)
```

and the continuing condition

```text
s.J + 2 <= prefixMinNat n (s.S + 1).
```

The active condition implies the displayed pivot `(s.J+1, s.J+1)` belongs to
the residual-block center.  Hence the displayed chart index is the
inverse, under a supplied chart equivalence, of that center element.  This
avoids relying on the private canonical equivalence used internally by the
normal-crossing file.

## Produced Chart And Point

Use the context

```text
selectedEntryAllPivotAnalyticAtlasContext
  (case2ResidualBlockPivotEntries_nonempty_of_cont n s.stage_pos hactive)
  chartEquiv
```

where `hactive` is the active pivot bound extracted from the continuing
guard and `chartEquiv` is any public equivalence from the finite chart index
type to the residual-block center.

The produced chart is the displayed top-left pivot chart:

```text
chartEquiv.symm
  ⟨(s.J + 1, s.J + 1),
    case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
      n s.stage_pos hactive⟩
```

The produced point is the corresponding source chart point:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
  hcenter chartEquiv producedChart input.u input.residual
```

This point is in the chart domain because the all-pivot context uses
universal chart domains.  The produced parameter is the chart map applied to
this point, and it is in the source domain because the source domain is also
universal.

The payload record ties this parameter to the chart map at the produced point.
It does not add a separate invariant tying `producedParam` to the
`producedSourceData` package, although the constructor uses the same
`input.u` and `input.residual` in both places.

## Source Data

The finite source-data component is already available:

```text
Case2AllPivotContinuingProducedSourceData.of_sourceInput hguard
```

It packages the displayed Case 2 source chart scalar `u`, residual
coordinates, exponent/level certificates, the continuing weighted
successor-following frontier payload, and the same-stage child recurrence.

This is the branch-specific `sourceData` of the produced payload.  It is not a
placeholder and does not use `SourceProductionObligation`.

## Source Support

Aoyagi pp. 19-22 support the displayed selected-pivot calculation: the pivot
chart, the source substitution by the exceptional coordinate, regular
row/column transformations, the transported following factor, the cleared
successor block, and the continue/stop split.  The existing Lean source-data
record is the repository reproduction of that displayed continuing branch.

The payload wrapper itself adds Lean atlas bookkeeping: a chart token, chart
point, chart-map equality, and universal domain witnesses.  These are not
printed by Aoyagi as a global atlas construction; they are the finite
all-pivot selected-entry chart certificate already built in the expedition.

## Nonclaims

This slice does not construct the full
`SelectedEntryAtlasProducedBranchData`.  It does not cover actual-width
stopped or row-exhausted stopped payloads.  It does not solve the
recurrence-wide fixed-center problem, generic-`alpha` transport, semantic
row-domain totality, analytic transition regularity, Jacobian/volume
compatibility, normal crossings, pole order, or RLCT extraction.

The current Lean constructor is specialized to real-valued recurrence states,
matching the displayed all-pivot source-data layer.

## Kill Conditions

Kill or rescope the Lean target if it needs any of the following:

- a fixed center that is not definitionally the current state center;
- a branch-state type varying over centers while the context center is fixed;
- `sourceData := Unit`, `True`, `PUnit`, or a `Nonempty` wrapper;
- `SourceProductionObligation` as the payload source-data witness;
- a generic coefficient type without a real transport into the displayed
  source-data recurrence;
- identifying a lower-tail, source-current row formula, or successor
  following factor with full source production of `C'^(S+1)`;
- any claim about stopped branches, all-branch totality, normal crossings,
  pole order, or RLCT.
