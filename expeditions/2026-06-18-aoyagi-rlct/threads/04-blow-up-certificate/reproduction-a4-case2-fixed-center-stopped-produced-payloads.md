# Reproduction - A4 Case 2 fixed-center stopped produced payloads

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the existing stopped Case 2 all-pivot source-data records be lifted to
`SelectedEntryProducedBranchPayload` constructors?

Answer: yes, for the fixed current residual-block center and for the stopped
subcases already represented by non-placeholder finite source data:

- actual-width stopped;
- row-exhausted terminal-last;
- row-exhausted source-suffix.

This does not produce a single total row-exhausted payload over the weaker
semantic row-exhausted guard.

## Shared Chart Bookkeeping

For a recurrence branch state `s : AoyagiRecurrenceBranchState L n Real`, use
the fixed center

```text
case2ResidualBlockPivotEntries n s.S s.J.
```

Each stopped guard is active-refined, so it contains the active pivot bound

```text
s.J + 1 <= prefixMinNat n (s.S + 1).
```

As in the continuing payload, the produced chart is the displayed pivot chart
obtained through a supplied public chart equivalence:

```text
chartEquiv.symm
  <(s.J + 1, s.J + 1),
    case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
      n s.stage_pos hactive>
```

The produced point is

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
  hcenter chartEquiv producedChart input.u input.residual.
```

The chart-domain and source-domain witnesses are universal in the all-pivot
analytic atlas context.  The payload record ties `producedParam` only to the
chart map at this produced point; it does not add an invariant connecting this
parameter with the finite `producedSourceData` witness.

## Actual-Width Stopped

The actual-width stopped guard is

```text
case2AllPivotActualWidthStoppedGuard s.
```

It contains the active pivot condition and the equality

```text
n (s.S + 1) = s.J + 1.
```

The finite source data is

```text
Case2AllPivotActualWidthStoppedProducedSourceData input C F
```

with constructor

```text
Case2AllPivotActualWidthStoppedProducedSourceData.of_sourceInput hguard.
```

This packages the existing actual-width stopped source-chart frontier payload
and the stage-relabelled terminal recurrence.

## Row-Exhausted Terminal-Last

The terminal-last row-exhausted guard is

```text
case2AllPivotRowExhaustedTerminalLastGuard s.
```

It strengthens the semantic row-exhausted stopped guard with

```text
s.S + 1 = L.
```

The finite source data is

```text
Case2AllPivotRowExhaustedTerminalLastProducedSourceData
  input kappa hguard.2 C Ctail
```

with constructor

```text
Case2AllPivotRowExhaustedTerminalLastProducedSourceData.of_sourceInput
  hguard C.
```

This is the no-suffix terminal-last API/package.  It is intentionally separate
from the source-suffix API/package, but the guards are not claimed to be
exclusive.

The record stores the supplied `C` rows and `Ctail` family as fields, with
definitional equality witnesses back to the constructor parameters.  This is
needed because the frontier theorem itself is proposition-valued; without
storing the supplied data, the source-data structure would erase to `Prop` and
would not be accepted by `SelectedEntryProducedBranchPayload.sourceData`.

## Row-Exhausted Source-Suffix

The source-suffix row-exhausted guard is

```text
case2AllPivotRowExhaustedSourceSuffixGuard s.
```

It strengthens the semantic row-exhausted stopped guard with

```text
s.S + 1 <= L.
```

The finite source data is

```text
Case2AllPivotRowExhaustedSourceSuffixProducedSourceData
  input kappa hguard.2 C Ctail
```

with constructor

```text
Case2AllPivotRowExhaustedSourceSuffixProducedSourceData.of_sourceInput hguard C.
```

This source-suffix package records transported-prefix source data.  It remains
separate as an API from actual-width and terminal-last data, but
`s.S + 1 <= L` overlaps with the terminal-last equality `s.S + 1 = L`; this is
not a disjoint branch decomposition.

As in the terminal-last subcase, the record stores the supplied `C` rows and
`Ctail` family as fields.  This is source data, not a placeholder wrapper.

## Source Support

Aoyagi pp. 19-22 support the displayed Case 2 local calculation: the selected
pivot chart, source substitution by the exceptional coordinate, regular
row/column transformations, transported following factor, cleared successor
block, product identity, and the continue/stop split.  The stopped source-data
records are the repository's finite reproduction of these displayed stopped
frontiers.

The payload constructors add Lean atlas bookkeeping: chart token, chart point,
chart-map equality, and universal domain witnesses.  Aoyagi does not print a
global selected-entry analytic atlas or a total produced-branch-data record.

## Nonclaims

These constructors do not instantiate `SelectedEntryAtlasProducedBranchData`.
They do not prove a total row-exhausted payload over the weaker semantic
row-exhausted guard, stopped-guard exclusivity, recurrence-wide center
alignment, generic coefficient transport, analytic chart coverage, transition
regularity, Jacobian/volume compatibility, normal crossings, pole order, or
RLCT extraction.

## Kill Conditions

Kill or rescope the Lean target if it requires:

- a center not definitionally equal to the current residual-block center;
- a branch-state type varying over centers while the atlas context center is
  fixed;
- using `Unit`, `True`, `PUnit`, `Nonempty`, or `SourceProductionObligation`
  as the payload source data;
- allowing the row-exhausted source-data records to erase to `Prop` by storing
  only proof-valued frontier fields;
- merging actual-width, row-exhausted terminal-last, and row-exhausted
  source-suffix data into one erased stopped witness;
- treating the source-suffix and terminal-last row guards as disjoint;
- treating the stronger terminal-last/source-suffix row guards as a proof of
  total semantic row-exhausted source production;
- generic coefficients without explicit transport from the displayed real
  source chart;
- claims about chart coverage, transition regularity, Jacobian/volume data,
  normal crossings, pole order, or RLCT.
