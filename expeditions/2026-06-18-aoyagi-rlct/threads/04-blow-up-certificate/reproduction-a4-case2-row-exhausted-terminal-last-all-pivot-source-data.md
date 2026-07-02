# Reproduction - A4 Case 2 row-exhausted terminal-last all-pivot source data

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean.

## Question

The all-pivot finite source-data layer now has a row-exhausted source-suffix
record under:

```text
active row-exhausted guard
and S + 1 <= L.
```

This packages the transported-prefix source-suffix payload.  It is not the
terminal-last row-exhausted package, because Aoyagi's terminal-last case uses
the identity that the suffix after the next layer is empty.

## Terminal-Last Guard

The terminal-last row-exhausted subcase is:

```text
active row-exhausted guard
and S + 1 = L.
```

The equality supplies the suffix-domain inequality by `le_of_eq`, but the
payload itself is different from the source-suffix payload.  It is the
existing displayed Case 2 terminal-last frontier:

```text
RowExhaustedTerminalLastSourceChartFrontierPayload
```

exposed through:

```text
SourceChartFrontierBoundaryPackages.rowExhaustedStopped
```

## Construction

Given the displayed all-pivot source input:

```text
u
residual
active pivot guard
exponent certificates
level invariants
least-value gap
```

and the terminal-last guard, construct the displayed frontier package:

```text
sourceChartMap_frontierBoundaryPackages_withoutChartFamily
```

Then call its `rowExhaustedStopped` field with:

```text
hSuffix := le_of_eq hLast
hLast   := hLast
hrow    := row-exhausted equality from the guard
```

This produces the terminal-last transported-prefix source-chart frontier
payload.  The terminal-last payload remains separate from the source-suffix
payload and from actual-width stopping.

## Remaining Gap

This covers the `S + 1 = L` terminal-last row-exhausted subcase.  The source
data layer still must not be read as a full semantic row-exhausted payload for
every state satisfying only the bare row-exhausted equality.  A final producer
will need a complete row-domain split, a branch invariant excluding any
remaining case, or additional source data.

## Nonclaims

This slice constructs only terminal-last finite source data below analytic
producer payloads.  It does not construct `SelectedEntryProducedBranchPayload`,
`SelectedEntryAtlasProducedBranchData`, produced charts, produced points,
chart-domain witnesses, source-domain witnesses, center alignment,
generic-`alpha` transport, transition regularity, Jacobian/volume
compatibility, normal crossings, pole order, or RLCT.
