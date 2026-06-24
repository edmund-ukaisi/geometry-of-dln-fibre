# Review - A4 selected-entry transition cocycle

Date: 2026-06-24.

Reviewer: `Beauvoir the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the current selected-entry transition cocycle slice:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-transition-cocycle-a4.md`;
- `statement-card-a4-selected-entry-transition-cocycle.md`.

The review checked denominator hypotheses, source/middle/target pivot use,
chart-point versus raw residual equality, Case 2 specialization, and theorem
comments for source overreach.

## Findings

No blocking findings.

The reviewer confirmed that the generic denominator-nonzero theorem derives
the middle-to-target denominator nonzero from normalized source coordinates
`x_q != 0` and `x_r != 0`.  The generic cocycle theorem proves normalized
coordinate algebra only:

```text
(x_i/x_q)/(x_r/x_q) = x_i/x_r.
```

The generic chart-family cocycle is correctly stated as chart-point equality.
Its residual comparison is only over `center.erase targetPivot`, so it does
not assert equality of arbitrary ambient residual functions.

The Case 2 specialization obtains source, middle, and target pivots from
`finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)` and keeps
the nonzero hypotheses in the `case2SourceSelectedNormalizedMapOfMem` form.

The theorem comments and documentation do not claim analytic transition
regularity, chart coverage, global normal crossings, pole order, RLCT
extraction, or repair of Aoyagi's printed-vector ambiguity.

## Gates

The reviewer ran and passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Controller gates also passed before ledger integration:

```text
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

## Minimal Repair

No Lean repair was needed.  The only reviewer-requested change was to update
the reproduction and statement-card verification bookkeeping after the Lean
formalisation landed.
