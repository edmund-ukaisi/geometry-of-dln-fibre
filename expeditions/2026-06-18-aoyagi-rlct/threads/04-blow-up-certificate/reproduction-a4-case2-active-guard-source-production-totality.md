# Reproduction - A4 Case 2 active guards for source-production totality

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean.

## Question

The previous produced-branch-data contract used the displayed Case 2 frontier
predicates:

```text
continuing:
  J + 2 <= prefixMinNat n (S + 1)

actual-width stopped:
  n (S + 1) = J + 1

row-exhausted stopped:
  prefixMinNat n S = J + 1
```

These predicates correctly name the finite frontier after a valid selected
pivot.  Are they also the right total guards for
`SelectedEntryAtlasProducedBranchData`?

Answer: not by themselves.  The producer payload fields are total over their
guards.  The stopped equalities alone do not assert that the selected pivot
`(J+1,J+1)` is in the current residual block.  A source-produced payload for a
Case 2 pivot chart must therefore use active-refined guards.

## Active Guard

The displayed Case 2 pivot is valid at old state `(S,J)` when:

```text
J + 1 <= prefixMinNat n (S + 1).
```

This is exactly the existing active guard used by the branch-progress bridge.
Aoyagi pp. 19-22 apply the selected-pivot blow-up calculation under this
condition: the residual block contains the pivot entry that is normalized to
`1`.

## Refined Source-Production Guards

For source production, use:

```text
active-continuing:
  J + 1 <= prefixMinNat n (S + 1)
  and J + 2 <= prefixMinNat n (S + 1)

active actual-width stopped:
  J + 1 <= prefixMinNat n (S + 1)
  and n (S + 1) = J + 1

active row-exhausted stopped:
  J + 1 <= prefixMinNat n (S + 1)
  and prefixMinNat n S = J + 1
```

The first active conjunct is redundant in the continuing branch, but including
it gives all three producer guards the same shape and prevents payload
obligations outside the displayed Case 2 chart.

## Guard Completeness

Assume the active guard:

```text
J + 1 <= prefixMinNat n (S + 1).
```

The existing finite frontier theorem gives:

```text
J + 2 <= prefixMinNat n (S + 1)
or n (S + 1) = J + 1
or prefixMinNat n S = J + 1.
```

Pairing each alternative with the active guard gives:

```text
active-continuing
or active actual-width stopped
or active row-exhausted stopped.
```

Thus the active-refined guards have the same branch-progress coverage on the
active region, without requiring payloads on inactive states.

## Finite Source-Data Packaging

The next useful Lean layer below `SelectedEntryProducedBranchPayload` is finite
source data, not analytic chart production.  The displayed Case 2 source input
contains:

```text
u
residual
active pivot guard
exponent certificates
level invariants
least-value gap
```

From this input, Aoyagi's Case 2 calculation on pp. 19-22 gives three
branch-specific finite packages already represented in Lean:

```text
ContinuingWeightedSuccFollowingFrontierPayload
ActualWidthSourceChartFrontierPayload
RowExhaustedSourceSuffixTransportedPrefixPayload
```

The continuing package is used only under the active-continuing guard.  It
records the weighted successor-following frontier and the concrete recurrence
state after the selected pivot:

```text
pre.case2Succ
  (case2DisplayedSourceChartMap ... (J + 1, J + 1))
```

This recurrence is the same-stage child used by the recurrence-aware progress
bridge.

The actual-width stopped package is used under the active guard plus

```text
n (S + 1) = J + 1.
```

It records the terminal relabelled recurrence over `(S+1,0)` and the supplied
actual-width terminal frontier payload.

The row-exhausted stopped package is used under the active guard plus

```text
prefixMinNat n S = J + 1.
```

The transported-prefix source-suffix version also needs the suffix-domain
condition:

```text
S + 1 <= L.
```

It must therefore be treated as a suffix-refined row-exhausted subcase, not as
data total over every semantic row-exhausted stopped state.  A final-stage
row-exhausted/no-suffix state would need separate terminal data or a branch
invariant excluding it.  This source-suffix package must still remain separate
from actual-width stopping because the terminal source rows and orientation
are different.

These packages are source data for future payload construction.  They are not
the payload itself because they do not include a produced analytic chart,
produced chart point, chart-domain membership, source-domain membership, or
center alignment with the fixed all-pivot atlas context.

They are also recurrence-valued in the displayed coefficient ring `R`: the
selected pivot value produced by the source chart feeds
`pre.case2Succ`.  A final generic
`AoyagiRecurrenceBranchState L n alpha` producer must either specialize
`alpha` to this value type, eventually `ℝ` for the signed-box atlas, or add an
explicit transport from displayed pivot values into `alpha`.

## Source-Production Consequence

The `SelectedEntryAtlasProducedBranchData` record requires:

```text
continuingPayload :
  forall s, continuingGuard s -> payload
actualWidthStoppedPayload :
  forall s, actualWidthStoppedGuard s -> payload
rowExhaustedStoppedPayload :
  forall s, rowExhaustedStoppedGuard s -> payload
```

Using the bare stopped equalities would ask for stopped payloads even when the
Case 2 pivot chart has no active pivot.  That is too broad for a
source-faithful construction.  The active-refined stopped guards are the right
total guards for source production.

## Nonclaims

This slice constructs active-refined guards and finite source-data packages
only.  It does not construct analytic producer payloads, produced charts,
produced points, chart-domain witnesses, source-domain witnesses, atlas
coverage, center alignment, generic-`alpha` transport, final-stage
row-exhausted/no-suffix terminal data, transition regularity,
Jacobian/volume compatibility, normal crossings, pole order, or RLCT.
