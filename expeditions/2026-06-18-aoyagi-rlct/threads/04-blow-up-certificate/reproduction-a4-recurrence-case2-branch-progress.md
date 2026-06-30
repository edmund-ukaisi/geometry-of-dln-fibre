# Reproduction - A4 recurrence-aware Case 2 branch progress

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the displayed Case 2 selected-entry branch-progress bridge be lifted from
the support-only branch state to the recurrence-aware branch state?

The existing support-only bridge chooses the continuing child `(S,J+1)` and
uses support growth to prove a decreasing step.  The recurrence-aware branch
state has one extra field:

```text
recurrence : IntroducedLabelRecurrenceState L n S J alpha.
```

Therefore a continuing child over `(S,J+1)` cannot be constructed from the
branch state alone.  It needs supplied child recurrence data:

```text
childRecurrence s h :
  IntroducedLabelRecurrenceState L n s.S (s.J+1) alpha.
```

## Source Check

Aoyagi's displayed Case 2 calculation, PDF pp. 19-22, blows up the selected
block, performs the regular `Q` and `P` transformations, and then states that
if

```text
J+1 <= M(S+1) = min{M(S), M^(S+1)}
```

then the inductive statement continues with `J` increased by one.  If the
inequality fails, the displayed matrix degenerates to the stopped
stage-handoff form.

For this Lean slice, the source-backed branch-domain movement is only the
continuing Case 2 move:

```text
(S,J) -> (S,J+1).
```

The recurrence data over the child domain is not produced here.  It remains a
supplied datum, because this slice does not construct the chart/source payload
whose coordinates would justify the recurrence update.

## Finite Calculation

Let

```text
s : AoyagiRecurrenceBranchState L n alpha.
```

Use the active Case 2 pivot-validity guard

```text
s.J + 1 <= prefixMinNat n (s.S + 1).
```

Assume the supplied source-production guards cover that active region:

```text
continuingGuard s
or actualWidthStoppedGuard s
or rowExhaustedStoppedGuard s.
```

For each continuing branch, assume:

```text
hbound s h :
  s.J + 1 <= prefixMinNat n (s.S + 1),

childRecurrence s h :
  IntroducedLabelRecurrenceState L n s.S (s.J+1) alpha.
```

Then the selected child is

```text
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
  s (childRecurrence s h).
```

The existing combined progress theorem gives

```text
AoyagiRecurrenceBranchState.progressStep L n alpha
  (sameStageChildWithRecurrence s (childRecurrence s h)) s
```

from `hbound s h`.

## Nonclaims

This constructs no recurrence data, source-production payload, branch guard,
terminal payload, chart, analytic atlas field, normal crossings, pole order, or
RLCT data.  It only packages the supplied continuing-child recurrence data and
the existing finite recurrence-aware progress theorem into
`SelectedEntryAtlasBranchProgressData`.
