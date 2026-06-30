# Reproduction - A4 selected-entry branch progress bridge

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the selected-entry analytic-atlas producer interface be connected to the
introduced-label termination kernel without constructing branch source
production?

Answer: yes, but only as a compatibility layer.  A continuing branch must name
the child state it intends to recurse into in a separate branch-progress
record, and that same record can prove the child is a decreasing step for a
supplied termination relation.

## Source-Facing Calculation

Aoyagi PDF pp. 19-22 describe the displayed Case 2 branch after selecting the
top-left residual entry.  The continuing alternative advances the same stage:

```text
(S,J)  -->  (S,J+1).
```

The stopped alternatives do not recurse through a same-stage child:

```text
n(S+1) = J+1              actual next-width stopped branch
M(S) = J+1                current-prefix row-exhausted stopped branch
```

where `M(S)` is represented in Lean by `prefixMinNat n S`.

The earlier progress kernel proves that the same-stage child strictly grows
the introduced-label support under the displayed pivot-validity bound

```text
J+1 <= prefixMinNat n (S+1),
```

and hence under the stronger continuing guard

```text
J+2 <= prefixMinNat n (S+1).
```

## Interface Reproduction

The source-production record remains source-production data.  The separate
progress record names:

```text
activeGuard : BranchState -> Prop
guards_complete :
  forall s, activeGuard s ->
    continuingGuard s or actualWidthStoppedGuard s or rowExhaustedStoppedGuard s
continuingChild :
  forall s, continuingGuard s -> BranchState
continuing_child_step :
  forall s h, termination.step (continuingChild s h) s
```

This child is not placed inside the branch payload's existing `branchState`
field, because that field is already the state whose branch is being handled,
and it is not placed in `SelectedEntryAtlasProducedBranchData` either.  For
stopped branches no child is introduced.

```text
SelectedEntryAtlasBranchProgressData
```

It consumes a supplied `SelectedEntryAtlasProducedBranchData` and a supplied
`SelectedEntryBranchTerminationData`.  This prevents a formula-level
source-production wrapper from pretending to fill termination.

## Displayed Case 2 Bridge

For branch states

```text
AoyagiIntroducedLabelBranchState L n
```

the termination relation is:

```text
step child parent := remaining L n child < remaining L n parent.
```

The initial state is `(1,0)`, requiring `1 <= L`.

The active guard is displayed pivot validity:

```text
s.J + 1 <= prefixMinNat n (s.S + 1).
```

If the supplied source-production guards cover this active guard, and a
supplied continuing guard implies either the pivot-validity bound or the
displayed continuing guard, the progress record chooses the continuing child

```text
AoyagiIntroducedLabelBranchState.case2SameStageChild s,
```

and proves it is a decreasing step.

## Nonclaims

This does not construct `SelectedEntryAtlasProducedBranchData`, branch payloads,
source data, terminal rows, suffixes, chart domains, atlas coverage, transition
regularity, normal crossings, pole order, or RLCT.  It does not assert stopped
guard exclusivity and does not attach fake decreasing children to stopped
branches.
