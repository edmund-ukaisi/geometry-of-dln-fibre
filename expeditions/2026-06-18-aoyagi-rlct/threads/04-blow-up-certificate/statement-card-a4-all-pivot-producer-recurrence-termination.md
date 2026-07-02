# Statement card - A4 all-pivot producer recurrence termination

Date: 2026-07-02.

## Statement

Add an all-pivot selected-entry producer adapter that fills the producer's
branch-termination field from the recurrence-aware finite progress relation.

Lean name:

```text
selectedEntryAllPivotSuppliedAnalyticAtlasProducerWithRecurrenceTermination
```

The adapter consumes:

```text
hcenter : center.Nonempty
chartEquiv : Fin center.card ~= center
hradius : forall i, 0 < radius i
L : Nat
n : Nat -> Nat
alpha : Type
hL : 1 <= L
initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 alpha
sourceProduction :
  SelectedEntryAtlasProducedBranchData
    (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
    (AoyagiRecurrenceBranchState L n alpha)
```

and returns:

```text
SelectedEntrySuppliedAnalyticAtlasProducer (center -> Real) Real
```

## Dependencies

- `selectedEntryAllPivotSuppliedAnalyticAtlasProducer`
- `selectedEntryRecurrenceBranchTerminationData`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate`
- `AoyagiRecurrenceBranchState`
- `IntroducedLabelRecurrenceState`

## Nonclaims

No source-production data, branch guard coverage, continuing-child
construction, stopped-branch terminal payloads, successor or suffix production,
normal crossings, pole order, or RLCT is proved.  The adapter only discharges
the all-pivot producer's termination input in the recurrence-aware branch-state
case.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-all-pivot-producer-recurrence-termination.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-all-pivot-producer-recurrence-termination.md
```
