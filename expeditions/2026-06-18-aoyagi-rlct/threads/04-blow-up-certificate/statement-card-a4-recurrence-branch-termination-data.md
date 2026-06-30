# Statement card - A4 recurrence branch termination data

Date: 2026-06-30.

## Statement

Add a selected-entry termination-data adapter for the recurrence-aware branch
progress relation.

Lean name:

```text
selectedEntryRecurrenceBranchTerminationData
```

The adapter consumes:

```text
C : AoyagiNormalCrossingChartCertificate Param R
L : Nat
n : Nat -> Nat
alpha : Type
hL : 1 <= L
initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 alpha
```

and returns:

```text
SelectedEntryBranchTerminationData C (AoyagiRecurrenceBranchState L n alpha).
```

## Dependencies

- `SelectedEntryBranchTerminationData`
- `AoyagiRecurrenceBranchState.progressStep`
- `AoyagiRecurrenceBranchState.progressStep_wellFounded`
- `IntroducedLabelRecurrenceState`

## Nonclaims

No selected-entry source-production data, branch guard coverage, continuing
child construction, terminal payloads, chart construction, full analytic-atlas
branch termination theorem, normal crossings, pole order, or RLCT is proved.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-recurrence-branch-termination-data.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-recurrence-branch-termination-data.md
```
