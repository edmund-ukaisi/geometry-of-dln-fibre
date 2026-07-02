# Reproduction - A4 all-pivot producer recurrence termination

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the all-pivot selected-entry producer stop taking branch termination as a
separate supplied input once recurrence termination data has already been
proved?

The existing all-pivot shell has the form:

```text
selectedEntryAllPivotSuppliedAnalyticAtlasProducer
  hcenter chartEquiv hradius BranchState sourceProduction termination
```

It fills the all-pivot source coverage, chart regularity, transition
regularity, unit regularity, and Jacobian/volume fields.  It still asks for:

```text
sourceProduction :
  SelectedEntryAtlasProducedBranchData
    (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
    BranchState

termination :
  SelectedEntryBranchTerminationData
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := Real) hcenter chartEquiv)
    BranchState
```

The recurrence progress bridge already supplies the second datum when

```text
BranchState = AoyagiRecurrenceBranchState L n alpha
```

and the initial recurrence state over `(S,J) = (1,0)` is supplied.

## Adapter Calculation

Use exactly the same chart certificate in both places:

```text
C =
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate
    (K := Real) hcenter chartEquiv
```

The recurrence termination bridge gives:

```text
selectedEntryRecurrenceBranchTerminationData
  C L n alpha hL initialRecurrence
```

whose fields are:

```text
step = AoyagiRecurrenceBranchState.progressStep L n alpha
step_wellFounded =
  AoyagiRecurrenceBranchState.progressStep_wellFounded L n alpha
initial = (1, 0, proof 1 <= 1, hL, initialRecurrence)
```

Substitute this termination datum into the all-pivot shell:

```text
selectedEntryAllPivotSuppliedAnalyticAtlasProducer
  hcenter chartEquiv hradius
  (AoyagiRecurrenceBranchState L n alpha)
  sourceProduction
  (selectedEntryRecurrenceBranchTerminationData
    C L n alpha hL initialRecurrence)
```

No other field changes.  Source coverage, chart regularity, transition
regularity, unit regularity, and Jacobian/volume compatibility still come from
the all-pivot shell.  Source production still comes from the supplied
`sourceProduction` input.

## Boundary Cases

- `hcenter : center.Nonempty` and `chartEquiv : Fin center.card ~= center`
  are unchanged from the all-pivot shell; the adapter does not alter chart
  coordinates.
- `hL : 1 <= L` is exactly the proof needed for the initial branch stage
  `(S,J) = (1,0)`.
- `initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 alpha` is not
  constructed here.  It is the remaining recurrence-initialization input.
- The branch state is recurrence-aware.  The adapter does not claim anything
  for an arbitrary `BranchState`.

## Nonclaims

This does not construct source-production payloads, branch guards, continuing
children, stopped-branch terminal payloads, successor or suffix source data,
normal crossings, pole order, or RLCT extraction.

It only removes one redundant supplied input: the all-pivot producer no longer
needs a separately supplied `termination` argument when the branch state is the
recurrence-aware state and initial recurrence data is available.

## Kill Conditions

- If the chart certificate passed to
  `selectedEntryRecurrenceBranchTerminationData` differs from the certificate
  used by the all-pivot producer shell, the adapter is ill-typed or incoherent.
- If `sourceProduction` is hidden or constructed by the adapter, the statement
  overclaims.
- If `initialRecurrence` is dropped, the initial recurrence field of the
  branch state is unsupported.
- If the result is described as normal-crossing extraction or final RLCT
  computation, the statement overclaims.
