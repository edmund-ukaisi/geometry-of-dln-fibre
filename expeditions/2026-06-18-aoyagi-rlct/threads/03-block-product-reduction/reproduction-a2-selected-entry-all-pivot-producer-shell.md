# Reproduction - A2 selected-entry all-pivot producer shell

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before review.

## Question

The all-pivot selected-entry chart family now has, over the same shared
universal-domain context:

```text
selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
```

the source-coverage, chart-regularity, unit-regularity, transition-regularity,
and Jacobian/volume fields required by
`SelectedEntrySuppliedAnalyticAtlasProducer`.  Can these proved analytic fields
be assembled into that producer record without pretending that source
production or branch termination has been constructed?

Answer: yes.  The assembly should take the two remaining non-analytic fields as
explicit inputs:

```text
sourceProduction :
  SelectedEntryAtlasProducedBranchData ctx BranchState

termination :
  SelectedEntryBranchTerminationData C BranchState
```

where

```text
C =
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate
    (K := ℝ) hcenter chartEquiv

ctx =
  selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv.
```

## Assembly Check

The producer fields are filled as follows:

```text
chartCertificate              := C
BranchState                   := BranchState
atlasContext                  := ctx
source_coverage               := selectedEntryAllPivotAnalyticSourceCoverageData
chart_regular                 := selectedEntryAllPivotAnalyticChartRegularData
transition_regular            := selectedEntryAllPivotAnalyticTransitionRegularData
unit_regular                  := selectedEntryAllPivotAnalyticUnitRegularData
analytic_jacobian_compatible  := selectedEntryAllPivotAnalyticJacobianVolumeData
source_production             := sourceProduction
branch_termination            := termination
```

The Jacobian/volume field requires a positive selected-entry signed-box radius:

```text
radius : center → ℝ
∀ i, 0 < radius i.
```

No mathematical calculation is added here.  This is a coherence assembly: the
point is that the analytic fields all refer to the same `ctx`, so the producer
record can be assembled once the genuine branch source-production and
termination data are available.

## Source Fidelity

Aoyagi PDF pp. 15-22 support the selected-entry coordinate calculation used by
the underlying all-pivot analytic fields.  This shell itself is expedition
interface bookkeeping: it records that the proved analytic data are coherent.
It does not attribute branch production or termination to the paper.

## Kill Conditions

- Any analytic field uses a context other than
  `selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`.
- The shell constructs `SelectedEntryAtlasProducedBranchData` or
  `SelectedEntryBranchTerminationData` internally.
- The shell is described as proving source production, branch termination,
  normal-crossing extraction, pole order, or RLCT.
