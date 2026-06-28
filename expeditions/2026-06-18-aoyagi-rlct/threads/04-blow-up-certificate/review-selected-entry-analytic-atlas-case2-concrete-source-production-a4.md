# Review - A4 Case 2 concrete selected-entry source production

Reviewer: xhigh `Dewey`.

Date: 2026-06-28.

Verdict: PASS after documentation fix.

## Finding

The Lean theorem

```text
SelectedEntryCase2DisplayedA0SourceProduction.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
```

has the right scope.  Its conclusion is only the concrete
`SelectedEntryCase2DisplayedA0SourceProduction` predicate for

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate n hS hcont.
```

It does not assume an existing `source_production`; it builds the displayed
continuing certificate through

```text
sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily
```

and fills the A0-facing wrapper from

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .localExponentCoordinateBridge_anyChart.
```

## Required Fix Applied

The first review found that the reproduction note incorrectly described
`Case2DisplayedContinuingA0ExponentCoordinateBridge` as carrying a certificate
equality field.  The current Lean API is a one-field wrapper containing only
`toExponentCoordinateBridge`.

The reproduction note was corrected at
`reproduction-selected-entry-analytic-atlas-case2-concrete-source-production-a4.md`
to state that the wrapper is filled by that single field.

## Residual Nonclaims

The arbitrary chart index `c` is an exponent-coordinate adapter in the finite
all-pivot certificate.  It is not source production of every non-displayed
pivot chart.

No analytic atlas coverage, chart regularity, transition regularity, unit
regularity, analytic Jacobian/volume-form compatibility, branch termination,
normal crossings, pole order, or RLCT is proved.
