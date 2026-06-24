# Review - Selected-entry analytic atlas boundary

Date: 2026-06-24.

Reviewer: Descartes the 2nd, xhigh independent checker.

Verdict: PASS.

## Scope

Reviewed
`reproduction-selected-entry-analytic-atlas-boundary-a4.md` against the
existing Lean interfaces

```text
AoyagiNormalCrossingChartCertificate
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero
```

and the A4 source-production audits.

## Findings

The reproduction is source-faithful as a boundary contract and does not claim a
new theorem.  It correctly separates the finite selected-entry certificates
from the missing analytic atlas and source-production data.

The inventory of `AoyagiNormalCrossingChartCertificate` matches the Lean fields
in `NormalCrossingInterface.lean`.  The description of
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate` is correctly
finite bookkeeping only, and the ratio/minimum/order facts match the existing
selected-entry certificate lemmas.  The Case 2 residual-block certificate and
displayed-overlap microcertificate contribution are also described at their
actual finite scope.

The "do not add another wrapper" direction is consistent with the A4 audits and
with the trivial/formula-level Lean APIs:

```text
SelectedEntryChartFamilyBoundary.exists_trivial
Case2ResidualBlockChartFamilyBoundary.exists_trivial
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack
```

## Tightening Applied

The reviewer requested two wording fixes before the statement card:

- phrase Aoyagi PDF pp. 5-6 as the Hironaka normal-crossing formula for
  `K(pi(u))` and the prior/Jacobian factor, not as a literal "squared error"
  quotation;
- make clear that a "produced `AoyagiNormalCrossingChartCertificate`" in the
  future boundary must be atlas-produced or explicitly supplied, not inferred
  from the finite selected-entry certificate alone.

Both fixes were applied to the reproduction before writing
`statement-card-a4-selected-entry-analytic-atlas-boundary.md`.

## Remaining Risk

The next Lean structure should be supplied-boundary only unless it contains
real fields for coverage, transition regularity, analytic unit/Jacobian control,
and source-produced successor/suffix data.  A constructor filled by the finite
selected-entry certificate alone would overclaim.
