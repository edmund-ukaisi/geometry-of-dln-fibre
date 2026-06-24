# Statement card - A4 selected-entry analytic atlas boundary

Status: Lean boundary structure landed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-boundary-a4.md`.

Independent review:
`Descartes the 2nd` returned PASS, with the source wording tightened in the
reproduction before this statement card was written.

## Target

Introduce a boundary structure named

```text
SelectedEntryAnalyticAtlasBoundary
```

or a more Aoyagi-specific name if the Lean file demands it.  The structure
should sit above the finite selected-entry certificate layer and below the
A0/A6 final socket.  It should record exactly the data that the finite
selected-entry all-pivot certificates do not prove but a normal-crossing atlas
producer must supply.

## Existing Inputs

Lean already has finite selected-entry certificate data:

```text
AoyagiNormalCrossingChartCertificate
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero
```

These give chart maps, formal chart points, local coordinates, monomial loss
and formal Jacobian/prior determinant identities, pointwise unit witnesses,
finite exponent arrays, active-ratio identities, chart-count identities, and
finite exponent order for the selected-entry center contribution.

They do not prove analytic chart coverage, regularity, transition regularity,
source-produced successor/suffix data, analytic Jacobian/volume-form
compatibility, global normal crossings, termination, pole order, or RLCT.

## Required Fields

The boundary should include fields for:

- an atlas-produced or explicitly supplied
  `AoyagiNormalCrossingChartCertificate`, not one inferred merely from the
  finite selected-entry certificate;
- coverage of the relevant source neighborhood or branch;
- regular/analytic chart maps on the stated domains;
- regular transition maps on overlap domains;
- nonvanishing/regular unit control on chart domains;
- analytic Jacobian/volume-form compatibility;
- source-produced successor, terminal, or suffix data, or an explicit recursive
  handoff to a later producer;
- branch and termination coverage for the blow-up recursion.

## Nontriviality Test

The structure must not be inhabitable by any of the existing trivial or
formula-level constructors alone:

```text
SelectedEntryChartFamilyBoundary.exists_trivial
Case2ResidualBlockChartFamilyBoundary.exists_trivial
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack
```

If the proposed Lean structure can be filled by one of these constructors plus
`simpa`, the statement is an API wrapper and should be rejected.

## Lean Slice

Lean now adds `SelectedEntryAnalyticAtlasBoundary` in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.  It is a
data-bearing supplied boundary with fields:

```text
chartCertificate
coverage
chart_regular
transition_regular
unit_regular
analytic_jacobian_compatible
source_production
branch_termination
```

It also provides the projection

```text
SelectedEntryAnalyticAtlasBoundary.exponentData
```

to the carried chart certificate's finite exponent data.  No constructor is
provided from the finite selected-entry certificate, the trivial chart-family
boundaries, or `SourceProductionObligation`.

A later theorem may project the supplied `chartCertificate` to the existing A0
final socket, but should not claim analytic extraction beyond the explicit
`ExtractionHypothesis` citation boundary.

Focused verification:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

passed on 2026-06-24.

## Kill Conditions

- Do not call finite selected-entry map coverage analytic atlas coverage.
- Do not call finite cocycle/inverse formulas transition regularity.
- Do not call formal pivot-first determinants analytic volume-form control.
- Do not infer source-produced `Csucc`, `Cterm`, `C'^(S+1)`, or suffixes from
  `SourceProductionObligation`.
- Do not claim normal crossings, pole order, termination, or RLCT.
