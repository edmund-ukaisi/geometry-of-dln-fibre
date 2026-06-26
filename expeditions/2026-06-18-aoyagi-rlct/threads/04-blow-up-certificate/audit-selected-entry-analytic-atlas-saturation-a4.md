# Audit - selected-entry analytic atlas saturation

Date: 2026-06-26.

Status: xhigh scout `Boole the 3rd`, integrated by controller.  No Lean theorem
is proposed from this audit.

## Verdict

The finite selected-entry chart layer is saturated below the analytic atlas
boundary.  Aoyagi pp. 14-22 support the displayed recursive algebra, selected
entry substitutions, `Q/P` operations, `C' = Q^{-1} C`, and the continue/stop
branch instructions.  They do not define analytic chart domains, chart tokens,
open coverage, analytic overlap maps, analytic Jacobian or volume
compatibility, produced suffix data, or a produced full successor family.

## Current Lean Boundary

`SelectedEntryAnalyticAtlasBoundary` in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean` correctly keeps
these as supplied fields:

- `coverage`;
- `chart_regular`;
- `transition_regular`;
- `unit_regular`;
- `analytic_jacobian_compatible`;
- `source_production`;
- `branch_termination`.

Finite results such as the all-pivot selected-entry coverage theorem,
`SelectedEntryFiniteAffineTransitionRegularFamily`, and selected-entry
principalization/unit facts are finite chart-map algebra.  They do not fill the
analytic fields above.

`SourceProductionObligation` constructors in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` are formula-level socket
fillers.  They are not source production unless a separate source chart,
coverage theorem, and analytic/density compatibility package has produced the
successor data.

## Guardrail

Do not use:

- finite all-pivot selected-entry coverage as `coverage`;
- `SelectedEntryFiniteAffineTransitionRegularFamily` as
  `transition_regular`;
- `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`;
- `SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`;

as fields of `SelectedEntryAnalyticAtlasBoundary` or as evidence that A4 source
production has been proved.

## First Missing Construction

The first non-wrapper A4 construction is an analytic selected-entry atlas
producer:

1. define chart domains and chart tokens;
2. define chart maps on those domains;
3. prove source-neighborhood coverage;
4. prove analytic or regular overlap maps;
5. prove analytic Jacobian/unit compatibility;
6. produce successor/suffix data on each chart;
7. prove branch termination or keep it supplied.

Only after those fields exist should the final A4/A0 sockets be tightened.
