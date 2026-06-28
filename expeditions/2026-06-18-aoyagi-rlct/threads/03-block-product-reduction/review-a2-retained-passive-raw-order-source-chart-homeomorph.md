# Review: A2 retained-passive raw-order source-chart homeomorphism

Reviewer: xhigh `Raman the 3rd`.

Verdict: PASS.  No findings.

The reviewer checked that the new homeomorphisms are scoped to reduced
fixed-base retained-passive data, with
`rho = Fin (Module.finrank K U0)` and the endpoint complement index, and that
the target is the fixed-base source edge-family subtype.

Checked points:

- `detChart_topologyTupleDetChartSet_homeomorph`.
- `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph`.
- `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply`.

The apply theorem correctly exposes the forward map as the public raw-order
source chart on the underlying value.  The docs and ledgers are precise that
this is only reduced fixed-base local inverse/continuity bookkeeping, with no
source-rank coverage, measure transport, new Jacobian theorem,
positivity/integrability, normal crossings, pole order, or RLCT claim.
