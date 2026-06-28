# Review: A2 retained-passive canonical chart residual readout

Reviewer: xhigh `Zeno the 3rd`.

Verdict: PASS.  No blocking findings.

## Scope

Reviewed the checkpoint adding:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualProduct
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualFactorProduct
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

and the matching reproduction, statement card, and root ledger updates.

## Findings

- The Lean statements are correctly scoped as pointwise determinant-chart
  readouts.  The hypothesis `z ∈ topologyTupleDetChartSet` is explicit in both
  theorem statements.
- The first proof uses determinant-chart membership to place
  `topologyTupleEdgeRawOrder z` in the raw-order source-recursive determinant
  chart before invoking the canonical source-chart realisation theorem.
- The residual-factor theorem genuinely needs determinant-chart membership: it
  converts the hypothesis into `(ofTopologyTuple z).detChart` and then uses
  `sourceReadback_edgeMatrix_eq`, whose API requires that hypothesis.
- The raw-order identities used are the right ones:

```text
mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
sourceReadback_edgeMatrix_eq
```

- No overclaim of residual positivity, residual integrability, normal
  crossings, pole order, or RLCT was found.  The Lean docstrings,
  reproduction, statement card, and ledgers keep these as explicit nonclaims or
  remaining frontier.
- The ledgers correctly describe the result as source-moving only in the
  readout sense and leave zero-locus/a.e. positivity/negative-power
  integrability, normal-crossing or monomial work, and prior/density transport
  as remaining work.

## Minor note

The first `..._eq_residualProduct` theorem could be generalized from
`z ∈ topologyTupleDetChartSet` to the weaker condition that
`topologyTupleEdgeRawOrder z` lies in the raw-order source-recursive chart.
This is not a blocker: the determinant-chart statement is the intended
chart-side form, and the residual-factor theorem needs determinant-chart
membership.

## Checks

The reviewer did not rerun Lean to avoid writing build artifacts.  The
reviewer ran read-only `git diff --check` and focused marker greps; no
review-blocking issue appeared.
