# Review - A2 Retained-Passive Local-Source Coverage

Date: 2026-06-26.

Reviewer: Carson the 3rd, xhigh.

Verdict: pass after wording correction.

## Finding

The theorem is sound and useful for the local-measure handoff shape, but its
nontrivial content is the ambient neighborhood statement:

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource ... in nhds x0.
```

The final source-rank inclusion is rank-insensitive.  The theorem returns

```text
Ulocal subset paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

and the inclusion

```text
Ulocal inter paperEndpointFixedBaseSourceRankStratum ... subset
  Ulocal inter paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

follows from this subset.  This should be described as a determinant-chart
preimage neighborhood plus a handoff-shaped inclusion, not as a theorem about
source-rank openness.

## Checks

The index convention is correct: the module uses vertices `Fin (M + 2)` and
edges `Fin (M + 1)`, matching the existing fixed-base API with `N := M + 1`.

The local source is not `sourceStratum`; it is the preimage of
`sourceRecursiveDetChartSet` under the fixed-base edge-matrix map.

No false claim was found for source-rank openness, measure transport,
Jacobian, normal crossings, pole order, or RLCT.

The import placement is reasonable: the new module imports the boundary
source-rank layer and retained-passive topology layer, and `DLNFibre.lean`
imports it after `RetainedPassiveCoordinatesTopology`.
