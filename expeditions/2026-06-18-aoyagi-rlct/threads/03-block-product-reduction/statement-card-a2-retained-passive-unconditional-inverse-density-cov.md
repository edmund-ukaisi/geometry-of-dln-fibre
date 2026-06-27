# Statement Card - A2 Retained-Passive Unconditional Inverse-Density COV

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

## Lean Names

```text
nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac
```

## Reproduction

```text
reproduction-a2-retained-passive-unconditional-inverse-density-cov.md
```

## Claim

The retained-passive raw-order chart map pushes additive Haar measure restricted
to the tuple determinant chart to additive Haar measure restricted to the
raw-order source-recursive target chart, weighted by the target-side inverse
Jacobian density

```text
y |-> ENNReal.ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y).
```

The explicit density a.e.-measurability hypotheses from the earlier conditional
theorem are now discharged from forward determinant-density continuity,
target-chart inverse continuity, and openness/null-measurability of the chart
sets.

## Method

The proof first proves continuity of the target-side inverse density:

```text
K(y) = (topologyTupleEdgeRawOrderFDerivAbsDet (topologyTupleEdgeRawOrderInverse y))^-1.
```

At `y in T`, the inverse point lies in `S`, the inverse chart map is
continuous, the forward determinant density is continuous at the inverse
point, and the forward determinant density is positive there.  Therefore
`K` is continuous at `y` by continuity of reciprocal away from zero.

This continuity proves the missing a.e.-measurability obligations for the
conditional inverse-density COV theorem.  The composed and edge-family wrappers
then follow by measure-map composition and map congruence.

## Role

This removes a measure-theoretic bookkeeping hypothesis from the retained-
passive chart-coordinate COV layer.  Downstream uses no longer need to supply
separate a.e.-measurability proofs for the forward density, inverse density,
or composed inverse density.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

Full `DLNFibre` build passed, with pre-existing linter warnings in unrelated
files.  `scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`.  `git diff --check` passed.  Independent xhigh review passed.

## Nonclaims

No explicit determinant formula, source-prior density theorem, original DLN
source pushforward, selected-entry target-image equality, source-rank coverage,
normal-crossing theorem, pole-order theorem, or RLCT theorem is proved here.
