# Statement Card - A2 retained-passive conditional raw-order Haar precomposition

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
```

Added theorem:

```text
map_topologyTupleEdgeRawOrder_comp_eq_withDensity_inverseJacobian
```

Statement shape:

```text
Measure.map pre eta = m.restrict topologyTupleDetChartSet
  ->
Measure.map (fun x => topologyTupleEdgeRawOrder (pre x)) eta =
  (m.restrict topologyTupleRawOrderSourceRecursiveDetChartSet).withDensity
    (fun y => ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y))
```

## Inputs Used

- `nullMeasurableSet_topologyTupleDetChartSet`.
- `continuous_topologyTupleEdgeRawOrder_detChart_subtype`.
- `AEMeasurable.map_map_of_aemeasurable`.
- `map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian`.

## Mathematical Meaning

This is the retained-passive analogue of the product-step conditional
precomposition theorem.  The theorem packages the elementary identity

```text
(Phi o pre)_* eta = Phi_* (pre_* eta)
```

under the hypothesis `pre_* eta = m|S`, then applies the retained-passive
raw-order inverse-Jacobian change of variables.

## Nonclaims

- No passive-theta endpoint topology-tuple Haar transport.
- No source-rank image coverage.
- No original or external DLN source-prior domination.
- No normal crossings, pole order, or RLCT extraction.
