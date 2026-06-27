# Reproduction - A2 Retained-Passive Actual Jacobian Local Unit After Composition

Status: controller reproduced; Lean target selected.

## Scope

This note records the elementary local-unit argument for the actual
retained-passive raw-order Jacobian density

```text
J(z) = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

It uses the true Frechet derivative density already proved in Lean.  It does
not identify this density with the formal determinant formula, and it does not
claim a monomial Jacobian formula.

## Pen-and-paper argument

Let `Y : alpha -> TopologyTuple` be continuous at `a0`, and assume

```text
Y(a0) in topologyTupleDetChartSet.
```

The existing analytic retained-passive layer proves two facts at determinant
chart points:

```text
1. J is continuous at Y(a0);
2. J(Y(a0)) > 0.
```

Therefore there is an `epsilon > 0` and a neighborhood `N1` of `Y(a0)` such
that

```text
epsilon <= J(z)       for z in N1.
```

There is also a `K > 0` and a neighborhood `N2` of `Y(a0)` such that

```text
J(z) <= K             for z in N2.
```

Continuity of `Y` at `a0` pulls back both neighborhoods.  On the intersection
of the two resulting neighborhoods of `a0`,

```text
epsilon <= J(Y(a)) <= K.
```

Thus the actual retained-passive Jacobian density is a positive bounded unit
after any continuous source parametrisation through a determinant-chart point.

## Lean target

The Lean theorem should compose the existing neighborhood bounds:

```lean
exists_pos_eventually_bounds_topologyTupleEdgeRawOrderFDerivAbsDet_comp
```

This is intended as source-density infrastructure for downstream
local-measure handoffs.  It is intentionally weaker than, and independent of,
the future formal/actual absolute determinant comparison.
