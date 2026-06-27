# Reproduction - A2 Retained-Passive Inverse Jacobian Local Bounds

Status: controller reproduced; Lean target selected.

## Scope

This note records the local-unit argument for the target-side inverse
retained-passive raw-order Jacobian density

```text
K(y) = topologyTupleEdgeRawOrderInverseJacobianDensity y.
```

Here `K(y) = J(g(y))^-1`, where `g` is the raw-order inverse and `J` is the
actual forward Frechet-derivative absolute determinant.  The argument does not
compute `J`, does not identify it with the formal determinant, and does not
construct a source measure.

## Pen-and-paper argument

Let

```text
y0 in topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The existing retained-passive inverse-density layer proves:

```text
1. K is continuous at y0;
2. K(y0) > 0.
```

The same elementary neighborhood argument as for the forward density gives:

```text
epsilon <= K(y) <= C
```

for all `y` in a neighborhood of `y0`, with `epsilon > 0` and `C > 0`.

If `Y : alpha -> TopologyTuple` is continuous at `a0` and `Y(a0) = y0`, the
neighborhood pulls back along `Y`, giving

```text
epsilon <= K(Y(a)) <= C
```

eventually near `a0`.

## Lean target

The retained-passive inverse-density API should mirror the existing
product-step inverse-density API:

```lean
topologyTupleEdgeRawOrderInverseJacobianDensity_comp_pos_of_mem_rawSourceChart
exists_pos_eventually_le_topologyTupleEdgeRawOrderInverseJacobianDensity_nhds
exists_pos_eventually_topologyTupleEdgeRawOrderInverseJacobianDensity_le_nhds
exists_pos_eventually_bounds_topologyTupleEdgeRawOrderInverseJacobianDensity_comp
```

These are bounded-unit lemmas for later density transport.  They are not
normal-crossing, pole-order, or RLCT statements.
