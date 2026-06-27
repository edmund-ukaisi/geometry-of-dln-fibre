# Reproduction - A2 Retained-Passive Unconditional Inverse-Density COV

Date: 2026-06-27.

Status: pen-and-paper reproduction for removing the explicit
a.e.-measurability hypotheses from the retained-passive inverse-density
chart-coordinate change of variables.  This uses the previously proved
forward `C^1` density continuity.

## Setup

Let

```text
S = topologyTupleDetChartSet
T = topologyTupleRawOrderSourceRecursiveDetChartSet
Phi = topologyTupleEdgeRawOrder
g = topologyTupleEdgeRawOrderInverse
J(z) = topologyTupleEdgeRawOrderFDerivAbsDet z
K(y) = topologyTupleEdgeRawOrderInverseJacobianDensity y = (J(g y))^-1.
```

The existing conditional theorem already proves

```text
map Phi (m.restrict S) = (m.restrict T).withDensity (ofReal K)
```

provided the forward density `ofReal J`, the target inverse density `ofReal K`,
and the composed density `ofReal (K o Phi)` are a.e.-measurable on the
appropriate restricted chart measures.

## Target-Side Inverse Density Continuity

Take `y0 in T`.  The raw-order inverse chart theorem gives `g y0 in S`.
The topological inverse theorem gives `g` is continuous at `y0`.  The previous
`C^1` checkpoint gives `J` is continuous at `g y0`.  Hence `J o g` is
continuous at `y0`.

The determinant-unit/positivity theorem gives

```text
0 < J(g y0).
```

Therefore the reciprocal `(J o g)^-1` is continuous at `y0`, by ordinary
continuity of inverse away from zero.  This is exactly continuity of `K` at
`y0`.

## A.E.-Measurability Inputs

The sets `S` and `T` are open, hence null-measurable for any Borel-space
measure.  On `S`, the forward density `ofReal J` is a.e.-measurable because
`J` is continuous at every chart point and `ENNReal.ofReal` is continuous.

On `T`, the inverse density `ofReal K` is a.e.-measurable by the continuity
argument above and `ContinuousOn.aemeasurable0`.

For the composed density on `S`, the forward chart map is continuous on `S`
and maps `S` into `T`.  Composing the target-side continuity of `ofReal K` at
`Phi z` with the continuous-within-at forward chart map at `z` gives
continuity within `S` of `ofReal (K o Phi)`, hence a.e.-measurability on
`m.restrict S`.

These three derived hypotheses are exactly the hypotheses consumed by the
existing conditional inverse-density COV theorem, so the unconditional theorem
is just a wrapper around the conditional result.

## Downstream Composition

Once the unweighted source restricted measure has been identified with the
inverse-density target measure, the generic downstream map wrapper follows by
the usual `Measure.map` associativity theorem for a.e.-measurable maps.  The
edge-family decoder specialization is then only `Measure.map_congr` plus the
raw-order readback identity.

## Lean Scope

The Lean checkpoint adds:

```text
nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac
```

## Nonclaims

This proves an unconditional chart-coordinate inverse-density transport theorem
for Haar measure restricted to the retained-passive determinant chart.  It
does not compute an explicit determinant formula, identify an original DLN
source prior, prove selected-entry target-image equality, prove source-rank
coverage, produce normal crossings, compute a pole order, or extract an RLCT.
