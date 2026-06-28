# A2 retained-passive canonical product-density residual handoff

Status: controller reproduced; Lean target selected.

## Claim

The canonical retained-passive p.13 local source can use the computed
solved-`A1` product Jacobian density as the source-side measure for the
generic residual-source handoff.  This removes the explicit source-measure
pushforward equality from the residual handoff, but leaves the chart-side
residual positivity and finite-integral facts as hypotheses.

## Product density as a local unit

Let

```text
S = topologyTupleDetChartSet
Jprod(z) = retainedPassiveFormalRawOrderJacobianProductAbsDetAt z
Jactual(z) = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

The determinant checkpoint proved, separately in the zero-tail and positive-tail
cases, that for every `z in S`,

```text
Jactual(z) = Jprod(z).
```

Packaging the two cases by induction on the number of retained-passive edges
gives the all-`M` identity

```text
Jprod(z) = Jactual(z)   for z in S.
```

The set `S` is open.  Therefore near any base point `z0 in S`, the two
functions are eventually equal.  Since the actual Jacobian density is already
known to be continuous and strictly positive at every point of `S`, `Jprod`
inherits:

```text
Jprod(z0) > 0,
ContinuousAt Jprod z0,
exists epsilon K > 0 with epsilon <= Jprod(z) <= K near z0.
```

After any parametrisation `Y` continuous at `a0` with `Y(a0) in S`, the same
neighborhood bounds pull back to

```text
epsilon <= Jprod(Y(a)) <= K       near a0.
```

This is only a local-unit API for the named product density.  It is not a
normal-crossing or monomial-density statement.

## Residual handoff

Let

```text
rho = Fin (finrank R U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0
T = topologyTupleRawOrderSourceRecursiveDetChartSet
sourceChart(y)
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y))
localSource = paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
mu = Measure.map sourceChart (m.restrict T)
nu = (m.restrict S).withDensity (fun z => ofReal (Jprod z)).
```

The canonical product-density COV proves exactly

```text
mu.restrict localSource
  = Measure.map (fun z => sourceChart (topologyTupleEdgeRawOrder z)) nu.
```

The generic theorem `residualSourceHypotheses_of_measure_map` says that such a
map identity transfers:

```text
0 < residual(chart z)              for nu-a.e. z,
int^- z, ofReal(residual(chart z)^(-t)) dnu < infinity
```

to the retained-passive local source:

```text
0 < residual(x)                    for mu.restrict localSource-a.e. x,
residualNegPowerIntegrableOn localSource mu t.
```

Thus the canonical product-density COV removes the supplied `hmap` field from
the residual-source handoff.  The composed chart is a.e.-measurable because
`topologyTupleEdgeRawOrder` is a.e.-measurable on the weighted determinant-chart
measure, its map is `m.restrict T` by the same COV, and the canonical
`sourceChart` is already a.e.-measurable on `m.restrict T`.  The theorem does
not prove the chart-side residual positivity or finite integral.

## Boundary

This checkpoint is source-side retained-passive raw-coordinate measure
plumbing.  It does not construct an original source prior, identify a
selected-entry signed-box density, prove a monomial lower bound, prove normal
crossings, compute pole order, or extract an RLCT.
