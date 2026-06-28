# A2 retained-passive local formal/product-density COV

## Claim

Let `S` be the retained-passive determinant chart, `T` the raw-order
source-recursive determinant chart, and

```text
Phi = topologyTupleEdgeRawOrder.
```

The previous checkpoint proves, for the formal determinant density and for the
solved-`A1` product density `J`,

```text
map Phi ((m.restrict S).withDensity J) = m.restrict T.
```

The retained-passive local-source measure socket may therefore use the same
local chart identity with `J` in place of the abstract Frechet determinant
`topologyTupleEdgeRawOrderFDerivAbsDet`.

## Reproduction

Fix a downstream source chart

```text
psi : TopologyTuple rho kappa' R -> alpha
```

which is a.e.-measurable for `m.restrict T`.  If `eta_J` denotes
`(m.restrict S).withDensity J`, then the formal/product COV gives

```text
map Phi eta_J = m.restrict T.
```

The composite pushforward is therefore

```text
map (psi o Phi) eta_J
  = map psi (map Phi eta_J)
  = map psi (m.restrict T).
```

The first equality is only pushforward associativity; the Lean proof needs the
a.e.-measurability of `Phi` for `eta_J`, obtained from continuity of `Phi` on
`S` plus absolute continuity of `eta_J` with respect to `m.restrict S`.  The
second equality is the new formal/product raw-order COV.

For the realized retained-passive local source, set

```text
mu = map sourceChart (m.restrict T),
localSource = paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

The realization hypothesis says that for every `y in T`, the edge family read
from `sourceChart y` is the raw-order edge family of `y`.  The already proved
local-source membership lemma then gives

```text
sourceChart y in localSource
```

for `m.restrict T`-a.e. `y`.  Hence

```text
mu.restrict localSource = mu.
```

Combining this with the composite pushforward identity gives

```text
mu.restrict localSource
  = map sourceChart (m.restrict T)
  = map (sourceChart o Phi) eta_J.
```

For the canonical fixed-base source chart, the chart is the retained-passive
source-edge-family decoder applied after `topologyTupleEdgeRawOrderInverse`.
On `T`, the inverse lands in `S`, the source chart is continuous on `T`, and
the raw-order inverse identity gives the required realization hypothesis.  Thus
the canonical theorem is an instance of the realized theorem.

## Boundary

This is still a local retained-passive chart-measure identity.  It does not
construct an original source prior, identify signed-box source densities, prove
normal crossings, compute pole order, or extract an RLCT.
