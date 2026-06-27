# Reproduction - A2 Retained-Passive Raw-Order Local-Source COV Bridge

Date: 2026-06-27.

Status: pen-and-paper reproduction for a conditional bridge from the
raw-order retained-passive change-of-variables theorem to the fixed-base
retained-passive p.13 local source.

This is independent of the quiver paper.  It does not prove determinant-density
continuity, inverse-density measurability, original source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT.

## Coordinate Objects

Fix the p.13 fixed-base endpoint data `W,B,U0,hU0`.  Put

```text
rho = Fin (finrank_R U0),
kappa' = throughSubspaceEndpointComplementIndex(reverseVertex W, reverseEdge W B, U0).
```

Let

```text
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
Phi = topologyTupleEdgeRawOrder,
J(z) = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

The retained-passive weighted COV theorem gives

```text
Measure.map Phi ((m.restrict S).withDensity (ofReal o J)) = m.restrict T.
```

The composed COV theorem says the same after applying any downstream
a.e.-measurable map `psi` out of the raw target chart:

```text
Measure.map (psi o Phi) ((m.restrict S).withDensity (ofReal o J))
  =
Measure.map psi (m.restrict T).
```

## Realization Into The Local Source

The fixed-base retained-passive p.13 local source is

```text
localSource =
  {x | edgeMatrixOfReverseEdges(Cedge x) in sourceRecursiveDetChartSet}.
```

A raw target point `y in T` means

```text
edgeFamilyOfRawOrderTuple y in sourceRecursiveDetChartSet.
```

Suppose a realization map

```text
sourceChart : TopologyTuple rho kappa' R -> alpha
```

and a continuous edge-family parameterization `Cedge : alpha -> edges` satisfy
the pointwise realization identity on `T`:

```text
edgeMatrixOfReverseEdges(Cedge (sourceChart y))
  =
edgeFamilyOfRawOrderTuple y.
```

Then for every `y in T`, the displayed equality transports the membership of
`edgeFamilyOfRawOrderTuple y` in `sourceRecursiveDetChartSet` to membership of
`sourceChart y` in `localSource`.

Thus, if

```text
eta = m.restrict T,
mu = Measure.map sourceChart eta,
```

and `sourceChart` is a.e.-measurable with respect to `eta`, the existing
map-restrict handoff gives

```text
mu.restrict localSource = mu.
```

## Composition

Apply the composed COV theorem with `psi = sourceChart`:

```text
Measure.map (sourceChart o Phi)
  ((m.restrict S).withDensity (ofReal o J))
 =
Measure.map sourceChart (m.restrict T)
 =
mu.
```

Combining this equality with `mu.restrict localSource = mu` gives

```text
mu.restrict localSource
 =
Measure.map (sourceChart o Phi)
  ((m.restrict S).withDensity (ofReal o J)).
```

## Boundary

The theorem constructs only the local-source restriction equality for a
measure already defined as the raw-target pushforward through a supplied
realization map.  It does not identify the original DLN source measure, does
not prove that a selected-entry signed-box target image is `T`, does not prove
measurability of inverse Jacobian densities, and does not prove any analytic
normal-crossing or RLCT result.
