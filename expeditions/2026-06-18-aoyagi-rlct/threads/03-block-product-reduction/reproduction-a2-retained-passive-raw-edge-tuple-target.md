# Reproduction - A2 Retained-Passive Raw Edge Tuple Target

Date: 2026-06-26.

Status: pen-and-paper reproduction and implemented target-coordinate layer.
No measure or derivative theorem is claimed by this note.

## Question

The retained-passive tuple source map now has type

```text
TopologyTuple rho kappa R ->
  forall p, Matrix (rho Sum kappa p.succ) (rho Sum kappa p.castSucc) R.
```

Mathlib's additive-Haar change-of-variables theorem used in the existing
one-step p.13 measure file is stated for an endomap.  The next target is
therefore a raw-order coordinate representation of the edge-family codomain
that has the same product type as the source tuple.

This representation must be named for what it is: it is a raw block readout of
edge matrices, not a retained-passive coordinate readback.

## Raw Edge Tuple

For an edge family

```text
E p : Matrix (rho Sum kappa p.succ) (rho Sum kappa p.castSucc) R,
```

write its four blocks as

```text
A1raw_p = top-left(E p)
A2raw_p = upper-right(E p)
A3raw_p = lower-left(E p)
A4raw_p = lower-right(E p).
```

The raw target tuple is packed into the existing `TopologyTuple` shape by
putting endpoint blocks into the endpoint slots:

```text
A1passive slot p   := A1raw_(p+1)      for p : Fin M
F2 slot p          := A2raw_p          for p : Fin (M+1)
A3passive slot p   := A3raw_p          for p : Fin M
C slot p           := A4raw_p          for p : Fin (M+1)
Ctop slot          := A1raw_0
F3 slot            := A3raw_last.
```

The inverse map reconstructs edge matrices by

```text
edge 0:
  fromBlocks Ctop F2_0 A3passive_0 C_0      if M > 0,
  fromBlocks Ctop F2_0 F3 C_0               if M = 0,

interior edge p = q+1:
  fromBlocks A1passive_q F2_p A3passive_p C_p

last edge:
  fromBlocks A1passive_last F2_last F3 C_last.
```

Lean should express this uniformly with `Fin.cases` for the top-left family
and `Fin.snoc` for the lower-left family:

```text
rawA1 z := Fin.cases z.Ctop z.A1passive
rawA3 z := Fin.snoc z.A3passive z.F3
edgeFamilyOfRawOrderTuple z p :=
  fromBlocks (rawA1 z p) (z.F2 p) (rawA3 z p) (z.C p).
```

Conversely:

```text
edgeFamilyRawOrderTuple E :=
  (fun p => top-left(E p.succ),
   fun p => upper-right(E p),
   fun p => lower-left(E p.castSucc),
   fun p => lower-right(E p),
   top-left(E 0),
   lower-left(E last)).
```

The two inverse identities are elementary block identities:

```text
edgeFamilyOfRawOrderTuple (edgeFamilyRawOrderTuple E) = E
edgeFamilyRawOrderTuple (edgeFamilyOfRawOrderTuple z) = z.
```

They use only `fromBlocks_toBlocks`, `toBlocks_fromBlocks_*`,
`Fin.cases_zero`, `Fin.cases_succ`, `Fin.snoc_castSucc`, and
`Fin.snoc_last`.

## Endomap For Future Jacobian

The retained-passive source map can then be represented as the endomap

```text
topologyTupleEdgeRawOrder z :=
  edgeFamilyRawOrderTuple (topologyTupleEdgeMatrix z)
```

with type

```text
TopologyTuple rho kappa R -> TopologyTuple rho kappa R.
```

This is the target-coordinate map for future derivative work.  It is not the
identity on the determinant chart, and it does not recover retained-passive
coordinates from an arbitrary edge family.  It is simply the source edge
family written in raw block coordinates in a product order compatible with the
source tuple.

## Expected Lean Scope

The first Lean layer should prove only:

```text
EdgeFamilyTuple
rawEdgeTupleA1
rawEdgeTupleA3
edgeFamilyRawOrderTuple
edgeFamilyOfRawOrderTuple
edgeFamilyOfRawOrderTuple_edgeFamilyRawOrderTuple
edgeFamilyRawOrderTuple_edgeFamilyOfRawOrderTuple
edgeFamilyRawOrderLinearEquiv
topologyTupleEdgeRawOrder
edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
injOn_topologyTupleEdgeRawOrder_detChartSet
```

The last injectivity theorem should follow by converting equality of raw
tuples back to equality of edge families and then using
`injOn_topologyTupleEdgeMatrix_detChartSet`.

## Nonclaims

No derivative, determinant formula, density, measure pushforward, source-rank
coverage, source-measure theorem, normal crossings, pole order, or RLCT
extraction is proved here.

## Lean Result

`RetainedPassiveCoordinatesTopology.lean` now implements the raw edge-family
tuple equivalence and the retained-passive endomap

```text
topologyTupleEdgeRawOrder z :=
  edgeFamilyRawOrderTuple (topologyTupleEdgeMatrix z).
```

The formalized facts are exactly the expected scope above, plus simp lemmas
for the endpoint reads of `rawEdgeTupleA1` and `rawEdgeTupleA3`.  The
injectivity theorem is only the transfer of already-proved injectivity for
`topologyTupleEdgeMatrix` along the raw edge-family equivalence.
