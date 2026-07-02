# A2 Raw-Order Patch COV

## Purpose

The previous localized COV handles an arbitrary determinant-chart patch
`Omega` and identifies the image as `Phi '' Omega`.  The next endpoint/raw
comparison wants to name the target-side patch first.  This note records the
elementary set calculation that converts a raw-order source patch `P` into the
corresponding determinant-side patch.

## Calculation

Let

```text
S = topologyTupleDetChartSet
T = topologyTupleRawOrderSourceRecursiveDetChartSet
Phi = topologyTupleEdgeRawOrder
Psi = topologyTupleEdgeRawOrderInverse
J z = ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z).
```

Assume `P subset T` and define

```text
Omega = S inter Phi^{-1}(P).
```

The inverse identities on the determinant/source charts give:

```text
Psi (Phi z) = z      for z in S,
Phi (Psi y) = y      for y in T,
Psi y in S           for y in T.
```

Hence `Phi '' Omega = P`.

The inclusion `Phi '' Omega subset P` is immediate from the definition of
`Omega`.  Conversely, if `y in P`, then `y in T`; put `z = Psi y`.  Then
`z in S`, `Phi z = y`, and therefore `z in Omega`.

Applying the localized retained-passive raw-order COV to `Omega` gives:

```text
Measure.map Phi ((m.restrict Omega).withDensity J)
  = m.restrict (Phi '' Omega)
  = m.restrict P.
```

If `psi` is a.e. measurable for `m.restrict P`, the post-composed form gives:

```text
Measure.map (fun z => psi (Phi z)) ((m.restrict Omega).withDensity J)
  = Measure.map psi (m.restrict P).
```

## Boundary

This is still determinant-chart measure infrastructure.  It does not prove
that any concrete endpoint image dominates Haar on `Omega`, nor that a
source-prior lower bound holds.  It only supplies the exact COV target once an
honest raw-order patch `P` has been named.
