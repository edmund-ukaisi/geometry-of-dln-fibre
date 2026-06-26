# Reproduction - A2 p.13 product-coordinate left-step raw preimage

Date: 2026-06-26.

Status: Lean proved.

## Question

The raw preimage tuple

```text
X(x,u) = (I, Dtail(x), F3(u), Ctop(u), -Ctop(u)*F2(u), 0, C0(x))
```

has already been shown to map to the p.13 raw-shaped target tuple under the
one-step raw product-reduction map.  The next bridge is to identify `X(x,u)`
with the actual left-endpoint raw step coordinates of the constructed
multi-edge p.13 product-coordinate matrix family.

This is still pointwise finite matrix algebra.  It does not construct an
original DLN source chart, prove source coverage, or transport a measure.

## Pen-and-Paper Check

Let `Ebase(x)` be the fixed-base edge matrix family obtained from the
base reversed-edge family.  Let `G(x,u)` be the multi-edge product-coordinate
matrix family built from `Ebase(x)` and the regular coordinates `u`.

For the tail before the left endpoint, the product-coordinate construction
uses the right endpoint and middle edge patterns

```text
right endpoint: [I, 0; -F3(u), C_last(x)]
middle edges:   [I, 0; 0, C_p(x)].
```

The suffix recursion therefore gives, immediately before processing the left
endpoint,

```text
S.B = 0,
S.Ctop = I,
S.L = [I, 0; F3(u), I],
S.D = residualProduct(G, last, 1).
```

Each transformed Schur residual block of `G` is the matching transformed
Schur residual block of `Ebase`, because `G` was built with residual factors
`C_p(x) = residualBlock(Ebase, last, p)`.  Hence the tail residual products
agree:

```text
residualProduct(G, last, 1) = residualProduct(Ebase, last, 1) = Dtail(x).
```

At the left endpoint, the product-coordinate matrix is

```text
G_0 = [Ctop(u), -Ctop(u)*F2(u); 0, C0(x)].
```

Since `S.B = 0`, the transformed edge used by the raw step is the same block
matrix:

```text
transformedEdge(G, 0, S) = [Ctop(u), -Ctop(u)*F2(u); 0, C0(x)].
```

The raw suffix-step coordinates are

```text
(S.Ctop, S.D, F3prev, A1, A2, A3, A4),
```

with `F3prev = F3(u)` and `A1,A2,A3,A4` the four blocks of the transformed
left edge.  Substitution gives exactly

```text
(I, Dtail(x), F3(u), Ctop(u), -Ctop(u)*F2(u), 0, C0(x)).
```

Applying the raw-order product-step map to this raw tuple then gives the
already-proved target tuple

```text
(Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)),
```

provided `det Ctop(u)` is a unit.

## Lean Artifacts

Added to `ProductReductionStepRegularDensity.lean`:

```text
paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple
```

The first theorem is unconditional pointwise raw-coordinate algebra.  The
second uses the existing determinant-unit hypothesis on `Ctop(u)`.

## Kill Conditions

- If the proof needs an inverse of `Dtail` or of any passive residual factor,
  the statement is wrong.
- If it claims original source coverage, original source/prior transport, or a
  product-measure pushforward, it overclaims.
- If the tail residual product is not explicitly related back to `Ebase`, the
  statement is too weak to connect to the existing p.13 raw tuple.

## Nonclaims

No original DLN source chart, no source coverage, no source/prior transport,
no signed-box density identification, no product-measure pushforward, no
regular-suspension certificate, no normal crossings, no pole order, and no
RLCT.
