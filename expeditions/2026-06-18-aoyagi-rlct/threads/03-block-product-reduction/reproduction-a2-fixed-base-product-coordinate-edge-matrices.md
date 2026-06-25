# Reproduction - A2 fixed-base product-coordinate edge matrices

Date: 2026-06-25.

Status: pen-and-paper reproduction for replacing supplied transformed-edge
shape hypotheses by raw p.13 product-coordinate edge-matrix shapes.

## Source Boundary

Aoyagi p.13 uses product coordinates whose regular fields are

```text
Ctop - I, F2, F3
```

and whose cleaned residual field is the residual product.  This note proves
only the finite matrix algebra that these raw edge patterns produce the suffix
fields read by the existing fixed-base coordinate map.

It does not construct an analytic chart, prove source coverage, prove a
Jacobian or density identity, produce normal crossings, or extract an RLCT.

## Calculation

The suffix recursion uses

```text
transformedEdge(E,p,S) = [I, S.B; 0, I] * E_p.
```

For a chain with at least two edges, use the raw edge patterns

```text
right endpoint: [I, 0; -F3, C_last],
middle edges:   [I, 0; 0, C_p],
left endpoint:  [Ctop, -Ctop F2; 0, C_0].
```

The right endpoint starts from the terminal state, where `B=0`, `Ctop=I`,
`D=I`, and `L=I`.  Hence the transformed edge is the same displayed right
matrix.  The one-step calculation gives

```text
B=0, Ctop=I, D=C_last, L=[I,0;F3,I].
```

Inductively, a middle edge is processed only after the tail state has `B=0`.
Thus

```text
[I,0;0,I] * [I,0;0,C_p] = [I,0;0,C_p],
```

and the middle step preserves `B=0`, `Ctop=I`, and `L=[I,0;F3,I]`, while
multiplying the residual by `C_p`.

At the left endpoint the tail still has `B=0`, so the raw left matrix is also
the transformed left matrix:

```text
[I,0;0,I] * [Ctop, -Ctop F2; 0, C_0]
  = [Ctop, -Ctop F2; 0, C_0].
```

With `IsUnit Ctop.det`, the Schur step gives

```text
B=-F2, Ctop=Ctop, D=residualProduct, L=[I,0;F3,I].
```

The fixed-base coordinate readout therefore remains

```text
value(Ctop - I, F2, F3, residualProduct EMat last 0).
```

For a single-edge chain the raw edge is already the endpoint-collapsed block

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   C0 + F3 Ctop F2 ].
```

Its Schur residual is

```text
(C0 + F3 Ctop F2) - (-F3 Ctop) Ctop^{-1} (-Ctop F2) = C0,
```

again under `IsUnit Ctop.det`.  The readout is

```text
value(Ctop - I, F2, F3, C0).
```

## Lean Target

`ProductReduction.lean` names the raw matrix patterns and proves the raw
suffix-field theorems:

```text
ChartLocalSuffixState.productCoordinateRightEndpointMatrix
ChartLocalSuffixState.productCoordinateMiddleMatrix
ChartLocalSuffixState.productCoordinateLeftEndpointMatrix
ChartLocalSuffixState.productCoordinateSingleEdgeMatrix
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges
ChartLocalSuffixState.suffixState_productCoordinate_fields_one
ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
```

`RegularSuspensionCoordinates.lean` then uses those suffix fields in the
fixed-base coordinate readout:

```text
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdges_succSucc
```

## Boundary

These theorems replace supplied transformed-edge hypotheses by supplied raw
edge-matrix shape hypotheses.  They still do not define a dependent
product-family parameterization `G(x,u)`, prove parameter-continuity, or prove
that a source chart covers the required neighborhood.  The residual coordinate
for the multi-edge case is still the suffix recursion's `residualProduct`, not
an arbitrary residual matrix.
