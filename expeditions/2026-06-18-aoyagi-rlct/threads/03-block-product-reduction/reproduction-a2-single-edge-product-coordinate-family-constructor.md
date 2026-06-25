# Reproduction - A2 single-edge product-coordinate family constructor

Date: 2026-06-25.

Status: pen-and-paper reproduction for the one-edge p.13 product-coordinate
matrix family `G(u,D)`.

## Source Boundary

Aoyagi p.13 writes the product-coordinate variables in the regular blocks

```text
Ctop - I, F2, F3
```

and the residual block `D`.  This note treats only the endpoint-collapsed
single-edge case.  It constructs the fixed-base edge matrix whose cleaned
coordinate readout is a prescribed regular coordinate vector `u` and a
prescribed residual matrix `D`.

It does not construct the multi-edge residual-factor family, prove
parameter-continuity in a source variable, prove source coverage, construct a
product chart, transport density/Jacobian factors, produce normal crossings,
prove pole order, or extract RLCT.

## Calculation

Let

```text
u : EuclideanSpace ℝ ((ρ × ρ) ⊕ ((ρ × ν) ⊕ (μ × ρ))).
```

From `u`, define

```text
X  i j = u(inl(i,j)),
F2 i j = u(inr(inl(i,j))),
F3 i j = u(inr(inr(i,j))),
Ctop = I + X.
```

Then `Ctop - I = X`, hence

```text
value(Ctop - I,F2,F3) = u.
```

Given a residual matrix `D : Matrix μ ν ℝ`, define the single fixed-base edge
matrix

```text
G(u,D) =
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ].
```

The terminal suffix state has `B=0`, `Ctop=I`, `D=I`, and `L=I`, so the
transformed edge is the same matrix.  The Schur residual is

```text
(D + F3 Ctop F2) - (-F3 Ctop) Ctop^{-1} (-Ctop F2).
```

Under the explicit chart hypothesis `IsUnit Ctop.det`,

```text
(-F3 Ctop) Ctop^{-1} (-Ctop F2) = F3 Ctop F2,
```

so the residual is exactly `D`.  The suffix fields are therefore

```text
S.B    = -F2,
S.Ctop = Ctop,
S.D    = D,
S.L    = [I,0;F3,I].
```

The fixed-base cleaned coordinate map reads

```text
ProductValue(Ctop - I,F2,F3,D).
```

Using `Ctop - I = X` and `value(X,F2,F3)=u`, this is exactly

```text
Sum.elim (fun c => u c) (AoyagiResidualBlockCoordinateIndex.value D).
```

## Lean Target

The finite residual matrix reconstruction is:

```text
AoyagiResidualBlockCoordinateIndex.matrix
AoyagiResidualBlockCoordinateIndex.value_matrix
AoyagiResidualBlockCoordinateIndex.exists_value_eq
```

The single-edge product-coordinate matrix family is:

```text
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean
```

The theorem realises the prescribed matrix as a continuous fixed-base edge
family using the existing `paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices`
and then applies the existing single-edge readout theorem.  The conclusion is
the full product-difference coordinate identity

```text
regular coordinate = u,
residual coordinate = value D.
```

## Boundary

This is pointwise finite matrix algebra for one edge.  It does not prove that
`Ctop` is invertible near the origin, produce a source-neighborhood
determinant chart, choose `D` from a base family, prove any multi-edge
residual-product identity, or prove continuity of a two-variable
`(x,u)` family.
