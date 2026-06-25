# Reproduction - A2 regular coordinate-vector block reconstruction

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite coordinate-vector-to-block
matrix reconstruction used before constructing the dependent p.13
product-coordinate family.

## Source Boundary

Aoyagi p.13 separates the regular product-coordinate variables into the three
block families

```text
Ctop - I, F2, F3.
```

This note proves only the elementary finite repackaging of a scalar coordinate
family indexed by those three tagged blocks into the three corresponding
matrices.  It does not define the dependent product-coordinate edge-family
`G(x,u)`, prove parameter-continuity, source coverage, product-chart
properties, density/Jacobian transport, normal crossings, pole order, or RLCT.

## Calculation

The regular coordinate index is the disjoint sum

```text
(ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι)).
```

Given a scalar coordinate family

```text
u : (ι × ι) ⊕ ((ι × ν) ⊕ (μ × ι)) -> R,
```

define the three block matrices componentwise by

```text
X  i j = u(inl(i,j)),
F2 i j = u(inr(inl(i,j))),
F3 i j = u(inr(inr(i,j))).
```

Here `X` is the coordinate block that will later be read as `Ctop - I`.
There are no signs in this reconstruction: the signs appear in the p.13 edge
matrices, while the cleaned coordinate readout is by definition
`value(X,F2,F3)`.

When an actual top-left block is needed, set

```text
Ctop = I + X.
```

Then `Ctop - I = X`, so the same readout theorem applies to
`value(Ctop - I,F2,F3)`.

The coordinate readout is

```text
value(X,F2,F3)(inl(i,j))       = X i j,
value(X,F2,F3)(inr(inl(i,j))) = F2 i j,
value(X,F2,F3)(inr(inr(i,j))) = F3 i j.
```

Substituting the definitions gives exactly

```text
value(X,F2,F3) = u
```

by a three-case split on the tagged coordinate.  Empty index types require no
separate argument: all three component formulas are functions out of the
corresponding product types, and the final proof is by cases on an existing
tagged coordinate.

For a Euclidean regular-coordinate vector

```text
u : EuclideanSpace ℝ (AoyagiRegularBlockCoordinateIndex ι μ ν),
```

the same construction applies to the scalar family `fun c => u c`.

## Lean Target

`RegularSuspensionCoordinates.lean` adds the coordinate projections

```text
AoyagiRegularBlockCoordinateIndex.ctopMinusIdentityMatrix
AoyagiRegularBlockCoordinateIndex.ctopMatrix
AoyagiRegularBlockCoordinateIndex.f2Matrix
AoyagiRegularBlockCoordinateIndex.f3Matrix
```

and proves

```text
AoyagiRegularBlockCoordinateIndex.ctopMatrix_sub_one
AoyagiRegularBlockCoordinateIndex.value_coordinateMatrices
AoyagiRegularBlockCoordinateIndex.exists_value_eq
AoyagiRegularBlockCoordinateIndex.value_euclideanCoordinateMatrices
AoyagiRegularBlockCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices
```

The Euclidean theorem is the finite API needed for the later product-family
goal

```text
regularBlock(CedgeProd(x,u)) = u.
```

It supplies the target `X,F2,F3` blocks for any desired regular coordinate
vector `u`; the remaining work is to place those blocks into the p.13 raw edge
matrix family while preserving the chosen residual coordinate and proving
continuity of the resulting dependent family.

## Boundary

This is finite tagged-coordinate bookkeeping.  It does not choose residual
matrices, construct raw edge matrices, realise those matrices as continuous
edge maps, prove source-stratum coverage, prove a signed-box pushforward,
transport density/Jacobian factors, produce normal crossings, or extract RLCT.
