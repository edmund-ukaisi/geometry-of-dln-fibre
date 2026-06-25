# Statement Card - A2 regular coordinate-vector block reconstruction

Date: 2026-06-25.

## Claim

Every scalar family of p.13 regular coordinates is the readout of explicit
regular block matrices.

For

```text
coord : AoyagiRegularBlockCoordinateIndex ι μ ν -> R,
```

define

```text
X  i j = coord(inl(i,j)),
F2 i j = coord(inr(inl(i,j))),
F3 i j = coord(inr(inr(i,j))).
```

Then

```text
AoyagiRegularBlockCoordinateIndex.value X F2 F3 = coord.
```

For a Euclidean regular-coordinate vector `u`, apply this to `coord c = u c`.
If the later edge-matrix constructor needs the actual top-left block, use
`Ctop = I + X`; then `Ctop - I = X` and the same coordinates are read.

## Lean Artifacts

```text
AoyagiRegularBlockCoordinateIndex.ctopMinusIdentityMatrix
AoyagiRegularBlockCoordinateIndex.ctopMatrix
AoyagiRegularBlockCoordinateIndex.f2Matrix
AoyagiRegularBlockCoordinateIndex.f3Matrix
AoyagiRegularBlockCoordinateIndex.ctopMatrix_sub_one
AoyagiRegularBlockCoordinateIndex.value_coordinateMatrices
AoyagiRegularBlockCoordinateIndex.exists_value_eq
AoyagiRegularBlockCoordinateIndex.value_euclideanCoordinateMatrices
AoyagiRegularBlockCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices
```

## Inputs Kept Explicit

- the tagged regular coordinate index `(ι×ι) ⊕ ((ι×ν) ⊕ (μ×ι))`;
- the scalar coordinate family, or a Euclidean vector read as its scalar
  coordinate function.

## Nonclaims

No dependent product-family `G(x,u)` is built.  No residual preservation,
parameter-continuity, source coverage, signed-box pushforward,
density/Jacobian transport, analytic chart, normal crossings, pole order, or
RLCT extraction is proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
