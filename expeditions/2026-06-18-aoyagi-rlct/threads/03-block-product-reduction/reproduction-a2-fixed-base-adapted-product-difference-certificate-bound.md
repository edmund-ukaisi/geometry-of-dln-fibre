# Reproduction - A2 fixed-base adapted product-difference certificate bound

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean attempt for the pointwise
certificate-facing wrapper.

## Source Anchor

Aoyagi p. 13 uses triangular endpoint multipliers to express the adapted
endpoint product matrix in block diagonal form.  In the fixed-base Lean
coordinate system, the deterministic suffix state supplies

```text
F2 = -S.B,
F3 = lowerLeftBlock S.L,
C  = S.Ctop,
D  = S.D.
```

The fixed-base product-reduction certificate gives the triangular identity

```text
[[I, 0], [F3, I]] * T(x) * [[I, F2], [0, I]]
  = [[C, 0], [0, D]],
```

where `T(x)` is the fixed-base endpoint total product matrix.

## Derivation

Let

```text
T0 = [[I, 0], [0, 0]],
A(x) = squareSum(T(x) - T0).
```

The already-proved finite triangular-multiplier theorem says that if

```text
squareSum([[I,0],[F3,I]]) * squareSum([[I,F2],[0,I]]) <= Kmul
```

and `c >= 0`, `c*Kmul <= 1`, then

```text
c * squareSum([C-I, -F2; -F3, D-F3*F2]) <= A(x).
```

With the deterministic substitutions `F2=-S.B` and
`F3=lowerLeftBlock S.L`, the literal coordinate map is exactly the scalar
coordinate family of the block `[C-I, -F2; -F3, D-F3*F2]`.

The multiplier bound is kept as a supplied pointwise hypothesis.  It should
later come from local boundedness of the deterministic suffix-state fields,
but determinant-unit or unitriangular shape alone is not such a bound.

## Lean Shape

Lean introduces pointwise helper definitions in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with intended names

```text
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
```

The theorem is pointwise over `ℝ` and assumes a
`PaperEndpointFixedBaseProductReductionCertificate`, `0 <= c`, `c*Kmul <= 1`,
and the supplied multiplier product bound.

## Boundary

This is not a theorem about the original DLN/statistical loss.  It does not
prove covariance lower bounds, basis norm equivalence with the original
network coordinates, local multiplier boundedness, source-rank openness,
analytic chart construction, Jacobian/prior transport, regular-suspension
Fubini/polar shift, normal crossings, pole order, or RLCT extraction.
