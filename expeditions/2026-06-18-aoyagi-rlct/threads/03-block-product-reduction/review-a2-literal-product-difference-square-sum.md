# Review - A2 literal product-difference square-sum

Date: 2026-06-24.

Reviewer: xhigh `Franklin the 4th`.

Verdict: pass.

## Scope Checked

The reviewer inspected the dirty worktree read-only and checked the intended
finite literal p. 13 square-sum slice in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`.

## API Shape

The reviewed Lean names are:

```text
AoyagiProductDifferenceCoordinateIndex.literalValue
AoyagiProductDifferenceCoordinateIndex.literalValue_regular
AoyagiProductDifferenceCoordinateIndex.literalValue_residual
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_regular_add_correctedResidual
```

The key definition uses the existing product-difference coordinate index:

```text
literalValue X F2 F3 D
| Sum.inl c => regularValue X (-F2) (-F3) c
| Sum.inr c => residualValue (D - F3 * F2) c
```

The correction is `D - F3 * F2`, not `D - F2 * F3`.

The square-sum theorem states:

```text
squareSum(literalValue X F2 F3 D)
  =
squareSum(regularValue X F2 F3)
  + squareSum(residualValue (D - F3 * F2)).
```

The hypotheses `[CommRing R] [Fintype iota] [Fintype mu] [Fintype nu]` are
appropriate: `iota` is needed for `F3 * F2`, and all three finiteness
assumptions are needed for square-sums.

## Fidelity Notes

The theorem is safe if kept at finite algebraic square-sum scope.  It proves
only that the literal signed/corrected scalar family splits as regular squares
plus corrected-residual squares.  The signs disappear by `(-a)^2 = a^2`.

It does not compare `D - F3 * F2` with `D`.

## Remaining Work

The real analytic step remains:

```text
||X||^2 + ||F2||^2 + ||F3||^2 + ||D - F3 F2||^2
```

must be compared locally with the cleaned loss

```text
||X||^2 + ||F2||^2 + ||F3||^2 + ||D||^2
```

in a real/normed finite-dimensional chart, with explicit two-sided bounds.
Separately, the Fubini/polar theorem must prove that adjoining `c` regular
square variables shifts RLCT by `c/2` and preserves pole order.

## Nonclaims Confirmed

No RLCT theorem, Frobenius norm comparison, analytic transport, cleaned-loss
equality, chart construction, Jacobian compatibility, normal crossings, or
pole-order theorem is asserted.
