# Statement Card - A2 literal product-difference square-sum

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
AoyagiProductDifferenceCoordinateIndex.literalValue
AoyagiProductDifferenceCoordinateIndex.literalValue_regular
AoyagiProductDifferenceCoordinateIndex.literalValue_residual
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_regular_add_correctedResidual
```

## Statement Shape

`literalValue X F2 F3 D` is the scalar coordinate family attached to the
literal signed/corrected p. 13 block:

```text
fromBlocks X (-F2) (-F3) (D - F3 * F2).
```

The regular summand reads entries of `X`, `-F2`, and `-F3`.  The residual
summand reads entries of `D - F3 * F2`.

Lean proves the finite square-sum identity

```text
aoyagiCoordinateSquareSum (literalValue X F2 F3 D)
  =
aoyagiCoordinateSquareSum (regularValue X F2 F3)
  + aoyagiCoordinateSquareSum (residualValue (D - F3 * F2)).
```

The signs disappear only through the elementary equality `(-a)^2 = a^2`.

## Scope

Finite algebraic square-sum bookkeeping for the literal p. 13 displayed block.
This is the literal-loss counterpart to the cleaned square-sum split.

## Nonclaims

No comparison between `D - F3 * F2` and `D`, no local loss comparability, no
analytic generator transport, no regular-coordinate chart construction, no
Jacobian/prior compatibility, no normal-crossing construction, no pole-order
theorem, and no RLCT extraction is proved.
