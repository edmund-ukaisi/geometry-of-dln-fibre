# Statement Card - A2 regular-coordinate ideal bridge

Date: 2026-06-24.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal
```

## Statement Shape

The scalar regular-coordinate ideal is

```text
Ideal.span (Set.range (AoyagiRegularBlockCoordinateIndex.value X F2 F3)).
```

Lean proves

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal X F2 F3 =
  regularBlockEntryIdeal X F2 F3.
```

For the fixed-base canonical product-difference source-rank package, Lean also
rewrites the product-difference entry ideal as

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔ matrixEntryIdeal S.D.
```

## Scope

Finite algebraic bridge between the scalar coordinate index and the regular
block-entry ideal.  The ideal equality itself is algebraic and does not require
finite index types; the finite Aoyagi use is supplied by the surrounding count
theorems.

## Nonclaims

No residual `D` coordinate, analytic chart, analytic ideal transport, coverage,
Jacobian compatibility, normal crossings, pole order, or RLCT.
