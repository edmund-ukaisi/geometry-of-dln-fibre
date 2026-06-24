# Reproduction - A2 local source regular-coordinate ideal split

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the product-difference generators into regular
block variables

```text
C1 - Er,   F2,   F3
```

and the residual block `D`.  The fixed-base local source certificate already
provides a neighborhood, relative to the source-shaped rank stratum, where the
canonical product-difference/source-rank package holds.

## Calculation

The pointwise source-rank package gives, for each allowed nearby source point,

```text
matrixEntryIdeal(productDifference)
  = fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D.
```

The regular/residual split rewrites the right side as

```text
regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L)
  + matrixEntryIdeal S.D.
```

The scalar-coordinate bridge rewrites the regular block-entry ideal as

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L).
```

Therefore the same local source certificate exposes an ordinary neighborhood
`U` such that every `x in U` lying in Aoyagi's source-shaped rank stratum
satisfies

```text
matrixEntryIdeal(productDifference at x)
  =
entryIdeal(S.Ctop - 1, -S.B, lowerLeftBlock S.L at x)
  + matrixEntryIdeal(S.D at x).
```

## Nonclaims

- The neighborhood conclusion is still guarded by source-stratum membership.
- No source-rank stratum openness is proved.
- No analytic germ-ideal transport is proved.
- No regular-suspension chart, coverage theorem, Jacobian compatibility,
  normal crossings, pole order, or RLCT theorem is constructed.
