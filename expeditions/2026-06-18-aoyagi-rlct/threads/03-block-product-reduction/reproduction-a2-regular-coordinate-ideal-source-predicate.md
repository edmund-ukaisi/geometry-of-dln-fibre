# Reproduction - A2 regular-coordinate ideal source predicate

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the product-difference variables into regular
blocks

```text
C1 - Er,   F2,   F3
```

and a residual block.  The previous A2 slices already prove, on the local
source-shaped rank stratum near the base chain, that the product-difference
entry ideal is the scalar regular-coordinate ideal joined with the residual
`D`-block entry ideal.

## Predicate Shape

For a later supplied regular-suspension chart, the source-side algebraic data
should be a predicate that says:

1. a fixed endpoint-complement local source certificate exists;
2. the certificate exposes an ordinary neighborhood `U` of the base point;
3. on `U` intersected with the source-shaped rank stratum, the canonical
   product-difference entry ideal splits as

```text
entryIdeal(S.Ctop - 1, -S.B, lowerLeftBlock S.L) + matrixEntryIdeal(S.D).
```

This predicate is stronger than merely remembering the existential local source
certificate, because it records the algebraic regular/residual split as a named
source-side obligation that a supplied regular-suspension chart can cite.

## Nonclaims

- No source-rank stratum openness.
- No analytic germ-ideal transport.
- No construction of a full regular-suspension chart `Cfull`.
- No chart coverage, Jacobian compatibility, exponent shift, normal crossings,
  pole order, or RLCT theorem.
- The residual block remains outside the scalar regular-coordinate ideal.
