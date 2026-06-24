# Reproduction - A2 regular-coordinate ideal source existence

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the product-difference variables into regular
blocks.  In the Lean canonical suffix-state convention these are

```text
Ctop - 1,   -B,   lowerLeftBlock L
```

and the residual block.  Earlier A2 slices already prove the elementary
fixed-base local source certificate and the scalar regular-coordinate/residual
ideal source predicate for these blocks.

## Calculation

Inputs:

- a continuous reversed-edge family `Cedge` at `x0`;
- base equality `Cedge x0 = reverseEdge W B`;
- product rank `rank(paperTotalMap W B) = r`;
- edge ranks `rank(reverseEdge W B p) = rEdge p`;
- source-rank bounds `r <= rEdge p`.

The existing source-certificate theorem first chooses an endpoint complement
`U0` to the total kernel of the base product.  With that fixed base, it returns
a local canonical product-difference source certificate.  The fixed-base
certificate gives an ordinary neighborhood where every point of the
source-shaped rank stratum has the canonical product-difference ideal split

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔ matrixEntryIdeal S.D.
```

Thus the raw rank and continuity hypotheses produce the stronger
`AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` predicate by
the following composition:

```text
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
  --> aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
```

No new matrix identity or analytic argument is introduced in this step.  The
calculation is only the assembly of the already-reproduced endpoint-complement
choice, local source certificate, and regular-coordinate/residual ideal split.

## Nonclaims

- No source-rank stratum openness.
- No analytic germ-ideal transport.
- No construction of a full regular-suspension chart `Cfull`.
- No construction of regular ideal transport, chart coverage, Jacobian
  compatibility, or exponent shift.
- No normal crossings, pole order, or RLCT theorem.
