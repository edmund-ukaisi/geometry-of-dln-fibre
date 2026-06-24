# Reproduction - A2 regular-coordinate source data

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the post-product-reduction product-difference
variables into three regular block families

```text
C1 - Er,   F2,   F3
```

and the remaining residual block.  Previous A2 slices already translated the
fixed-base Lean convention for these regular block families as

```text
S.Ctop - 1,   -S.B,   lowerLeftBlock S.L.
```

The residual block is `S.D`.

## Calculation

Assume a continuous reversed-edge family `Cedge` based at a chain `B`,

```text
Cedge x0 = reverseEdge W B,
```

and source rank data

```text
rank(paperTotalMap W B) = r,
rank(reverseEdge W B p) = rEdge p.
```

The base product factors through each edge, so the already proved no-`hle`
source-certificate constructor derives the inequalities `r <= rEdge p` and
chooses a total-kernel complement

```text
U0 complement ker(paperTotalMap W B).
```

For this fixed endpoint basis, the canonical local source certificate supplies:

1. a local source certificate with basepoint membership in the source-shaped
   rank stratum;
2. an ordinary neighborhood whose restriction to that source-shaped rank
   stratum satisfies the regular/residual ideal split

```text
matrixEntryIdeal(productDifference)
  =
AoyagiRegularBlockCoordinateIndex.entryIdeal
  (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L)
  + matrixEntryIdeal S.D;
```

3. centered continuous scalar regular coordinates for every entry of
   `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`;
4. after the residual-coordinate update, centered continuous scalar residual
   coordinates for every entry of `S.D`, recorded separately from the regular
   coordinate index;
5. with the dimension convention

```text
H(k+1) = finrank(W k),
```

the scalar regular-coordinate index has cardinality

```text
aoyagiTheorem2RegularVariableCount N H r.
```

The residual-coordinate update also records the residual entry count

```text
(H(1)-r) * (H(N+1)-r).
```

The source-data package is therefore a strict assembly of already reproduced
finite/topological source information: it exposes, in one object, the local
source certificate, the regular-coordinate/residual ideal split, centered
scalar coordinates for both the regular and residual blocks, the p. 13
regular-variable count, and the residual endpoint entry count.

## Nonclaims

- No exact-rank or source-rank openness.
- No construction of an analytic regular-suspension chart.
- No analytic germ-ideal transport.
- No chart coverage theorem.
- No Jacobian compatibility theorem.
- No exponent-shift theorem beyond finite cardinal/count bookkeeping.
- No normal crossings, pole order, or RLCT theorem.
