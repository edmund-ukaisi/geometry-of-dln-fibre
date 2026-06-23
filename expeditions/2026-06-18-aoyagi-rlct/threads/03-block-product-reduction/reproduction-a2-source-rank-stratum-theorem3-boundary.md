# A2 source-rank-stratum Theorem 3 boundary reproduction

Date: 2026-06-23.

Source used: Aoyagi 2023 preprint, Section 5, Lemma 2 and Theorem 3
(PDF/printed pp. 10-13).

## Question

The existing Lean boundary has two source-facing pieces of Aoyagi's Theorem 3:

- the endpoint triangular block form whose lower-right block is the deterministic
  product of transformed Schur residuals;
- the source-rank-stratum equality
  `rank(residual block at layer p) = rEdge p - r`.

The next safe step is to package these together at a fixed basepoint, restricted
to Aoyagi's source rank stratum. This is not a new proof of Theorem 3; it is the
elementary fixed-base/source-stratum boundary that the existing Lean facts
already prove.

## Paper calculation

Fix a base chain `B` whose total product has rank `r`. Choose endpoint bases so
that the rank-`r` part is the upper-left block, equivalently choose the
complement `U0` used in the fixed-base Lean chart. Aoyagi's one-step Lemma 2
starts with a block matrix

```text
[ A1 A2
  A3 A4 ],
```

where the upper-left block is regular, and triangular row/column operations
replace the lower-right block by the Schur residual

```text
C = A4 - A3 A1^{-1} A2.
```

In Theorem 3, after the preceding suffix has already been diagonalised, the next
edge is first transported by the previous right multiplier. Applying Lemma 2 at
the transported edge updates the endpoint lower-right block by multiplication
with the transformed Schur residual. Therefore the endpoint lower-right block is
not the raw product of original lower-right blocks. It is the ordered product

```text
residualProduct = residualBlock_last * ... * residualBlock_first
```

visited by the deterministic suffix recursion.

Aoyagi's rank statement is pointwise on the rank stratum. If the nearby edge at
layer `p` has rank `rEdge p`, and the fixed upper-left product rank is `r`, then
Lemma 2's rank calculation gives

```text
rank(transformed Schur residual at p) = rEdge p - r.
```

The source stratum records the rank hypotheses needed for this subtraction;
the regular-corner chart hypotheses needed to apply Lemma 2 still live in the
separate fixed-base product-reduction certificate:

```text
rank(base product) = r,
rank(edge p) = rEdge p for every p,
r <= rEdge p for every p.
```

The Lean fixed-base certificate gives the same calculation first as

```text
rank(residualBlock p) = rEdge p - finrank(U0),
```

and the basepoint certificate identifies

```text
finrank(U0) = rank(base product) = r.
```

Thus, on the source stratum, the residual-rank conclusion rewrites to
`rEdge p - r`.

## Lean target

Add a source-shaped endpoint predicate and constructor in
`ProductReductionBoundary.lean`.

The predicate should record:

- existence of Aoyagi-style triangular endpoint multipliers with invertible
  triangular determinants and invertible top block;
- the lower-right endpoint block equal to
  `ChartLocalSuffixState.residualProduct`, not a raw block product;
- for every layer `p`, the visited transformed Schur residual block has rank
  `rEdge p - r`.

The constructor should take:

```text
base : PaperEndpointBasepointCertificate W B U0 hU0
cert : PaperEndpointFixedBaseProductReductionCertificate W B U0 hU0 Cedge rEdge x
hsrc : x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

and combine the already-proved endpoint triangular residual-product theorem
with the already-proved source-rank residual-block theorem.

## Nonclaims

- No exact-rank openness.
- No claim that the source rank stratum is an ambient neighborhood.
- No Aoyagi Lemma 1 normalization.
- No analytic ideal-germ transport.
- No regular-coordinate RLCT additivity.
- No normal-crossing chart production.
- No pole order or RLCT conclusion.
- No identification of the residual product with the raw product of original
  edge lower-right blocks.
