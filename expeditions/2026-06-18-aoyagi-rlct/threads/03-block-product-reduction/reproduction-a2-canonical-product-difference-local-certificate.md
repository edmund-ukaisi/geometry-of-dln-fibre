# Reproduction - A2 canonical product-difference local certificate

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The existing Lean development has three separate p. 13 ingredients:

1. a local fixed-base product-reduction certificate near the base chain on the
   recursive determinant charts;
2. the canonical product-difference entry-ideal equality with fields
   `S.Ctop - I`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`;
3. continuity and basepoint centering of these four canonical fields at the
   self-base chain.

Future regular-suspension work needs these as one local source-facing object.
The present slice reproduces the exact elementary package: a fixed-base local
certificate, relative to Aoyagi's source-shaped rank stratum, whose pointwise
conclusion uses the canonical fields and whose basepoint fields are centered
and continuous.

## Source Anchor

Aoyagi Theorem 3 and the following paragraph, PDF pp. 11-13, separate the
entries of the block product difference into regular variables

```text
Ctop - I,  F2,  F3
```

and a reduced residual product.  The Lean canonical fields are the
deterministic suffix-state versions

```text
Ctop = S.Ctop,  F2 = -S.B,  F3 = lowerLeftBlock S.L,  D = S.D.
```

This slice is still only the elementary/topological boundary around that
calculation.  It does not construct a normal-crossing chart or prove analytic
ideal transport.

## Reproduction

Fix a base paper chain `B`, choose a total-kernel complement `U0`, and let
`Cedge : alpha -> edges` be a continuous reversed-edge family with
`Cedge x0 = reverseEdge B`.

For each parameter `x`, define the fixed-base coordinate edge matrices

```text
E(x,p) = matrix of Cedge(x,p) in the endpoint bases fixed from B and U0
```

and let

```text
S(x) = suffixState E(x) (last N) 0.
```

The existing local product-reduction theorem gives a neighborhood `U` of
`x0` such that for every `x in U`, the fixed-base product-reduction certificate
holds.  Therefore the recursive suffix-state block-diagonal invariant holds
for `S(x)`.

From that certificate, the canonical entry-ideal theorem gives

```text
matrixEntryIdeal(total(x) - [I 0; 0 0])
  = fourMatrixEntryIdeal
      (S(x).Ctop - I)
      (-(S(x).B))
      (lowerLeftBlock S(x).L)
      (S(x).D).
```

Restricting to the source-shaped rank stratum adds the source residual-rank
formulas:

```text
rank residualBlock_p(x) = rEdge_p - r.
```

This is a relative `nhdsWithin` statement.  It does not assert that the source
rank stratum is open.

At the base point, the previously proved centered-continuity theorem gives

```text
S(x0).Ctop - I = 0,
-(S(x0).B) = 0,
lowerLeftBlock S(x0).L = 0,
S(x0).D = 0,
```

and continuity at `x0` of the same four fields.  The determinant-unit fact
`IsUnit ((S x0).Ctop.det)` is retained.

## Lean Shape

Add in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

PaperEndpointFixedBaseProductReductionCertificate
  .toCanonicalProductDifferenceSourceRanks

paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source

PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl

PaperEndpointCanonicalProductDifferenceLocalCertificate

exists_paperEndpointCanonicalProductDifferenceLocalCertificate
```

The fixed-base local certificate should contain:

- the centered-continuity theorem for the self-base canonical fields;
- a `nhdsWithin` conclusion, relative to
  `paperEndpointFixedBaseSourceRankStratum`, whose pointwise predicate records
  the canonical product-difference entry-ideal equality and residual-rank
  formulas.

## Kill Conditions

- If the statement asserts source-rank or exact-rank openness, it is too
  strong.
- If it claims analytic regularity, analytic ideal/germ transport, chart
  coverage, regular-suspension construction, normal crossings, pole order, or
  RLCT, it is too strong.
- If the pointwise ideal equality uses existential `F2/F3` witnesses instead
  of the deterministic fields `-S.B` and `lowerLeftBlock S.L`, it does not
  serve the next regular-suspension step.
- If the centered-continuity data is omitted, this is only the old local
  product-difference certificate in another form.
