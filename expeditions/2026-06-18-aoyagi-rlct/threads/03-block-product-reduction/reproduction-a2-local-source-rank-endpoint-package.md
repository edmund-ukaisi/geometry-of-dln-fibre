# A2 local source-rank endpoint package reproduction

Date: 2026-06-23.

Source used: Aoyagi 2023 preprint, Section 5, Lemma 2 and Theorem 3
(PDF/printed pp. 10-13).

## Question

The fixed-base A2 boundary already has a pointwise source-shaped endpoint
wrapper:

```text
PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks
```

It takes a basepoint certificate, a fixed-base product-reduction certificate,
and membership in the source rank stratum.  Separately, the local boundary says
that the fixed-base product-reduction certificate holds on a neighborhood of
the base chain, and that rank-refined statements should be read relative to
the exact/source rank stratum.

The missing packaging step is the local source-shaped conclusion itself:
near the base chain, relative to Aoyagi's source rank stratum, the endpoint
triangular residual-product/source-rank conclusion holds.

A second small boundary check is also needed: the source rank stratum is
nonempty at the base parameter once the source rank equalities are supplied.
This does not make the stratum open; it only prevents the local relative
package from being read as vacuous at the base point.

## Reproduction

Fix a paper-order base chain `B`, a total-kernel complement `U0`, and a
continuous nearby reversed-edge family `Cedge` based at `B`.  The already
proved local fixed-base theorem gives an ordinary neighborhood `U` of the base
parameter `x0` such that every `x in U` has a fixed-base product-reduction
certificate:

```text
ProductReductionCertificate(x).
```

The source rank stratum is a restriction:

```text
rank(base product) = r,
rank(Cedge x p) = rEdge p for every p,
r <= rEdge p for every p.
```

It is not asserted to be open.  Therefore the correct local statement is a
relative-neighborhood statement:

```text
U intersect SourceRankStratum
  subset {x | TriangularResidualProductSourceRanks(x)}.
```

For any `x` in this intersection, the product-reduction certificate supplies
the determinant-chart and endpoint block-diagonal data.  The source stratum
supplies the rank hypotheses.  The basepoint certificate identifies
`finrank U0` with the fixed base product rank `r`.  Applying the existing
pointwise wrapper gives:

```text
TriangularResidualProductSourceRanks(x).
```

The endpoint lower-right block is still
`ChartLocalSuffixState.residualProduct`, the deterministic product of the
transformed Schur residuals visited by the suffix recursion.  It is not a raw
product of untransformed lower-right edge blocks.

Existentially, finite-dimensionality gives a complement `U0` to the total
kernel of the base product, hence a local source-rank endpoint package after
choosing that complement.

For basepoint membership, assume explicitly:

```text
Cedge(x0,p) = reverseEdge(B,p),
rank(paperTotalMap B) = r,
rank(reverseEdge(B,p)) = rEdge p,
r <= rEdge p.
```

Then the definition of `paperEndpointFixedBaseSourceRankStratum` is immediate:
the first field is the supplied product-rank equality; the edge-rank-stratum
field follows by rewriting `Cedge x0 p` to the base edge; the inequality field
is supplied.  No continuity or openness argument is used.

## Lean target

Add to `ProductReductionBoundary.lean`:

- a fixed-base `nhdsWithin` theorem whose target set is
  `PaperEndpointFixedBaseTriangularResidualProductSourceRanks`;
- an existential local package choosing the total-kernel complement;
- an existence theorem for a continuous family based at the paper chain.
- a basepoint membership theorem for `paperEndpointFixedBaseSourceRankStratum`
  from supplied source product/layer rank equalities and inequalities.

## Not Claimed

- No exact-rank openness.
- No nonemptiness of the source rank stratum.
  The basepoint theorem proves membership only under supplied rank data.
- No full source Theorem 3.
- No Aoyagi Lemma 1 normalization.
- No analytic ideal-germ transport.
- No regular-coordinate RLCT additivity.
- No normal-crossing chart production, pole order, or RLCT conclusion.
- No identification of `residualProduct` with a raw product of original edge
  lower-right blocks.

## Kill Conditions

- If the local theorem uses `nhds x0` instead of `nhdsWithin x0
  SourceRankStratum`, it is overclaiming exact-rank openness.
- If the conclusion drops the transformed `residualProduct` and uses a raw
  edge-block product, it is not the proved Aoyagi recursion.
- If the theorem is later used as analytic ideal transport or regular
  variable additivity, its statement boundary has been crossed.
