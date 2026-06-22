# A2 rank-stratum boundary reproduction

Date: 2026-06-22.

Source used: Aoyagi 2023 preprint, Section 5, Theorem 3 proof.

## Question

The current Lean product-reduction boundary gives residual-rank conclusions as
implications:

```text
if rank(A^(s)) = r^(s), then rank(C^(s)) = r^(s) - r.
```

Aoyagi's source hypotheses are rank-stratum hypotheses on the nearby layers, not
open-chart hypotheses.  Since exact-rank strata are not open in general, the
next safe step is to make the stratum restriction explicit rather than treating
it as part of the open neighborhood.

## Calculation

Fix endpoint bases from a base chain and a total-kernel complement.  Let
`Cedge x p` be the nearby reversed paper edge at a parameter `x`, and let
`rEdge p` be the source-specified rank of that layer.  Define the exact
edge-rank stratum

```text
RankStratum = { x | for every p, rank(Cedge x p) = rEdge p }.
```

For source-facing use also record Aoyagi's product rank and layer-rank
inequalities:

```text
SourceRankStratum =
  { x |
    rank(base product) = r,
    x in RankStratum,
    for every p, r <= rEdge p }.
```

The existing certificate contains:

```text
residualRankImplications :
  for every p,
    rank(Cedge x p) = rEdge p ->
      rank(residualBlock visited at p) = rEdge p - rank(U0).
```

Therefore, on `RankStratum`, every implication may be applied pointwise:

```text
rank(residualBlock visited at p) = rEdge p - rank(U0).
```

Topologically, the determinant-chart/block-diagonal certificate still holds on
an ordinary neighborhood `U` of the base point.  The rank-refined statement is
not that `RankStratum` is a neighborhood; it is the relative-neighborhood
statement

```text
U ∩ RankStratum ⊆ { x | product-reduction certificate with residual ranks }.
```

Equivalently, the rank-refined certificate holds in
`nhdsWithin x0 RankStratum`.

On the source-shaped stratum, the basepoint certificate supplies

```text
rank(U0) = rank(base product) = r,
```

so the residual-rank equality rewrites to Aoyagi's displayed subtraction:

```text
rank(residualBlock visited at p) = rEdge p - r.
```

## Lean target

Add to `ProductReductionBoundary.lean`:

- `paperEndpointFixedBaseEdgeRankStratum`;
- `paperEndpointFixedBaseSourceRankStratum`;
- `paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks`;
- `PaperEndpointFixedBaseProductReductionRankStratumCertificate`;
- a pointwise constructor from the existing certificate plus stratum membership;
- a source-shaped residual rank theorem using the basepoint certificate;
- `nhdsWithin` theorems near the base chain for both rank-stratum predicates;
- local fixed-base and existential wrappers mirroring the existing local
  certificate API.

## Nonclaims

- No exact-rank openness.
- No claim that a nearby point remains in the rank stratum.
- No analytic ideal-germ transport.
- No regular-coordinate or RLCT additivity.
- No Aoyagi Lemma 1 use.
- No normal-crossing production or extraction.
