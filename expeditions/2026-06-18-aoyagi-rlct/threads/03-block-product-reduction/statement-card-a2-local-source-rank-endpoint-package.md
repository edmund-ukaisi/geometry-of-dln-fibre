# Statement card - A2 local source-rank endpoint package

## Claim

Near a continuous reversed-edge family based at a fixed paper chain, and
relative to Aoyagi's source rank stratum, the proved product-reduction boundary
has the endpoint source shape: triangular endpoint multipliers expose the
deterministic transformed residual product, and every visited transformed
residual block has rank `rEdge p - r`.

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`

Names:

- `paperEndpointFixedBaseSourceRankStratum_selfBase_mem`
- `paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`
- `PaperEndpointTriangularSourceRanksLocalCertificate`
- `exists_paperEndpointTriangularSourceRanksLocalCertificate`

## Inputs Kept Explicit

- finite-dimensional paper chain;
- continuous nearby reversed-edge family `Cedge`;
- basepoint equality `Cedge x0 = reverseEdge W B`;
- source product rank `r` and layer ranks `rEdge`;
- explicit basepoint product/layer rank equalities and inequalities for
  source-stratum membership;
- relative restriction to `paperEndpointFixedBaseSourceRankStratum`.

## Proved

The fixed-base theorem packages the existing ordinary neighborhood of
product-reduction certificates with the source-rank-stratum restriction and
then applies the existing pointwise endpoint source-rank wrapper.  The
existential theorem chooses a total-kernel complement and records the same
local package without exposing the fixed complement as a caller input.

The basepoint membership theorem proves that the base parameter belongs to the
source rank stratum when the source rank equalities and inequalities are
supplied explicitly.  It does not prove any openness or rank persistence.

## Not Proved

No exact-rank openness, ambient source-stratum nonemptiness, full Aoyagi
Theorem 3, Aoyagi Lemma 1 normalization, analytic ideal transport,
regular-coordinate/RLCT additivity, normal-crossing production, pole order, or
RLCT extraction.  The only nonvacuity statement here is basepoint membership
under supplied rank data.

The lower-right endpoint block remains `ChartLocalSuffixState.residualProduct`
for transformed Schur residuals, not a raw product of original edge lower-right
blocks.

## Verification

Focused and full builds passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionBoundary
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The no-sorry audit reported zero `sorry`, `#exit`, `native_decide`, and
`axiom` hits.
