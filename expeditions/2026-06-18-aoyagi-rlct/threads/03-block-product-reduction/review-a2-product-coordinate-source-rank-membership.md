# Review - A2 product-coordinate source-rank membership

Date: 2026-06-25.

Reviewers: xhigh check-ins from `Bernoulli`, `Banach`, and `Confucius`, plus
controller Lean/API audit after recovery.

## Scope

Reviewed the pen-and-paper reproduction
`reproduction-a2-product-coordinate-source-rank-membership.md` and the Lean
increment:

```text
ChartLocalSuffixState.rank_productCoordinateRightEndpointMatrix
ChartLocalSuffixState.rank_productCoordinateMiddleMatrix
ChartLocalSuffixState.rank_productCoordinateLeftEndpointMatrix
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum
exists_pos_radius_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum_nhdsWithin_source
```

## Verdict

Accepted for the stated finite/source-rank scope.

The block-rank calculations are the elementary p.13 row/column
unitriangular reductions:

- right endpoint: multiply by `[I 0; F3 I]` and reduce to `[I 0; 0 C]`;
- middle edge: already `[I 0; 0 C]`;
- left endpoint: multiply by `[I F2; 0 I]` and use `IsUnit det(Ctop)` to
  reduce to `[Ctop 0; 0 C]` with regular rank equal to the corner size.

The pointwise source-rank theorem correctly requires both base source-rank
membership and a base product-reduction certificate.  The local theorem only
adds a small Euclidean radius ensuring `det Ctop(u)` is a unit and eventual
base product-reduction certificates near the self-base chain.

## Boundary

This slice is not source coverage and not a product chart theorem.  It does
not prove exact-rank openness, local inverse, selected-entry source/image
equality, weighted pushforward, Jacobian/source-density identity, residual
monomial identities, normal crossings, pole order, or RLCT.

The next source-moving targets remain:

- local selected-entry source/image equality, or
- concrete selected-entry residual readout/factor-product identity, or
- analytic product-coordinate chart and density/Jacobian transport.

## Checks

Focused checks passed:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/ProductReduction.lean
lake build DLNFibre.DLN.Aoyagi.ProductReduction
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

Banking gates also passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
```
