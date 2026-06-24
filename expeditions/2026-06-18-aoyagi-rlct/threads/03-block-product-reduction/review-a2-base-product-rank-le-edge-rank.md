# Review - A2 base product rank bounded by edge ranks

Date: 2026-06-24.

Reviewers: controller self-check and xhigh `Copernicus the 3rd`.

## Verdict

Passed.

The rank-bound theorem
`paperTotalMap_finrank_range_le_reverseEdge_finrank_range` factors the full
reversed chain as

```text
chainMap 0 last = S.comp ((reverseEdge W B p).comp P)
```

for the prefix `P` and suffix `S`.  It then applies rank-of-composite
inequalities and converts the resulting finite cardinal-rank inequality to a
`finrank` inequality under the existing finite-dimensional hypotheses.

The no-`hle` constructors remove only the redundant explicit base inequality
input.  They derive `r <= rEdge p` from `hprod`, `hedge`, and the rank-bound
theorem, then package basepoint membership in the same source-rank stratum.
They do not change the guarded nature of the source-rank stratum and do not
assert openness.

The regular-coordinate source wrapper
`exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq`
remains source-side algebraic.  `Cred`, `Cfull`, and `regularCount` remain
shape parameters for the source predicate, and the supplied regular-suspension
boundary still requires ideal transport, coverage, Jacobian compatibility, and
exponent shift separately.

## Build Check

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean
lake build DLNFibre.DLN.Aoyagi.ProductReductionBoundary
lake build DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
lake build DLNFibre.DLN.Aoyagi.RegularSuspensionAlgebraicSource
scripts/sorries
git diff --check
```

The first serial builds passed.  One earlier parallel build of
`RegularSuspensionAlgebraicSource` raced the same `ProductReductionBoundary`
output as a simultaneous boundary build and failed while writing the `.olean`;
the serial rerun passed.

## Nonclaims Checked

No exact-rank or source-rank openness, nearby-point rank theorem outside the
existing guarded source stratum, analytic germ-ideal transport, `Cfull`
construction, ideal transport, coverage, Jacobian compatibility, exponent
shift, normal crossings, pole order, or RLCT is proved.
