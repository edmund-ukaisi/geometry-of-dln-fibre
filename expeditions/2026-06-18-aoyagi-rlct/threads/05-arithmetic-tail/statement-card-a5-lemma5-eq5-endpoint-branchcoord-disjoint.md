# Statement card - A5 Lemma 5 Eq5 endpoint branch-coordinate disjointness

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord`

## Claim

Supplied component coordinate facts for the Eq5 strict, upper-endpoint, and
explicitly inserted rising lower-endpoint records force raw branch sets at
distinct interior coordinates `i,j in Finset.Icc 1 (ell - 1)` to be disjoint.
Consequently the Eq5 endpoint supplied family can be constructed without
separately supplying cross-coordinate disjointness, while still assuming raw
value injectivity and all coverage/value data.

## Proved

Finite coordinate-map disjointness for raw branch sets and a supplied-family
constructor wrapper that derives the disjointness field from component
coordinate facts.

## Assumed

Strict branch coordinate correctness, upper endpoint coordinate correctness,
rising-case lower endpoint coordinate correctness, base-value membership, raw
value injectivity, Eq5 alpha-domain coverage, and endpoint value equalities.

## Deferred

Source construction of branch records, source production of endpoint records,
source-label legality, source proof of the coordinate map, source proof of raw
value injectivity, endpoint distinctness, base-filter survival, counted-datum
back-to-label coverage, no-extra terminal-minimum coverage, exact order count
from source, pole order, normal crossings, and RLCT extraction.

## Review

Passed independent xhigh review by Noether on 2026-06-22.  Review artifact:
`review-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`.

## Verification

Passed:

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
