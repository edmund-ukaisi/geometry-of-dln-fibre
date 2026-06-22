# Statement card - A5 Lemma 5 Eq5 alpha endpoint value-image split

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split`

## Claim

For one positive interior coordinate `p`, a supplied alpha-indexed Eq5
strict-offset branch family plus supplied endpoint branch records has value
image equal to the same-coordinate interval, with the lower endpoint required
exactly in the rising case.

## Proved

Lean proves a disjunction.  Given supplied alpha-domain coverage and the Eq5
strict-offset value formula, the supplied branch image is the Eq5 offset-value
set.  The existing endpoint-deficit split then gives either:

- outside the rising case, inserting a supplied upper endpoint branch fills
  the interval;
- in the rising case `p <= a` and `p <= ell-a`, inserting supplied upper and
  lower endpoint branches fills the interval.

## Assumed

The theorem assumes the finite branch family, alpha projection, value map,
supplied endpoint branch records, alpha-domain image equality, branchwise Eq5
value formula, positive interior coordinate `p`, and endpoint value equalities.

## Deferred

Eq5 branch construction, endpoint source-label legality, branch injectivity,
base-value membership, cross-coordinate disjointness, supplied nonbase-family
construction, counted-datum classifier construction, no-extra
terminal-minimum coverage, order count, pole order, normal crossings, and RLCT
extraction.

## Review

Focused Lean check, serial module build, full `DLNFibre` build,
`git diff --check`, and `scripts/sorries` passed.  Independent xhigh review is
recorded in `review-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.
