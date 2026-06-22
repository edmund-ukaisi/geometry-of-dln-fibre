# Statement card - A5 Lemma 5 Eq5 endpoint counted-datum classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`

## Claim

The strictest Eq5 endpoint supplied-family constructor has the branch-coordinate
correctness needed by the generic counted-datum classifier API.  Therefore it
also yields a counted-datum classifier for its supplied full branch set.

## Proved

Finite constructor-unfolding bookkeeping: filtered branch membership implies
raw branch membership, hence supplied component coordinates give
`branchCoord b = j`.  The direct classifier wrapper then applies the existing
generic `countDatumClassifierOfBranchCoord_of_branchCoord_eq`.

## Assumed

The dimension bound `a <= ell`, base-value membership, Eq5 alpha-domain
coverage, strict branch value formulas, upper endpoint value formula, rising
lower endpoint value formula, strict alpha injectivity, and strict/upper/lower
component coordinate correctness.

## Deferred

Source construction of branch records, source production of endpoint records,
source-label legality, source proof of strict alpha injectivity, source proof
of the coordinate map, endpoint distinctness, base-filter survival,
terminal-minimum label coverage, no-extra order count, pole order, normal
crossings, and RLCT extraction.

## Cited

None; this slice is finite Lean bookkeeping over supplied hypotheses and
previously formalized definitions.

## Review

Initial independent xhigh review by Hypatia on 2026-06-22 failed for
documentation/API-surface issues only: the classifier name was missing its
namespace, the notes omitted `a <= ell`, and verification metadata was stale.
These issues have been repaired.  Review artifact:
`review-lemma5-eq5-endpoint-countdatum-classifier-a5.md`.

## Verification

Passed:

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
