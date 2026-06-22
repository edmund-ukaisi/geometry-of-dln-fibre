# Statement card - A5 Lemma 5 Eq5 endpoint branch coordinates

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq`

## Claim

The Eq5 endpoint raw branch set inherits a supplied coordinate map from its
strict, upper-endpoint, and explicitly inserted rising lower-endpoint component
records.  After filtering out the supplied base value, the same coordinate
correctness gives the `branchCoord_eq` input to the existing generic
counted-datum classifier.

## Proved

Finite membership dispatch through the conditional raw branch set and
inheritance through the base-value filter.

## Assumed

Strict branch coordinate correctness, upper endpoint coordinate correctness,
rising-case lower endpoint coordinate correctness, base-value membership, raw
value injectivity, cross-coordinate disjointness, Eq5 alpha-domain coverage,
and endpoint value equalities.

## Deferred

Source construction of branch records, source production of endpoint records,
source-label legality, source proof of the coordinate map, source proof of raw
value injectivity/disjointness, endpoint distinctness, base-filter survival,
counted-datum back-to-label coverage, no-extra terminal-minimum coverage, exact
order count from source, a dedicated Eq5 counted-datum classifier wrapper, pole
order, normal crossings, and RLCT extraction.

## Review

xhigh `Chandrasekhar` passed with no findings after the lower-endpoint wording
was tightened.  Residual risk: without distinctness hypotheses, `lower j`
could still occur in the non-rising raw finset by collision with another
record; the theorem does not assert distinctness.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
