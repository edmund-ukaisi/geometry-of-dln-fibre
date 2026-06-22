# Statement card - A5 Lemma 5 Eq5 endpoint raw value injectivity

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`

## Claim

For one interior coordinate, supplied Eq5 strict alpha-domain coverage, strict
branch values `Htilde'_j-alpha`, endpoint values, and strict alpha injectivity
force value injectivity on the Eq5 endpoint raw branch set.  Consequently the
Eq5 endpoint supplied family can be constructed while deriving both raw value
injectivity and cross-coordinate raw disjointness from supplied structured
data.

The interior-coordinate hypothesis is essential: the analogous `j=0` endpoint
raw set may have coincident upper and lower endpoint values.

## Proved

Finite value-injectivity bookkeeping for the raw endpoint branch set and a
constructor wrapper replacing raw value injectivity plus raw disjointness by
strict alpha injectivity plus component coordinate facts.

## Assumed

Base-value membership, Eq5 alpha-domain coverage, strict branch value formulas,
upper endpoint value formula, rising lower endpoint value formula, strict
alpha injectivity, and strict/upper/lower component coordinate correctness.

## Deferred

Source construction of branch records, source production of endpoint records,
source-label legality, source proof of strict alpha injectivity, base-filter
survival, counted-datum back-to-label coverage, no-extra terminal-minimum
coverage, exact order count from source, pole order, normal crossings, and RLCT
extraction.

## Cited

None; this slice is finite Lean bookkeeping over supplied hypotheses and
previously formalized definitions.

## Review

Passed independent xhigh landed-slice review by Dalton on 2026-06-22.  Review
artifact: `review-lemma5-eq5-endpoint-value-injective-a5.md`.

## Verification

Passed:

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
