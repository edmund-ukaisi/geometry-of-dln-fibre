# Statement card - A5 Lemma 5 Eq5 endpoint raw branches

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage`

## Claim

For each interior coordinate, supplied strict Eq5 alpha branches plus supplied
endpoint branches have raw value image equal to the same-coordinate interval.
The lower endpoint branch is included exactly in the rising case
`j <= a` and `j <= ell-a`.

The supplied nonbase-family constructor can therefore be instantiated from
Eq5 alpha-domain coverage and endpoint value equalities, while keeping
base-value membership, value injectivity, and cross-coordinate disjointness as
explicit hypotheses.

## Proved

Finite value-image coverage and the corresponding supplied-family assembly.

## Assumed

Strict alpha-domain coverage for each coordinate, strict Eq5 branch value
formulas, supplied upper endpoint values, supplied lower endpoint values in
the rising case, base-value membership, raw-branch value injectivity, and
cross-coordinate disjointness.

## Deferred

Source construction of the branch records, source-label legality,
source-backed endpoint production, injectivity/disjointness from source,
counted-datum back-to-label coverage, no-extra terminal-minimum coverage,
exact order count from source, pole order, normal crossings, and RLCT
extraction.

## Review

xhigh `Hilbert` passed with no findings.  Residual risk: this is still a
supplied-data slice and does not prove source-produced endpoint records or
raw branch injectivity/disjointness.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage`
- `lake build DLNFibre`
- `scripts/sorries`
- `git diff --check`
