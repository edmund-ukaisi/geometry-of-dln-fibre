# Review - Lemma 5 Eq5 endpoint raw branches

Date: 2026-06-22.

Reviewer: xhigh `Hilbert`.

Verdict: pass.  No mathematical/formalisation mismatches or doc overclaims
found.

## Checks

- The rising split matches the endpoint-deficit lemmas: the lower endpoint is
  inserted exactly when `j <= a` and `j <= ell-a`.
- The non-rising branch uses `offsets = interval.erase upper`.  The rising
  branch uses `insert lower offsets = interval.erase upper`, then inserts the
  upper endpoint using interval membership.
- The supplied-family wrapper proves the raw `value_image` field from
  alpha-domain coverage and endpoint equalities before passing it into
  `AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage`; it does not
  assume raw coordinate coverage directly.
- The `value_injective` and `branches_pairwiseDisjoint` hypotheses are stated
  over exactly the same `aoyagiLemma5Eq5EndpointRawBranches` used by the
  coverage theorem and constructor.
- The notes and docstrings keep source construction, source-label legality,
  endpoint production, injectivity/disjointness, pole order, normal crossings,
  and RLCT extraction outside the claim.

## Residual Risk

This remains a supplied-data slice.  It does not prove that Aoyagi's source
construction produces the endpoint branch records, nor that the raw branch
sets are injective or pairwise disjoint from labels.
