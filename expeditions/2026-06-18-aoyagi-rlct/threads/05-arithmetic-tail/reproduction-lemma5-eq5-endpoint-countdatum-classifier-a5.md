# Reproduction - Lemma 5 Eq5 endpoint counted-datum classifier

Date: 2026-06-22.

Scope: finite classifier packaging for the supplied Eq5 endpoint nonbase family
constructed from strict alpha-domain coverage, endpoint values, strict alpha
injectivity, and component coordinate facts.  This does not construct Aoyagi's
branch records, prove source labels, prove terminal-minimum coverage, prove an
order count, prove pole order, prove normal crossings, or extract RLCT data.

## Input family

The strictest endpoint constructor currently builds

```text
F =
  ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

from the following supplied data:

```text
a <= ell,
baseValue_mem,
strict Eq5 alpha-domain coverage,
strict branch values Htilde'_j - alpha,
upper endpoint values,
rising lower endpoint values,
strict alpha injectivity,
component coordinate facts for strict/upper/lower records.
```

Earlier Lean slices derive:

```text
raw value_image coverage,
raw value injectivity,
raw cross-coordinate disjointness,
filtered branch-coordinate correctness.
```

## Branch-coordinate correctness

For `b in F.branches j`, unfolding the constructor shows that `b` lies in

```text
filter (fun b => value b != baseValue j) (raw_j).
```

The filter only removes records, so `b in raw_j`.  The raw branch-coordinate
adapter then gives

```text
branchCoord b = j.
```

No endpoint record is shown to survive the filter; this is only a one-way
membership statement.

## Counted-datum classifier

The generic supplied-family API already defines

```text
F.countDatumClassifierOfBranchCoord_of_branchCoord_eq branchCoord
```

once branch-coordinate correctness is available.  Applying the branch-coordinate
theorem above gives a classifier

```text
Option beta -> Option (Sigma Nat Int)
```

on the supplied full branch set `F.fullBranches`.  The base branch maps to
`none`; a nonbase branch `b` maps to

```text
some ⟨branchCoord b, F.value b⟩.
```

Its `mapsTo` and injectivity fields come from the supplied-family fields and
the already-proved branch-coordinate correctness.  This is not a classifier
from terminal-minimum source labels and does not prove no-extra coverage.

## Lean targets

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

## Nonclaims

- No construction of strict Eq5 or endpoint branch records.
- No source-label legality or source-produced coordinate map.
- No endpoint distinctness or base-filter survival theorem.
- No terminal-minimum label classifier or back-to-label coverage.
- No no-extra order count, pole order, normal crossings, or RLCT extraction.
