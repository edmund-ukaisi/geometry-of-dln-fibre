# Reproduction - Lemma 5 Eq5 endpoint branch-coordinate disjointness

Date: 2026-06-22.

Scope: finite disjointness bookkeeping for the Eq5 endpoint raw branch sets.
This does not construct Aoyagi's branch records, prove source-label legality,
prove endpoint records are source-produced, prove raw value injectivity, prove
base-value survival, prove no-extra terminal-minimum coverage, prove pole
order, prove normal crossings, or extract RLCT data.

## Raw branch sets

For each interior coordinate `j in Finset.Icc 1 (ell - 1)`, the Eq5 endpoint
raw branch set is

```text
raw_j =
  if j <= a and j <= ell-a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j).
```

The lower endpoint is explicitly inserted only in the rising branch.  No
distinctness from `upper j` or the strict records is asserted.

## Coordinate disjointness calculation

Let `branchCoord : beta -> Nat` be a supplied coordinate map.  Assume the
component coordinate facts:

```text
branchCoord b = j           for b in strictBranches j,
branchCoord (upper j) = j,
branchCoord (lower j) = j   if j <= a and j <= ell-a.
```

The previous raw branch-coordinate lemma proves:

```text
b in raw_j -> branchCoord b = j.
```

Now suppose `i != j` are interior coordinates and `b in raw_i ∩ raw_j`.
Applying the coordinate lemma to the first membership gives
`branchCoord b = i`; applying it to the second membership gives
`branchCoord b = j`.  Hence `i=j`, contradiction.  Therefore

```text
Disjoint raw_i raw_j.
```

This argument tolerates duplicate records inside one coordinate raw set.  It
also tolerates the lower endpoint record appearing in a non-rising raw set only
by collision with the upper record or a strict record: membership in that set
then follows through the upper/strict alternative and still has coordinate
`j`.

## Constructor wrapper

The Eq5 endpoint supplied-family constructor currently keeps
cross-coordinate raw-branch disjointness as an explicit hypothesis.  The
disjointness theorem above can supply that field from the component coordinate
facts.  A wrapper may therefore replace

```text
branches_pairwiseDisjoint
```

by the component coordinate hypotheses while leaving all other supplied data
unchanged:

```text
baseValue_mem,
alpha-domain coverage,
endpoint value equalities,
raw value injectivity.
```

Value injectivity is not implied by coordinate disjointness.  Base-value
filtering is not a survival theorem.  The wrapper constructs only the same
supplied nonbase family boundary with a narrower disjointness input.

## Lean targets

```text
aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord
```

## Nonclaims

- No construction of strict Eq5 or endpoint branch records.
- No proof that endpoint branch records are source-produced.
- No source-label legality.
- No proof of raw value injectivity.
- No endpoint distinctness or base-filter survival claim.
- No no-extra terminal-minimum coverage or order count.
- No pole order, normal crossings, or RLCT extraction.
