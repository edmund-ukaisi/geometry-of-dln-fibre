# Reproduction - Lemma 5 Eq5 endpoint branch coordinates

Date: 2026-06-22.

Scope: finite coordinate bookkeeping for the Eq5 endpoint raw branch set.  This
does not construct Aoyagi's branch records, prove source-label legality, prove
source-produced endpoint records, prove raw value injectivity, prove
cross-coordinate disjointness, prove no-extra terminal-minimum coverage, prove
pole order, prove normal crossings, or extract RLCT data.

## Raw branch-coordinate calculation

The Eq5 endpoint raw branch set at coordinate `j` is

```text
raw_j =
  if j <= a and j <= ell-a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j).
```

The lower endpoint is explicitly inserted only in the rising branch.  Without
distinctness hypotheses it could still coincide with `upper j` or a strict
branch record; this slice does not assert distinctness or survival.

Let `branchCoord : beta -> Nat` be a supplied coordinate map.  Assume:

```text
branchCoord b = j           for b in strictBranches j,
branchCoord (upper j) = j,
branchCoord (lower j) = j   if j <= a and j <= ell-a.
```

If `b in raw_j`, split on the same rising condition.

In the rising case, membership means

```text
b = upper j
or b = lower j
or b in strictBranches j.
```

The three supplied component-coordinate facts give `branchCoord b=j`.

In the non-rising case, membership means

```text
b = upper j
or b in strictBranches j,
```

and the upper/strict coordinate facts again give `branchCoord b=j`.

## Filtered supplied family

The Eq5 endpoint supplied-family constructor is an instance of
`ofCoordinateValueCoverage`.  Its stored coordinate branch set is

```text
F.branches j = raw_j.filter (fun b => value b != baseValue j).
```

Thus `b in F.branches j` implies `b in raw_j`; the base-value filter is
irrelevant for the coordinate calculation.  Applying the raw membership lemma
gives the `branchCoord_eq` hypothesis needed by the generic counted-datum
classifier constructor.

## Counted-datum classifier

The existing generic constructor

```text
F.countDatumClassifierOfBranchCoord_of_branchCoord_eq
```

builds the counted-datum classifier from the supplied family and the coordinate
correctness fact.  This slice stops at proving that coordinate correctness
fact for the Eq5 endpoint supplied family.  Downstream code can call the
existing classifier constructor directly, avoiding another long wrapper that
only mirrors the supplied-family constructor arguments.

## Lean targets

```text
aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq
```

## Nonclaims

- No construction of strict Eq5 or endpoint branch records.
- No proof that endpoint branch records are source-produced.
- No source-label legality.
- No proof of raw value injectivity or cross-coordinate disjointness.
- No proof that the branch coordinate map comes from Aoyagi's source.
- No endpoint distinctness or base-filter survival claim.
- No new counted-datum classifier constructor; use the existing generic one
  with the proved coordinate-correctness fact.
- No no-extra terminal-minimum coverage or order count.
- No pole order, normal crossings, or RLCT extraction.
