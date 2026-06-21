# Reproduction - coordinate coverage to counted-datum classifier

Date: 2026-06-21.

Scope: finite supplied-data assembly for Aoyagi Lemma 5.  This does not
construct Aoyagi's displayed branch family, prove source-vector coverage,
prove Case 1(2) uniqueness, prove back-to-label coverage, prove pole order,
normal crossings, or extract RLCT data.

## Coordinate Coverage

Suppose that for each interior coordinate `j=1,...,ell-1` we have a supplied
raw branch set

```text
rawBranches_j
```

with a value map

```text
value : beta -> Z
```

such that

```text
value(rawBranches_j) = I_j,
```

where `I_j` is the same-coordinate interval value set
`aoyagiHtildeIntervalValueSetNat ell a M m j`.

Assume also:

- the supplied base value `baseValue j` lies in `I_j`;
- `value` is injective on `rawBranches_j`;
- raw branch sets at different interior coordinates are disjoint.

The nonbase family should count every value in `I_j` except the base value.
Define

```text
branches_j = { b in rawBranches_j | value b != baseValue j }.
```

The elementary set identity is

```text
value(branches_j) = value(rawBranches_j) \ {baseValue j}.
```

In finite-set notation:

```text
(rawBranches_j.filter (fun b => value b != baseValue j)).image value
  = (rawBranches_j.image value).erase (baseValue j).
```

Using the supplied full-image equality, this becomes exactly the
`value_image` field of `AoyagiLemma5SuppliedNonbaseFamily`.

Injectivity and cross-coordinate disjointness are inherited by passing to
subsets.

## Counted-Datum Classifier

Given a supplied nonbase family `F`, the full branch set is

```text
none        -- base branch
some b      -- nonbase branch
```

Assume a supplied coordinate map

```text
branchCoord : beta -> Nat
```

such that every `b in F.branches j` satisfies `branchCoord b = j`.

Define the counted-datum classifier on full branches by

```text
none    |-> none
some b  |-> some (branchCoord b, F.value b).
```

For `none`, membership in the counted datum set is the base-datum theorem.
For `some b`, membership in `F.fullBranches` gives some interior `j` with
`b in F.branches j`; the coordinate hypothesis rewrites `branchCoord b = j`,
and `F.value_image` gives

```text
F.value b in I_j.erase (F.baseValue j).
```

Thus the classifier maps into `aoyagiLemma5CountDatumSet`.

The injectivity needed for `AoyagiLemma5CountDatumClassifier` is still
supplied.  This is deliberate: the printed Aoyagi paragraph does not prove the
Case 1(2) nonduplication/back-to-label statement needed to derive it.

## Formalisation Boundary

The formal slice should add:

```text
finset_image_filter_value_ne_eq_erase_image
AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord
```

The result is a cleaner supplied `mapsTo`/classifier assembly.  It is not the
source-backed no-extra classifier for terminal lambda-vectors.
