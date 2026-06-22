# Reproduction - Lemma 5 Eq5 endpoint filtered cardinality

Date: 2026-06-22.

Scope: finite cardinality of the filtered supplied Eq5 endpoint branch family.
This is downstream of the raw endpoint branch coverage/count slices and the
generic supplied nonbase-family count.  It does not construct Eq5 branches,
prove endpoint records are source-produced, prove source-label legality, prove
terminal-minimum label coverage, prove no-extra coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT data.

## One Coordinate

The supplied endpoint constructor starts with a raw coordinate family:

```text
raw_j = aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower j.
```

The constructor for `AoyagiLemma5SuppliedNonbaseFamily` filters out the
supplied base value at coordinate `j`:

```text
branches j = raw_j.filter (fun b => value b != baseValue j).
```

The generic supplied-family theorem already proves:

```text
(branches j).card =
  (aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1
```

because `value` is injective on the filtered coordinate family, the filtered
value image is the same-coordinate interval with `baseValue j` erased, and
`baseValue j` is supplied to lie in the interval.

For an interior coordinate `j in Icc 1 (ell-1)`, we have `j < ell+1`, so the
Nat-indexed Htilde interval value set has cardinality:

```text
aoyagiLemma5IntervalSize ell a j.
```

Substitution gives the endpoint-shaped filtered count:

```text
(ofEq5AlphaIndexedEndpointCoverage ...).branches j).card =
  aoyagiLemma5IntervalSize ell a j - 1.
```

This counts only the filtered supplied branch set at one coordinate, not raw
branches and not terminal-minimum labels.

## Full Tagged Branch Set

The generic supplied nonbase-family API defines:

```text
fullBranches = insert none (biUnion_j (branches j).image some).
```

The supplied base branch contributes the leading `1`, and the generic
disjoint-union count gives:

```text
fullBranches.card = a * (ell-a) + 1.
```

The endpoint wrapper specializes this to `ofEq5AlphaIndexedEndpointCoverage`.
The strictest wrapper specializes further to
`ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord`, where raw
value injectivity is derived from supplied strict alpha injectivity and raw
disjointness is derived from supplied component-coordinate facts.

## Lean Targets

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card
```

## Nonclaims

- No Eq5 branch construction.
- No source production of strict or endpoint records.
- No source-label legality.
- No base-filter survival theorem for a specific source record.
- No terminal-candidate or terminal-minimum label count.
- No source-backed no-extra coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
