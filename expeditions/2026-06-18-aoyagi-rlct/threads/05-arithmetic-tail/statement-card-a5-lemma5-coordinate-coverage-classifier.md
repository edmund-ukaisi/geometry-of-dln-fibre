# Statement Card - A5 Lemma 5 Coordinate Coverage Classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.finset_image_filter_value_ne_eq_erase_image`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord`

## Claim

Coordinate-wise supplied value coverage can be assembled into the existing
nonbase branch-family boundary, and such a supplied family gives a counted
datum classifier once branch coordinates and tagged-classifier injectivity are
also supplied.

The finite-set identity is:

```text
(s.filter (fun b => f b != y)).image f = (s.image f).erase y.
```

This removes the supplied base value from a raw coordinate family while
preserving exactly the remaining coordinate values.

## Inputs

For `ofCoordinateValueCoverage`:

- raw coordinate branch sets `rawBranches j`;
- a value map `value : beta -> Z`;
- a supplied base value `baseValue j` in the interval at each interior
  coordinate;
- full coordinate coverage
  `(rawBranches j).image value = aoyagiHtildeIntervalValueSetNat ell a M m j`;
- injectivity of `value` on each `rawBranches j`;
- pairwise disjointness of raw branch sets at distinct interior coordinates.

For `countDatumClassifierOfBranchCoord`:

- a supplied nonbase family `F`;
- a coordinate map `branchCoord : beta -> Nat`;
- proof that every branch in `F.branches j` has coordinate `j`;
- supplied injectivity of the tagged classifier
  `F.countDatumOfBranchCoord branchCoord` on `F.fullBranches`.

## Proves

The constructor builds `AoyagiLemma5SuppliedNonbaseFamily` by filtering out
branches whose value is the supplied base value.

The classifier bridge builds:

```text
AoyagiLemma5CountDatumClassifier
  (Option beta) ell a M m F.baseValue F.fullBranches
```

and proves its `mapsTo` field from the supplied family fields and supplied
branch-coordinate equation.

## Does Not Prove

- Coordinate-wise raw value coverage from Aoyagi's printed equations.
- Source construction of the branch family.
- Source proof of branch-coordinate uniqueness.
- Injectivity of the tagged classifier from Case 1(2).
- Back-to-label coverage, terminal-label exactness, pole order, normal
  crossings, or RLCT extraction.

## Source

This is finite supplied-data assembly below Aoyagi Lemma 5's upper-bound
classifier frontier.  It follows the elementary interval-count structure on
PDF p. 26 but does not claim that the printed paragraph proves the supplied
coverage or injectivity hypotheses.
