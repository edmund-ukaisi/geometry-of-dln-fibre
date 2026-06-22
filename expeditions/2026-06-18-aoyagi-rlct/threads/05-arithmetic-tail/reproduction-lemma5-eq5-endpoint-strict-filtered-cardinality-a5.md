# Reproduction - Lemma 5 Eq5 strict endpoint filtered cardinality

Date: 2026-06-22.

Scope: one-coordinate filtered cardinality for the strictest supplied Eq5
endpoint constructor.  This fills the local API gap between the existing
general endpoint filtered count and the strictest full-branch count.  It does
not construct Eq5 branches or terminal minimum labels.

## One Coordinate

The general endpoint supplied-family constructor already gives, for an
interior coordinate `j`,

```text
(branches j).card = aoyagiLemma5IntervalSize ell a j - 1.
```

The strictest endpoint constructor is the same supplied-family constructor
with two supplied hypotheses discharged by earlier finite lemmas:

```text
raw value injectivity
  <- strict alpha injectivity + endpoint value formulas

raw cross-coordinate disjointness
  <- component branch-coordinate facts
```

Therefore the strictest constructor inherits the same one-coordinate filtered
count:

```text
((ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord ...).branches j).card
  = aoyagiLemma5IntervalSize ell a j - 1.
```

This is only the filtered branch count after erasing the supplied base value.
It does not say which source record is erased or that any source-produced
endpoint record survives the filter.

## Lean Target

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one
```

## Nonclaims

- No Eq5 branch construction.
- No source production of endpoint records.
- No source-label legality.
- No source proof of strict alpha injectivity.
- No base-filter survival theorem for a specific source record.
- No terminal-minimum label count.
- No source-backed no-extra coverage.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
