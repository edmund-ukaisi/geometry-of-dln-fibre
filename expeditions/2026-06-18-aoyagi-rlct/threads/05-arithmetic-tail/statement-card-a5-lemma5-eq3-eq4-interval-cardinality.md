# Statement Card - A5 Lemma 5 Eq3/Eq4 Interval Cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two`

## Claim

For one rising-coordinate interval, a supplied Eq3-shaped upper component,
supplied Eq4 lower endpoint, and strict Eq5 offset set have cardinality equal
to the interval size.  In the rising region, this is equivalently the strict
Eq5 offset-set cardinality plus two.

## Inputs

- Guards `1 <= ell`, `1 <= p`, `p <= a`, and `p <= ell-a`.
- Source-selected sum and strict selected-width hypotheses.
- Supplied Eq3-shaped piecewise certificate.
- Supplied Eq4 piecewise certificate.

## Proves

- The supplied three-piece finite set has cardinality
  `aoyagiLemma5IntervalSize ell a p`.
- The same cardinality is the strict Eq5 offset-set cardinality plus `2` in
  the rising region.

## Does Not Prove

- Eq3 or Eq4 source-label legality.
- Construction of Eq3, Eq4, or Eq5 displayed vectors.
- All-coordinate coverage, all-branch packaging, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)`, `(4)`, and `(5)`, PDF pp. 26-27, represented by
supplied one-coordinate certificate data and finite cardinality arithmetic.
