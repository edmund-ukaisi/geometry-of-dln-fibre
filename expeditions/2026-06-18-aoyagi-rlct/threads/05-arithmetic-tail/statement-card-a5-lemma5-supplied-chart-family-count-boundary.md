# Statement Card - A5 Lemma 5 Supplied Chart-Family Count Boundary

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleNonbaseFamily`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5SuppliedNonbaseFamily_count`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5SuppliedNonbaseFamily_biUnion_count`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount`

## Claim

If, for every interior coordinate `j=1,...,ell-1`, a supplied finite branch
family bijects onto the same-coordinate `Htilde` interval with one supplied
base value removed, then the aggregate indexed nonbase branch count is
`a*(ell-a)+1` after adding the one base branch.  If the coordinatewise branch
sets are also supplied disjoint, the same formula counts their finite union.

## Inputs

- A supplied finite branch set `branches j` for each interior coordinate.
- A supplied value map that is injective on each `branches j`.
- A supplied base value in each interval value set.
- A supplied image equality saying the branch values are exactly the interval
  value set with that base value erased.
- Supplied cross-coordinate disjointness for the finite-union count.
- For the admissible extension, explicit branchwise `H`-chain obligations:
  `H_0=m_0`, same-coordinate `Htilde` lower and upper bounds, Lemma 4
  two-value increments, and equality between the counted value and the
  branch's `H_j`.

## Proves

- At each interior coordinate, the supplied nonbase branch set has cardinality
  `|I_j|-1`.
- Summing over the interior coordinates gives
  `1 + sum_j |branches j| = a*(ell-a)+1`.
- With the supplied disjointness field, the finite union satisfies
  `1 + |union_j branches j| = a*(ell-a)+1`.
- Each branch in the admissible extension satisfies Lemma 4's finite two-value
  count under the selected-width sum hypothesis.

## Does Not Prove

- The supplied branch family exists.
- Aoyagi's printed equations `(3)`, `(4)`, or `(5)` satisfy the supplied
  fields.
- Source-label legality, displayed-vector construction, Case 1(2) chart
  sequence, terminal `tilde t=0`, pole-order interpretation, normal crossings,
  or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-27.  The interval arithmetic is source-backed and
already formalised; the chart-family realisation is explicitly supplied here
because the printed-equation obstruction checkpoint prevents using equations
`(3)`, `(4)`, and `(5)` as complete Lemma 4 witnesses as printed.
