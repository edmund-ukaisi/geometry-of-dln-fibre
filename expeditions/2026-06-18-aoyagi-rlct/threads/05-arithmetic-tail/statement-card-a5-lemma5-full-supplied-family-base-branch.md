# Statement Card - A5 Lemma 5 Full Supplied Family Base Branch

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.fullBranches`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.base_twoValueCount`

## Claim

Given the supplied nonbase branch-family boundary, encode the one base branch
as `none` and every nonbase branch as `some b`.  The resulting finite full
branch set has cardinality `a*(ell-a)+1`.  If a base `H`-chain is also supplied
with the same Lemma 4 witness obligations, that base branch satisfies Lemma
4's finite two-value count.

## Inputs

- The supplied nonbase family from the previous boundary.
- Cross-coordinate disjointness and injective erased-interval coverage for
  nonbase branches.
- For the admissible full extension, a supplied base `H`-chain satisfying:
  `H_0=m_0`, same-coordinate `Htilde` lower and upper bounds, and Lemma 4
  two-value increments.

## Proves

- The full tagged branch set `{none} ∪ ⋃_j {some b : b ∈ branches j}` has
  cardinality `a*(ell-a)+1`.
- The supplied base branch satisfies Lemma 4's finite two-value count under
  the selected-width sum hypothesis.

## Does Not Prove

- The base branch exists from Aoyagi's printed formulas.
- The nonbase or base branches are source-backed.
- Source-label legality, displayed-vector construction, Case 1(2) chart
  sequence, terminal `tilde t=0`, pole-order interpretation, normal crossings,
  or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-27.  The leading `1` in the interval-count formula
is represented here by an explicit supplied base branch; its existence and
admissibility are hypotheses, not consequences of the printed equations.
