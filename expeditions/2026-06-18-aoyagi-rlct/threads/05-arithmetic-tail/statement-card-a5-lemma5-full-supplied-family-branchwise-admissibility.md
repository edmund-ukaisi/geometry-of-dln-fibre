# Statement Card - A5 Lemma 5 Full Supplied Family Branchwise Admissibility

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullH`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount`

## Claim

For the supplied full tagged branch family, `fullH none` is the supplied base
`H`-chain and `fullH (some b)` is the inherited nonbase `H b` chain.  Every
tagged full branch in `fullBranches` satisfies Lemma 4's finite two-value
count.

## Inputs

- The supplied full admissible family.
- A tagged branch `x ∈ fullBranches`.
- The selected-width sum hypothesis and `a <= ell`.

## Proves

- Nonbase membership is characterized by existence of an interior coordinate
  `j` with `b ∈ branches j`.
- The tagged full branch's `H`-chain satisfies the Lemma 4 two-value count.

## Does Not Prove

- The tagged branch family exists from Aoyagi's printed formulas.
- Source-label legality, displayed-vector construction, Case 1(2) chart
  sequence, terminal `tilde t=0`, pole-order interpretation, normal crossings,
  or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-27.  This is a supplied-data wrapper around the
branchwise Lemma 4 obligations; it is not a reconstruction of equations `(3)`,
`(4)`, or `(5)`.
