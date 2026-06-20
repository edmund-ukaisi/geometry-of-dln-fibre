# Statement card - A5 Htilde interval bounds

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_le_upperChain`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalOffsets`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalOffsets_card`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSet`
- `DLNFibre.DLN.Aoyagi.aoyagiHtilde_mem_intervalValueSet_iff_bounds`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSet_card`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeChainBounds_mem_intervalValueSet`
- `DLNFibre.DLN.Aoyagi.aoyagiHtilde_interval_mem_of_sameCoordinateChain`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_F_twoValue`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_F_twoValue`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_HtildeChainBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_HtildeChainBounds_freeHighCount_lemma3A_eq_min`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_twoValueCount`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_twoValueCount`

## Statement

Lean now proves same-coordinate consequences of the displayed `Htilde` and
`Htilde'` chains.  The lower chain is pointwise below the upper chain, and the
finite set of integer values between them at coordinate `j` has cardinality
`aoyagiLemma5IntervalSize ell a j`.

If an intermediate `H`-chain is squeezed between the displayed chains in the
same coordinates, then `H_ell=0` under Definition 3's selected-width sum.  The
existing Lemma 4 count and Lemma 3 bridge can therefore be applied under the
still-explicit two-value increment hypothesis.

## Proved

- Terminal zero for each displayed chain under `a <= ell` and the
  selected-width sum.
- Pointwise same-coordinate order `Htilde <= Htilde'`.
- Offset intervals `{0,...,excess_j}` have cardinality equal to the displayed
  Lemma 5 interval size.
- The integer value set between the displayed chain values has the same
  cardinality.
- Membership in that value set is equivalent to the same-coordinate bounds
  `Htilde_j <= H_j <= Htilde'_j`.
- Supplied componentwise vector bounds imply interval-value membership when a
  coordinate map from chain positions to vector coordinates is supplied.
- Same-coordinate chain bounds imply `H_ell=0`.
- Both displayed chains themselves satisfy the finite two-value increment
  count.
- Same-coordinate chain-bound wrappers feed the existing Lemma 4 count and
  Lemma 3 free-count bridge, while still assuming the arbitrary-chain
  two-value increment hypothesis.

## Assumed

- The selected-width sum and `a <= ell` for terminal and interval-bound
  consequences.
- For intermediate-chain count wrappers, the two-value increment hypothesis.
- For vector-to-interval membership, an explicit coordinate map and
  coordinate equations.

## Cited

- None in Lean.  This is finite arithmetic and conditional bookkeeping.

## Deferred

- A source-faithful `T -> (H_j),(S_j)` correspondence.
- Proof that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the same
  chain coordinates.
- The two-value increment hypothesis for arbitrary intermediate vectors.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-htilde-interval-bounds-a5.md`.
- Review artifact:
  `review-htilde-interval-bounds-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
