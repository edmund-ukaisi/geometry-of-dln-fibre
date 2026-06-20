# Statement card - A5 Htilde chain arithmetic

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_succ`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_selectedWidthNat_last`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerHighCount`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperHighCount`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerIncrementPrefix`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperIncrementPrefix`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerIncrementPrefix_succ_sub`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperIncrementPrefix_succ_sub`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_last_eq_terminalEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_last_eq_terminalEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerChain_F_eq`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_F_eq`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeHighCount_diff_eq_intervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpper_sub_lower_eq_intervalExcess`

## Statement

Lean now formalises the finite arithmetic of Aoyagi's two displayed extremal
chains `Htilde_j` and `Htilde'_j` from the Lemma 4/Lemma 5 discussion.

With selected widths `m : Fin (ell+1) -> Z`, the lower chain subtracts
`j*(M-1)+min(j,a)` from the selected-width prefix.  The upper chain subtracts
the low-first version of the same two-value increment pattern.  The two chains
start at the common source convention `H_0=M(S_1)`, have the same terminal
endpoint expression already named as `aoyagiLemma4TerminalEndpoint`, realise
the high-first and low-first ordered increment patterns, and differ pointwise
by the Lemma 5 interval-excess formula.

## Proved

- Total selected-width and prefix-sum helpers, with a finite terminal-sum
  bridge.
- Lower and upper `Htilde` chain definitions with finite `Fin (ell+1)`
  wrappers.
- Both chains have value `m 0` at the `H_0=M(S_1)` convention.
- The lower chain increments are `M` for the first `a` positions and `M-1`
  afterwards.
- Under `a <= ell`, the upper chain increments are `M-1` for the first
  `ell-a` positions and `M` afterwards.
- Under `a <= ell`, both terminal values equal the previously defined common
  endpoint expression `aoyagiLemma4TerminalEndpoint`.
- Under `a <= ell`, the pointwise upper-minus-lower chain gap equals
  `aoyagiLemma5IntervalExcess`.

## Assumed

- A finite selected-width sequence `m` and integer `M`.
- The order parameter bound `a <= ell` where needed for the upper chain and
  terminal/gap statements.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- A source-faithful `T -> (H_j),(S_j)` correspondence.
- Proof that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the
  same-coordinate hypotheses isolated earlier.
- The two-value increment hypothesis for an arbitrary intermediate vector.
- Vector admissibility and correspondence to `lambda`.
- The terminal exponent rewrite into the Lemma 3 quadratic.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-htilde-chain-arithmetic-a5.md`.
- Review artifact:
  `review-htilde-chain-arithmetic-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
