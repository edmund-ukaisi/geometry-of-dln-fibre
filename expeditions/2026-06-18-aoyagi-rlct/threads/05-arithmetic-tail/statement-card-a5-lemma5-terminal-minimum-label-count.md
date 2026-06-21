# Statement Card - A5 Lemma 5 Terminal Minimum Label Count

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5MinNumerator`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.mem_terminalMinimumLabels`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_terminalMinimumLabels`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_noExtra`

## Claim

For a supplied terminal-candidate family, the supplied branch-label image is
contained in the finite set of introduced labels whose least value is zero and
whose terminal exponent equals the supplied Lemma 5 minimum numerator
`a*(n+1)*((n+1)-a)`.

If the reverse containment is supplied as a no-extra-minimizer hypothesis, and
the branch-label map is injective on `fullBranches`, then this finite
exact-minimum label set has cardinality `a*(n+1-a)+1`.

## Inputs

- A supplied terminal-candidate family.
- The selected-width sum hypothesis and `a <= n+1` for the branchwise
  terminal-exponent minimum.
- Branch-label injectivity on `fullBranches`.
- A supplied no-extra containment:

```text
terminalMinimumLabels subset branchLabelImage.
```

## Proves

- Membership in `terminalMinimumLabels` is equivalent to introduced-label
  membership plus `leastValue=0` and terminal exponent equal to
  `aoyagiLemma5MinNumerator n a`.
- `branchLabelImage subset terminalMinimumLabels`.
- Under supplied no-extra containment and supplied injectivity,
  `terminalMinimumLabels.card = a*(n+1-a)+1`.

## Does Not Prove

- Source-backed no-extra-minimizer classification.
- Source construction or injectivity of branch labels.
- Pole order, normal crossings, `lambda`, `theta`, or RLCT extraction.

## Source

Aoyagi PDF p. 6 gives the normal-crossing minimum/order reading, and pp. 22-27
motivate the terminal candidate and Lemma 5 count.  This Lean slice proves only
the finite exact-minimum-label boundary after the candidate data and no-extra
coverage have been supplied.
