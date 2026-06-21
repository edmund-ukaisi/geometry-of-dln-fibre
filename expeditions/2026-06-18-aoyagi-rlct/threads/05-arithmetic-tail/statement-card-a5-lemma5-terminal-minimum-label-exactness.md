# Statement Card - A5 Lemma 5 Terminal Minimum Label Exactness

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_exactness`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_exactness`

## Claim

For a supplied terminal-candidate family, packaged exactness consists of
branch-label injectivity on `fullBranches` and the supplied no-extra containment
`terminalMinimumLabels subset branchLabelImage`.  Under this exactness package,
the finite exact-minimum label set has cardinality `a*(n+1-a)+1`.

## Inputs

- A supplied terminal-candidate family.
- `a <= n+1`.
- The selected-width sum hypothesis.
- `TerminalMinimumLabelExactness C`.

## Proves

- `terminalMinimumLabels = branchLabelImage`.

```text
terminalMinimumLabels.card = a*(n+1-a)+1.
```

## Does Not Prove

- Source-backed branch-label injectivity.
- Source-backed no-extra-minimizer coverage.
- A normal-crossing certificate, pole order, `theta`, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 24-27, motivates the intended exact count.  This Lean
slice only packages the supplied finite exactness hypotheses already isolated
by the previous terminal-minimum-label boundary.
