# Reproduction - Lemma 5 Terminal Minimum Label Exactness

Status: supplied-data package; ready for a narrow Lean wrapper.

The previous slice proved the exact finite minimum-label count from two
supplied hypotheses:

1. supplied branch-label injectivity on the tagged branch set;
2. supplied no-extra containment from all minimum labels to the branch-label
   image.

This note packages those two hypotheses as reusable finite exactness data.

## Exactness Data

For a supplied terminal-candidate family `C`, define exactness to mean:

```text
branchLabel_injOn:
  branchLabel is injective on fullBranches

terminalMinimumLabels_subset_branchLabelImage:
  terminalMinimumLabels subset branchLabelImage
```

The first field says distinct tagged supplied branches give distinct source
labels.  The second field is the no-extra-minimizer boundary: every introduced
label with least value zero and terminal exponent equal to the supplied
minimum numerator occurs among the supplied branch labels.

## Consequence

The previous theorem already proves

```text
branchLabelImage subset terminalMinimumLabels.
```

Combining that with `terminalMinimumLabels_subset_branchLabelImage` gives
equality between the finite minimum-label set and the supplied branch-label
image.  Combining equality with branch-label injectivity and the supplied
branch count gives

```text
terminalMinimumLabels.card = a*(n+1-a)+1.
```

The new theorem is only a convenience wrapper around
`terminalMinimumLabels_card_of_noExtra`; it proves no new source fact.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_exactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_exactness
```

## Kill Conditions

- Do not treat exactness as proved from Aoyagi's printed equations.
- Do not use exactness as a normal-crossing certificate.
- Do not call the resulting finite label count `theta` or pole order without
  the separate normal-crossing-to-RLCT extraction boundary.

## Nonclaims

- No source-backed injectivity or no-extra-minimizer classification is proved.
- No chart coverage, Jacobian arithmetic, normal crossings, or RLCT extraction
  is proved.
