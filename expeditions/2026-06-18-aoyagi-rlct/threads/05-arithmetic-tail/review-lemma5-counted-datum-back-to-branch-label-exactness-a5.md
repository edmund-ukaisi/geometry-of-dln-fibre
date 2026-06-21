# Review - Lemma 5 counted datum back-to-branch-label exactness

Date: 2026-06-21.

Reviewer: xhigh independent reviewer `McClintock`.

## Verdict

Pass.  No blocking Lean, mathematical-scope, source-fidelity, naming, or
bedrock issue was found.

## Audit

The wrappers

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel
```

are mathematically correct and scoped as supplied finite exactness only.
The first theorem converts the supplied back-to-label witness into the existing
`UpperBoundClassifier`, then packages it with supplied branch-label
injectivity.  The second theorem correctly adds `a<=n+1` and the
selected-width sum to obtain the easy inclusion from branch labels to
terminal-minimum labels and hence exact cardinality.

The hypotheses are appropriate.  Branch-label injectivity is required for
exactness and exact cardinality.  The selected-width sum is required only for
the exact cardinality wrapper, not for the no-extra packaging itself.

The theorem docstrings, statement card, reproduction note, and ledgers do not
claim source construction of the counted-datum classifier, branch-coordinate
map, back-to-label bridge, or branch-label injectivity.  They also do not
claim pole order, normal crossings, or RLCT extraction.

## Verification

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
git diff --check
```

passing.  The controller also ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
lake build DLNFibre
./scripts/sorries
git diff --check
```

with the build and scanner passing; the full build emitted only pre-existing
Core linter warnings.
