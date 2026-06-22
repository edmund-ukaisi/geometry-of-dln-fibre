# Statement card - A5 Lemma 5 counted-datum classifier cardinal squeeze

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn`

## Claim

For a supplied terminal-candidate family, a supplied counted-datum classifier
on `terminalMinimumLabels` and supplied branch-label injectivity imply
terminal-minimum exactness by finite cardinality squeeze.  This gives equality
between `terminalMinimumLabels` and `branchLabelImage`, the exact finite count,
and a branch-label bijection.

## Proved

Lean combines:

- `branchLabelImage subset terminalMinimumLabels`;
- `branchLabelImage.card = a * (n + 1 - a) + 1` from branch-label
  injectivity and the supplied branch count;
- `terminalMinimumLabels.card <= a * (n + 1 - a) + 1` from the supplied
  counted-datum classifier.

The finite-set lemma `Finset.eq_of_subset_of_card_le` then identifies the two
label sets.

## Assumed

The terminal-candidate family, `a <= n+1`, the selected-width sum, a supplied
terminal-minimum counted-datum classifier, and supplied branch-label
injectivity.

## Deferred

Construction of the counted-datum classifier from Aoyagi's equations,
branch-label injectivity, source-label legality, displayed branch-family
construction, terminal source realisation, pole order, normal crossings, and
RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```
