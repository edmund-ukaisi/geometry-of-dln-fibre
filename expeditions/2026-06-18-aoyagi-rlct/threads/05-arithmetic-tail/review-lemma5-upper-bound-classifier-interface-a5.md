# Review - Lemma 5 Upper-Bound Classifier Interface

Reviewer: Socrates, xhigh effort.

Status: passed after correction.

## Scope

Reviewed:

- `reproduction-lemma5-upper-bound-classifier-interface-a5.md`
- `statement-card-a5-lemma5-upper-bound-classifier-interface.md`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`

The review checked for mathematical overclaim, source-boundary clarity, and
Lean API soundness.

## Finding

The first version of `terminalMinimumLabels_card_le_of_upperBoundClassifier`
unnecessarily required branch-label injectivity.  The upper bound follows from
the supplied classifier and the branch count alone:

1. the classifier gives
   `terminalMinimumLabels.card <= branchLabelImage.card`;
2. `Finset.card_image_le` gives
   `branchLabelImage.card <= fullBranches.card`;
3. the supplied full-branch count gives
   `fullBranches.card = a*(n+1-a)+1`.

Requiring injectivity blurred the intended separation between upper-bound
classification and exactness/nonduplication.

## Correction

The theorem was sharpened so that
`terminalMinimumLabels_card_le_of_upperBoundClassifier` assumes only
`a <= n+1` and `UpperBoundClassifier C`.  Branch-label injectivity is now
reserved for `branchLabelImage_card` and
`terminalMinimumLabelExactness_of_upperBoundClassifier`.

The reproduction note, statement card, A5 thread log, synthesis, and theorem
ledger were updated to match this boundary.

## Verdict

No remaining source-backed classifier overclaim found.  The Lean comments and
artifact prose now distinguish:

- upper inequality: supplied classifier only;
- exactness/equality: supplied classifier plus supplied branch-label
  injectivity, together with the previously proved easy inclusion.

The slice remains below the source frontier.  It does not prove the
label-to-vector bridge, minimum-to-lambda bridge, interval classifier, Case
1(2) uniqueness, back-to-label bridge, pole order, normal crossings, or RLCT
extraction.
