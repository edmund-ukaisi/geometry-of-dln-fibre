# Review - Lemma 5 upper-bound classifier exactness wrappers

Reviewers: xhigh pen-and-paper scout `Lovelace`; xhigh Lean/API reviewer
`Sartre`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-upper-bound-classifier-exactness-a5.md`
- `statement-card-a5-lemma5-upper-bound-classifier-exactness.md`

## Findings

No findings.

## Pen-And-Paper Check

The pen-and-paper scout reduced the slice to finite-set bookkeeping with

```text
B = C.fullBranches
f = C.branchLabel
I = C.branchLabelImage = B.image f
T = C.terminalMinimumLabels.
```

`UpperBoundClassifier C` is exactly the no-extra containment `T subset I`.
The existing supplied-candidate theorem gives `I subset T`.  Therefore
`T = I`.  With supplied `Set.InjOn f B`, maps-to, injectivity, and
surjectivity give `Set.BijOn f B T`; counting then uses the supplied
full-branch count.

The scout emphasized that classifier construction, branch-label injectivity,
and any counted-datum back-to-label bridge must remain supplied.  Cardinal
equality alone is not a replacement for a bijection.

## Lean/API Check

The Lean/API reviewer found no source-fidelity or API issue in the four new
declarations:

- `terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier`;
- `terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier`;
- `terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn`;
- `branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier`.

The reviewer confirmed that the theorem statements and docstrings do not imply
a source-backed Lemma 5 no-extra claim, pole order, normal crossings, or RLCT
extraction.  The only residual risk is future readability: these are strong
convenience wrappers, so callers must keep the supplied classifier and
injectivity hypotheses visible.

## Verification

The focused module check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```
