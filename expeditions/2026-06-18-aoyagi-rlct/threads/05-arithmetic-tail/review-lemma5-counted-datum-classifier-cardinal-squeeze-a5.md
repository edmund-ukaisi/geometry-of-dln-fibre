# Review - Lemma 5 counted-datum classifier cardinal squeeze

Reviewer: xhigh Lean/API reviewer `Wegener`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`
- `statement-card-a5-lemma5-counted-datum-classifier-cardinal-squeeze.md`

## Findings

No findings.

## Lean/API Notes

The reviewer confirmed that the finite-set squeeze is correctly oriented:

```text
branchLabelImage subset terminalMinimumLabels
branchLabelImage.card = N
terminalMinimumLabels.card <= N
```

Together these give

```text
terminalMinimumLabels.card <= branchLabelImage.card,
```

so `Finset.eq_of_subset_of_card_le` identifies the finite sets.

The source-boundary wording remains conditional on supplied
`TerminalMinimumCountDatumClassifier` and supplied
`Set.InjOn C.branchLabel C.fullBranches`.  The reviewed statements and notes
do not claim a constructed classifier, counted-datum back-to-label bridge,
pole order, normal crossings, or RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```
