# Review - Lemma 5 Branch-Label Image Count

Reviewers: xhigh Lean/API audit `Nash`; xhigh source-boundary audit `Bohr`.

Verdict: pass after API tightening.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-branch-label-image-count-a5.md`
- `statement-card-a5-lemma5-branch-label-image-count.md`
- matching updates in `thread.md`, `claims.md`, `synthesis.md`, and
  `theorem-ledger.md`

## Findings

No critical, major, or minor findings remain.

## Audit Notes

- The count is correctly stated as an image of supplied branch labels, not as
  the set of all terminal labels.
- The exact image count requires the explicit hypothesis
  `Set.InjOn C.branchLabel ↑C.fullBranches`; existing supplied fields do not
  imply label injectivity.
- `branchLabel` uses the existing `Sigma.mk s k` label representation, so
  `branchLabelImage` lives in the same type as `introducedLabelFinset`.
- The image count does not require the selected-width sum hypothesis; that
  hypothesis is used only for terminal-exponent/minimum-numerator data.
- `branchLabel_mem_introducedLabelFinset` and
  `branchLabelImage_subset_introducedLabelFinset` correctly transfer the
  supplied `introducedLabel` field to the finite introduced-label set.
- Source-side pole-order language is avoided.  At this stage the count is:
  tagged branch count; with supplied branch-label injectivity, distinct
  supplied-label image count; only with no-extra terminal-minimizer coverage
  and the cited normal-crossing extraction interface can it become `theta`.

## Verification

The focused Lean build passed:

```text
lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
```

Full-library and hygiene checks are recorded with the landing commit.
