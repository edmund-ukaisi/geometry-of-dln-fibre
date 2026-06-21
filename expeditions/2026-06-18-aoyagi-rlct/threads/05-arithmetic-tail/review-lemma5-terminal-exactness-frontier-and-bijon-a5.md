# Review - Lemma 5 Terminal Exactness Frontier And Bijection API

Reviewers: xhigh Lean/API audit `Herschel`; xhigh source-boundary audit
`Hubble`.

Verdict: pass after source-wording refinement.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-terminal-exactness-source-audit-a5.md`
- `statement-card-a5-lemma5-terminal-exactness-source-frontier.md`
- `reproduction-lemma5-terminal-minimum-label-bijon-a5.md`
- `statement-card-a5-lemma5-terminal-minimum-label-bijon.md`
- matching updates in `thread.md`, `priorities.md`, `threads.md`,
  `claims.md`, `synthesis.md`, and `theorem-ledger.md`

## Findings

No findings remain.

## Resolved Finding

- The first source-audit draft said Lemma 4 "forces" values into intervals and
  that PDF p. 26 "supports" the finite upper-bound shape.  This was too strong
  because Aoyagi's Lemma 4 is stated as a sufficient criterion, while Lemma 5's
  upper-bound paragraph asserts the upper count without spelling out the
  converse/classifier.  The audit and root summaries now say that Aoyagi
  asserts/invokes the upper count, but reproducing it as a source-backed
  classifier still needs the listed bridges.

## Lean/API Notes

- `branchLabel_bijOn_terminalMinimumLabels_of_exactness` uses `ha` and the
  selected-width sum only to map supplied branch labels into
  `terminalMinimumLabels`; injectivity and no-extra coverage come from
  exactness.
- `terminalMinimumLabelExactness_of_branchLabel_bijOn` correctly needs no
  selected-width sum: the bijection itself supplies injectivity and
  surjectivity onto `terminalMinimumLabels`.
- `terminalMinimumLabels_card_of_branchLabel_bijOn` legitimately omits the
  selected-width sum.  `hbij.mapsTo` supplies the forward inclusion, and the
  remaining count uses `a<=n+1` plus `hbij.injOn`.
- The names are finite and boundary-explicit; they do not claim source-backed
  exactness, pole order, normal crossings, or RLCT extraction.

## Verification

The Lean/API reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

passing.  The controller also ran the focused Lake target successfully.
