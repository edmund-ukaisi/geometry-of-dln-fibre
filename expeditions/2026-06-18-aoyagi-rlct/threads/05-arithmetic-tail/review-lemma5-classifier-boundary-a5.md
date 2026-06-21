# Review - Lemma 5 classifier-boundary slice

Reviewer: Arendt, xhigh-effort subagent.
Date: 2026-06-21.

## Scope

- `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-terminal-binary-counted-datum-maps-to-a5.md`
- `statement-card-a5-lemma5-terminal-binary-counted-datum-maps-to.md`
- `reproduction-lemma5-terminal-minimum-counted-datum-classifier-a5.md`
- `statement-card-a5-lemma5-terminal-minimum-counted-datum-classifier.md`

## Findings

None.

## Verdict

The Lean names and statements match the documented claims.

The maps-to theorem proves exactly one conditional nonbase counted-datum
membership under terminal binary-prefix-delta hypotheses and
`H_j != baseValue j`.

The terminal-minimum classifier is a supplied
`AoyagiLemma5CountDatumClassifier` on `C.terminalMinimumLabels`, and the
upper-bound theorem only applies the existing finite injection count.

No overclaims were found.  The documents consistently say these results do not
construct the source-backed classifier, prove injection or back-to-label
coverage from Aoyagi, build terminal source branches, prove branch-label
exactness, count pole order, prove normal crossings, or extract RLCT.  The
hypotheses are deliberately strong supplied-boundary hypotheses, not misleading
as exactness or source-backed results.

## Verification

The reviewer typechecked both touched Lean modules with `lake env lean`.
