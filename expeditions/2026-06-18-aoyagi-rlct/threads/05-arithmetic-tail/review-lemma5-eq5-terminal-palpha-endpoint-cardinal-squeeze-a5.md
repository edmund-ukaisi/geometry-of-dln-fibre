# Review - Lemma 5 Eq5 terminal pAlpha endpoint cardinal squeeze

Date: 2026-06-22.

Reviewer: Lagrange, xhigh hardener review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`
- `statement-card-a5-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze.md`

## Verdict

Pass.

The two new Lean statements are thin compositions:

- counted-datum injectivity is supplied structurally by
  `terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn`;
- branch-label injectivity is supplied structurally by
  `branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase`;
- both are passed into the existing finite cardinal-squeeze wrappers.

The hypotheses still explicitly require terminal Eq5 payloads for every
terminal-minimum label, terminal `(p, alpha)` injectivity, branch alpha
injectivity, branch block/formula data, terminal-label nonbase inequality, and
the terminal-endpoint base label.

## Nonclaims Checked

The slice does not construct source branches, source payloads, source
injectivity, counted-datum back-to-label data, pole order, normal crossings, or
RLCT.  It proves conditional `TerminalMinimumLabelExactness` and exact
cardinality only under the supplied hypotheses.

## Residual Risk

Documentation must continue to describe this as a finite cardinal squeeze under
supplied hypotheses, not as source-backed no-extra coverage.  The older
structured-injection adapter ledger row should remain adapter-only; this slice
is the separate conditional exactness/cardinality composition.
