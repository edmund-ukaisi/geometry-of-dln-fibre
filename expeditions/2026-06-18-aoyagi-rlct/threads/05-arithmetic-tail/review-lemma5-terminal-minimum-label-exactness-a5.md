# Review - Lemma 5 Terminal Minimum Label Exactness

Reviewers: xhigh Lean/API audit `Anscombe`; xhigh source-boundary audit
`Turing`.

Verdict: pass after field-name and equality-theorem refinement.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-terminal-minimum-label-exactness-a5.md`
- `statement-card-a5-lemma5-terminal-minimum-label-exactness.md`
- matching updates in `thread.md`, `claims.md`, `synthesis.md`, and
  `theorem-ledger.md`

## Findings

No critical, major, or minor findings remain.

## Audit Notes

- A finite exactness package is the honest next step.  A Lean
  normal-crossing-to-RLCT extraction interface should wait for actual finite
  chart data, nonvanishing units, Jacobian/weight exponents, cover/global
  minimum handling, and zero-exponent conventions.
- The exactness package correctly stays nested under
  `AoyagiLemma5SuppliedTerminalCandidateFamily`.
- The fields are proposition-shaped:
  `branchLabel_injOn` and
  `terminalMinimumLabels_subset_branchLabelImage`.
- The equality theorem
  `terminalMinimumLabels_eq_branchLabelImage_of_exactness` is exposed because
  it is the reusable finite fact; the cardinality theorem is then a direct
  consequence plus the existing branch-label image count.
- The package does not prove exactness from Aoyagi's printed equations.  It
  wraps supplied branch-label injectivity and supplied no-extra containment.
- The layer avoids `theta`, `poleOrder`, `lambda`, `rlct`,
  `normalCrossing`, and `learningCoefficient` names.

## Verification

The focused terminal bridge build passes.  Final full-library and hygiene
checks are recorded with the landing commit.
