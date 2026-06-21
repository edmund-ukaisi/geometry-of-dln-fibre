# Review - Lemma 5 Terminal Minimum Label Count

Reviewers: xhigh Lean/API audit `Bernoulli`; xhigh source-boundary audit
`Singer`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-terminal-minimum-label-count-a5.md`
- `statement-card-a5-lemma5-terminal-minimum-label-count.md`
- matching updates in `thread.md`, `claims.md`, `synthesis.md`, and
  `theorem-ledger.md`

## Findings

No critical, major, or minor findings.

## Audit Notes

- `terminalMinimumLabels` is correctly defined as a finite subset of
  `introducedLabelFinset`, filtered by `leastValue = 0` and terminal exponent
  equal to `aoyagiLemma5MinNumerator n a`.
- The proved direction is exactly
  `branchLabelImage subset terminalMinimumLabels`, using `ha` and
  `hselected` through the existing Lemma 4/Lemma 3 minimum bridge.
- The reverse containment
  `terminalMinimumLabels subset branchLabelImage` is correctly an explicit
  supplied no-extra-minimizer/coverage boundary.
- Branch-label injectivity is still required for the count: coverage alone
  would not prevent two supplied branches from mapping to the same source
  label.
- The theorem names avoid `theta`, `poleOrder`, `lambda`, `rlct`,
  `learningCoefficient`, and other analytic conclusions.
- The finite count is not a pole-order theorem.  Aoyagi p. 6 reads order only
  after a normal-crossing pullback with chart coverage and analytic extraction;
  those remain outside this finite-label boundary.

## Verification

Bernoulli checked that the terminal bridge type-checks.  Final focused and
full builds are recorded with the landing commit.
