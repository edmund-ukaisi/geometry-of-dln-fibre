# Review - Theorem 2 ratio-count terminal-order bridge

Date: 2026-06-22.

Reviewer: xhigh reviewer `Russell the 2nd`.

## Verdict

Pass, after naming adjustment.

## Findings

No blocking findings.

## Naming Adjustment

The reviewer noted that the initial wrapper names used `terminalLabels_card`
even though the hypotheses and proofs use `TC.terminalMinimumLabels.card`.
The Lean declarations and documentation were renamed to
`ratioCount_terminalMinimumLabels_card`.

## Scope Check

The bridge lets source-facing counts be supplied at the displayed Theorem 2
lambda.  The active-pair lower-bound certificate first proves
`D.exponentMinimum = displayed lambda`; then the A0 count-at-ratio bridge
rewrites those counts to `minCountInChart`.

The bridge does not claim chart construction, active-ratio bounds, terminal
exactness, normal crossings, pole order without A0, or RLCT extraction.

## Checks

Reviewer checks:

```text
lake build DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
git diff --check
```

The reviewer also scanned changed files for `sorry`, `axiom`, `native_decide`,
and `#exit`.

Controller closeout additionally ran focused checks, full build, and
`scripts/sorries`.
