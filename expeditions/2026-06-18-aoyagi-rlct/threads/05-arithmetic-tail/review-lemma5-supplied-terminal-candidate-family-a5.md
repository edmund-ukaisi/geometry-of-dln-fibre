# Review - Lemma 5 Supplied Terminal Candidate Family

Reviewer: xhigh subagent `Descartes`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- `reproduction-lemma5-supplied-terminal-candidate-family-a5.md`
- `statement-card-a5-lemma5-supplied-terminal-candidate-family.md`
- matching updates in `thread.md`, `claims.md`, `synthesis.md`, and
  `theorem-ledger.md`

## Findings

No critical, major, or minor findings.

## Checks

- `leastValue = 0` is a supplied field, not presented as a source proof of
  terminal `tilde t=0`.
- `introducedLabel` is an appropriate supplied source-label legality proxy: it
  includes actual-width label legality and introduced-state membership.
- The docs do not derive labels from equations `(3)`, `(4)`, or `(5)`.
- The branch count remains a `fullBranches.card` statement and is not
  interpreted as pole order without injectivity/no-extra-minimizer data.
- The theorem names include `Supplied`/`Candidate` where needed and do not
  overclaim.

## Verification

Descartes ran:

```text
git status --short --branch
git diff --stat
git diff --check
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
```

The Lean checks passed from the `lean/` project root.  An initial Lake attempt
from the worktree root failed only because the Lake project is rooted in
`lean/`.
