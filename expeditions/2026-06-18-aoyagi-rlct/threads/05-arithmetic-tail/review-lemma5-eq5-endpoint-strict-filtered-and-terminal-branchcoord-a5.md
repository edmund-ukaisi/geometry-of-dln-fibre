# Review - Lemma 5 Eq5 strict filtered endpoint and endpoint-to-terminal branchcoord

Date: 2026-06-22.

Reviewer: xhigh subagent `Popper`.

## Verdict

Passed.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-endpoint-strict-filtered-cardinality-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-strict-filtered-cardinality.md`
- `reproduction-lemma5-eq5-endpoint-to-terminal-branchcoord-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-to-terminal-branchcoord.md`
- Updated ledgers: `claims.md`, `priorities.md`, `synthesis.md`,
  `theorem-ledger.md`, and `thread.md`.

## Findings

None.

## Post-Review Rename Check

After the initial review, the strict endpoint count theorem was renamed to
`ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one`
to avoid a new long-line style warning, and terminal-classifier references to
the endpoint constructor were shortened by opening the nonbase-family
namespace.  The same xhigh reviewer rechecked the resulting diff and reported
no findings.

## Review Notes

The strict endpoint count remains a filtered coordinate-cardinality
specialization.  The terminal transport requires explicit nonbase-family
equality plus a supplied `branchS` formula.  The patch does not claim source
branch construction, no-extra terminal coverage, normal crossings, pole order,
or RLCT extraction.

## Reviewer Verification

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean
git diff --check
```

All passed.
