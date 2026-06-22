# Review - Case 2 source-production obligation canonical formula

Date: 2026-06-22.

Reviewer: xhigh scout Huygens the 2nd.

## Verdict

Pass after two documentation precision fixes.

2026-06-22 API update: this review describes the superseded constructor that
still carried a supplied next chart-family argument.  The live API removed
that argument after the true-predicate audit; see
`reproduction-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.

## Findings

First, the summaries said the theorem "removes arbitrary `Csucc/Cterm`
choices from the interface."  The Lean structure still permits arbitrary
`Csucc` and `Cterm`; the theorem gives a canonical inhabitant for the specific
formula-level choices.  The summaries now say it removes the need to choose
arbitrary `Csucc/Cterm` in this canonical constructor.

Second, the short statement card compressed the actual-width terminal-row
proof to the actual-width collapse.  The Lean proof first uses that
transported rows are original rows of the formula-level successor factor, then
uses actual-width collapse of that factor to old `C`.  The statement card and
synthesis now record that two-step reasoning.

## Scope Check

No theorem-name mismatch, source-boundary issue, or quiver leakage was found.
In the historical reviewed constructor, the continuing next chart-family
boundary remained a supplied theorem argument and was passed directly into the
obligation field.  In the current API that field is removed.  Row-exhausted
terminal rows remain transported rows, with the obligation field proved by
reflexivity in the canonical formula-level constructor.

The theorem does not construct source production, successor chart-family data,
suffixes, coverage, transition regularity, normal crossings, pole order, or
RLCT.
