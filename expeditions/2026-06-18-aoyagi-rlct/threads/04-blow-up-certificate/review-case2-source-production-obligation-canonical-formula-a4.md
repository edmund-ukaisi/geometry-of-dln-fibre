# Review - Case 2 source-production obligation canonical formula

Date: 2026-06-22.

Reviewer: xhigh scout Huygens the 2nd.

## Verdict

Pass after two documentation precision fixes.

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
The continuing next chart-family boundary remains a supplied theorem argument
and is passed directly into the obligation field.  Row-exhausted terminal rows
remain transported rows, with the obligation field proved by reflexivity.

The theorem does not construct source production, successor chart-family data,
suffixes, coverage, transition regularity, normal crossings, pole order, or
RLCT.
