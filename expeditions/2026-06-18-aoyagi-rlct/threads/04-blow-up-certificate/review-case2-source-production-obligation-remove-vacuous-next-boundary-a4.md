# Review - Case 2 source-production obligation removes vacuous next boundary

Date: 2026-06-22.

Reviewer: xhigh API/source reviewer `Hooke the 2nd`.

## Verdict

Pass, with API cleanup applied.

## Findings

No blocking issues.  Removing `continuing_suppliedNextChartFamily` is sound
for the current Lean API and more faithful to Aoyagi pp. 19-22.

The reviewed field was an existential over
`Case2ResidualBlockChartFamilyBoundary`, which is a predicate-only
`SelectedEntryChartFamilyBoundary`.  Since the predicates were existentially
chosen, `True` predicates inhabited the field.  It therefore did not encode
nontrivial chart regularity, coverage, transition regularity, suffix
production, or source production of the full successor object.

## Naming

The reviewer accepted

```text
SourceProductionObligation.of_formulaSuccessor_transportTerminalRows
```

as the main constructor name.  The name states exactly what the theorem does:
choose the formula-level successor following factor and transported terminal
rows.

## API Cleanup

The reviewer recommended not keeping

```text
of_formulaSuccessor_transportTerminalRows_suppliedNextChartFamily
of_formulaSuccessor_transportTerminalRows_truePredicateNextBoundary
```

as live wrappers, because their ignored next-boundary arguments would invite
the same overreading the patch fixes.  The current patch removes these names
from the Lean API.

## Residual Risk

This is interface hardening only.  It does not construct a successor affine
atlas, source-produce `Csucc` or `C'^(S+1)`, produce suffixes, prove meaningful
coverage or transition regularity, derive corrected post-data, prove normal
crossings, pole order, termination, RLCT, or repair the printed Case 2 vector
mismatch.
