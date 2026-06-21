# Review - A4 Case 2 constructed source following factor

Status: pass.

Reviewer: xhigh independent audit, 2026-06-21.

## Scope Audited

- Lean declarations in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  - `case2DisplayedConstructedSourceFollowingFactor`
  - `case2DisplayedSourceFollowingFactor_constructed`
  - `case2DisplayedPaperCprime_of_constructedSourceFollowingFactor`
  - `Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP`
- Reproduction note:
  `reproduction-case2-constructed-source-following-factor-a4.md`.
- Statement card:
  `statement-card-a4-case2-constructed-source-following-factor.md`.
- Thread, ledger, synthesis, claims, and priorities updates naming this
  checkpoint.

## Verdict

No findings.

The Lean statements prove only the claimed finite source-coordinate
zero-extension, restriction recovery, constructed-source
`Q^-1*(Q*Cprime)=Cprime` direction, and supplied-boundary `Q/P` wrapper.  The
constructor zero-extends outside `case2ResidualBlockCols`; restricting with
`case2DisplayedSourceFollowingFactor` reads only residual columns and recovers
the supplied pivot-first matrix.

The reindexing is conceptually correct: `pivotFirstIndexEquiv` maps pivot-first
indices into the residual-column subtype, and the constructor uses `.symm` to
pull a residual source column back to the supplied pivot-first index.

The supplied-boundary wrapper honestly reuses the existing
`sourceDisplayedQP_constructedCprime_paperQP` theorem and rewrites the
constructed source function back to its restricted pivot-first matrix.  It does
not change hypotheses or smuggle chart-production claims.

## Nonclaims Checked

The checkpoint does not claim:

- full source production of the next `C'^(S+1)`;
- recurrence or exponent post-data from coordinates;
- successor chart-family construction;
- chart coverage, coordinate regularity, or Jacobian arithmetic;
- normal crossings or RLCT extraction;
- arbitrary-pivot coverage;
- terminal relabeling;
- repair of the printed Case 2 vector.

## Verification

The reviewer reported passing:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
git diff --check
```

The reviewer did not run a full library build.
