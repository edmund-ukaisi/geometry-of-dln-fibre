# Review - A4 Case 2 next-state source-product reindex

Reviewers: xhigh independent reviewer `McClintock the 2nd` for the landed
statement shape, and xhigh independent reviewer `Jason the 2nd` for the
resume-time source/ledger audit.

Status: passed after adding this durable review artifact.

## Blocking Issues

No blocking source-fidelity, formalisation, or mathematical overclaim issue was
found in the Lean statement shape.

The reviewer did flag two process issues before this file existed:

- The reproduction, statement card, thread, claim ledger, and theorem ledger
  recorded an xhigh review without a durable review artifact.
- The tracked ledgers referenced the new reproduction and statement-card docs,
  so those new docs must be staged with the ledger updates.

This file resolves the first issue.  The second is a staging/commit
discipline requirement.

## Source And Statement Review

The reviewed Lean declarations are:

```text
case2SourceOldTopSuccResidualRowEquiv
case2SourceOldTopSuccResidualColEquiv
case2DisplayedSuccessorFollowingFactor_reindex_nextSource
case2DisplayedWeightedDppp_reindex_nextSource
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct
case2DisplayedPivotFirstRHS_reindex_nextSourceProduct_mul
```

The reviewer found the slice stays inside finite row/column/product
reindexing.  In particular, the product theorem assumes the displayed
continuation bound but no `hnext` or nonempty-tail hypothesis; the residual
tail may be empty and is handled by the finite index types.

The reviewer also accepted the boundary language: the slice does not construct
`Csucc`, source-produce full `C'^(S+1)`, produce source suffixes, construct
successor charts, prove coverage or transition regularity, derive coordinate
post-data, prove normal crossings, compute pole order, prove termination, or
extract RLCT.

## Nonblocking Notes

The name `case2SourceOldTopSuccResidualColEquiv` is defensible but easy to
misread.  Keep the local docstring's clarification that these are columns of
the displayed `D'''` block but rows of the following factor.

## Verification

The reviewer ran `git diff --check` and found no whitespace problems.  A
targeted scan found no `sorry`, `axiom`, `native_decide`, or `#exit` in the
touched Lean file.

The reviewer did not independently complete a Lean build: attempted
`lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and
`lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` runs were terminated with no
diagnostics after remaining silent.
