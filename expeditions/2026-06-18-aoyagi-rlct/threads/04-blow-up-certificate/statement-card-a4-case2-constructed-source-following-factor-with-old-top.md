# Statement card - A4 Case 2 constructed source following factor with old top rows

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedConstructedSourceFollowingFactorWithOldTop`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopBlock_constructedWithOldTop`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceFollowingFactor_constructedWithOldTop`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperCprime_of_constructedSourceFollowingFactorWithOldTop`
- `DLNFibre.DLN.Aoyagi.case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopBlock_constructedWithOldTopFromCprime`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperCprime_of_constructedSourceFollowingFactorWithOldTopFromCprime`
- `DLNFibre.DLN.Aoyagi.case2SourceCurrentFollowingBlock_constructedWithOldTop_submatrix_oldTopPaperCprimeRowEquiv`
- `DLNFibre.DLN.Aoyagi.case2SourceCurrentFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv`
- `DLNFibre.DLN.Aoyagi.case2SourceSuccessorFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv`

## Claim

Lean now constructs a total source-coordinate following factor from arbitrary
old-top rows and arbitrary displayed pivot-first residual-column data.  The
constructor recovers the supplied old-top block and the supplied residual
block under the existing source restrictions.

Specializing the residual block to `Q*Cprime`, Aoyagi's displayed inverse
operation recovers the free chart-coordinate following factor `Cprime`.
Consequently the current source-row block reindexes to `[Cold; Q*Cprime]`,
while the formula-level successor block reindexes to `[Cold; Cprime]`.

## Proved

- Old-top rows `1,...,J` are disjoint from the residual-column interval
  `J+1,...,n(S+1)` in the piecewise constructor.
- `case2DisplayedSourceOldTopBlock` of the constructed factor is `Cold`.
- `case2DisplayedSourceFollowingFactor` of the constructed factor is the
  supplied pivot-first residual block `Csrc`.
- For generic `Csrc`, `paperCprime` of the constructed factor is
  `Q^-1*Csrc`.
- For `Csrc = Q*Cprime`, `paperCprime` is exactly `Cprime`.
- The existing source-current and successor row reindexing APIs turn these
  projections into the current and successor stacked-block identities.

## Assumed

Only the displayed Case 2 stage and continuation hypotheses needed to form the
finite domains, plus arbitrary finite matrices `Cold`, `Csrc`, and `Cprime`.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 19-22, where Case 2
uses the displayed residual-block operation `C'_J^(S+1)=Q^-1 C_J^(S+1)`.

## Deferred

Construction of `SourceProductionObligation`, successor chart families,
source suffixes, recurrence post-data, exponent post-data, chart coverage,
transition regularity, analytic coordinate regularity, Jacobian/volume
arithmetic, normal crossings, pole order, termination, RLCT extraction,
stopped-branch terminal production, and repair of the printed Case 2 vector
mismatch.

## Review

xhigh review passed with boundary corrections incorporated.  Review artifact:
`review-case2-constructed-source-following-factor-with-old-top-a4.md`.
