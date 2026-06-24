# Statement card - A4 Case 2 constructed old-top `Cprime` source-current stack

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.sourceChartMap_continuingOldTopSourceSuffixConstructedWithOldTopFromCprimeStack_withoutChartFamily`

## Claim

Lean now specializes the existing continuing source-current stack theorem to
the constructed source-coordinate following factor with free old-top rows
`Cold` and free displayed chart-coordinate following factor `Cprime`.

The left current stack uses the reconstructed old residual block

```text
case2DisplayedPaperConstructedFollowingFactor ... Cprime
```

which is the displayed pivot-first `Q*Cprime`.  The right successor stack uses
the transported block `Cprime`.

## Proved

The theorem returns the same finite package as the upstream continuing
source-current stack theorem:

- next-center nonemptiness;
- an existential row-operation witness `q`;
- the specialized stack identity
  `[Cold; case2DisplayedPaperConstructedFollowingFactor ... Cprime]` on the
  left and `[Cold; Cprime]` on the right;
- corrected exponent post-data;
- level invariants, least-value gap, and `post.case2Gap`;
- finite center value membership, divisibility, and principalization.

The proof instantiates the existing source-current stack theorem with
`case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime`, then
rewrites the two source-row submatrices using the constructed current and
successor row-block lemmas.

## Assumed

The displayed Case 2 stage and continuation hypotheses, the continuing guard
`J+2 <= prefixMinNat n (S+1)`, the upstream exponent and level data, supplied
suffix matrices `Ctail`, and the free finite matrices `Cold` and `Cprime`.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 19-22, especially the
displayed Case 2 operation `C'_J^(S+1)=Q^-1 C_J^(S+1)`.

## Deferred

Construction of `SourceProductionObligation`, source-produced `Csucc`, suffix
production, successor chart families, chart coverage, transition regularity,
analytic coordinate regularity, Jacobian/volume arithmetic, normal crossings,
pole order, termination, RLCT extraction, stopped-branch terminal production,
and repair of the printed Case 2 vector mismatch.

## Review

xhigh review passed with statement-shape corrections incorporated.  Review
artifact:
`review-case2-constructed-oldtop-cprime-source-current-stack-a4.md`.
