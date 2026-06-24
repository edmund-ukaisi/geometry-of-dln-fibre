# Reproduction - Case 2 constructed old-top `Cprime` source-current stack

Date: 2026-06-24.

Status: controller reproduction, pending independent check.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2, performs the displayed column operation

```text
C'_J^(S+1) = Q^-1 C_J^(S+1)
```

and then continues the induction with `J` replaced by `J+1`.  The existing
Lean stack theorem already proves the finite displayed source-chart stack
identity for an arbitrary source-coordinate following factor `C`:

```text
[oldTopWeight, 0; 0, lowerLeft] * [oldTop(C); oldResidual(C)] * suffix
 =
[oldTopWeight, 0; 0, lowerRight] * [oldTop(C); paperCprime(C)] * suffix.
```

Here `lowerLeft` is the row-operated weighted source-substitution block and
`lowerRight` is the weighted displayed `D'''` block.

## Construction

Use the constructed old-top source following factor from the previous
checkpoint.  Take free finite coordinate data

```text
Cold   : {1,...,J} -> tau -> R,
Cprime : (Unit + pivotComplement(J+1)) -> tau -> R.
```

Define

```text
Csrc = Q*Cprime,
C = constructedWithOldTopFromCprime(Cold,Cprime).
```

The previous checkpoint proves the two row-block projections:

```text
currentFollowingBlock(C), reindexed
  = [Cold ; case2DisplayedPaperConstructedFollowingFactor(..., Cprime)],

successorFollowingBlock(C), reindexed
  = [Cold ; Cprime].
```

Equivalently, before source-row reindexing:

```text
oldTop(C) = Cold,
oldResidual(C) = Q*Cprime,
paperCprime(C) = Cprime.
```

## Stack Specialization

Instantiate the existing continuing source-current stack theorem with this
constructed `C`.  The theorem supplies:

```text
nonempty next center,
q : pivotComplement(row) -> R,
stack identity with current/successor source-row blocks,
corrected exponent post-data,
level invariants,
least-value gap,
post.case2Gap,
finite center principalization data.
```

Rewrite the current source-row block by

```text
case2SourceCurrentFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv
```

and rewrite the successor source-row block by

```text
case2SourceSuccessorFollowingBlock_constructedWithOldTopFromCprime_submatrix_oldTopPaperCprimeRowEquiv.
```

The resulting stack identity is:

```text
([oldTopWeight, 0; 0, lowerLeft] *
  [Cold ; case2DisplayedPaperConstructedFollowingFactor(..., Cprime)]) * suffix
 =
([oldTopWeight, 0; 0, lowerRight] * [Cold ; Cprime]) * suffix.
```

The existential row-operation witness `q` is produced after specializing to
the supplied `Cold` and `Cprime`; the corrected post-data package is inherited
from the upstream stack theorem.  Nothing in the specialization constructs the
supplied suffix matrices or a successor chart.

## Formalisation Target

```text
sourceChartMap_continuingOldTopSourceSuffixConstructedWithOldTopFromCprimeStack_withoutChartFamily
```

Possible compatibility wrapper if useful:

```text
sourceChartMap_continuingOldTopSourceSuffixConstructedWithOldTopFromCprimeStack_withCorrectedPostData
```

## Kill Conditions

- If the existing continuing stack theorem requires arbitrary values of `C`
  outside the rows used by the constructed source factor, the specialization
  may overstate coordinate freedom.
- If the current block is rewritten to `[Cold; Cprime]` instead of the exact
  Lean old-residual term
  `[Cold; case2DisplayedPaperConstructedFollowingFactor(..., Cprime)]`, the
  statement is wrong.
- If the successor block is rewritten to `[Cold; Cprime]` without first using
  the constructed `Q*Cprime` recovery theorem, the statement hides a necessary
  hypothesis.
- If the result claims construction of `SourceProductionObligation`, suffixes,
  or a successor chart family, it overclaims.

## Nonclaims

This is finite stack specialization only.  It does not construct a
`SourceProductionObligation`, source-produce `Csucc`, produce source suffixes,
construct successor chart families, prove chart coverage, transition
regularity, analytic coordinate regularity, Jacobian/volume arithmetic,
normal crossings, pole order, termination, RLCT extraction, stopped-branch
terminal production, or repair of the printed Case 2 vector mismatch.
