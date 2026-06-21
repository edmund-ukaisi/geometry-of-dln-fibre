# Pen-and-paper reproduction - A4 Case 2 free Cprime continuing branch

Status: reproduced as a finite block-multiplication and reindexing target.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  After blowing up the residual block at the
displayed coordinate `(J+1,J+1)`, the paper defines the regular matrix `Q`,
sets

```text
C'_J^(S+1) = Q^-1 C_J^(S+1),
```

then defines `P` and

```text
D'''_J = [1 0; 0 D_{J+1}].
```

The displayed product identity ends with

```text
P diag(b'_J+1,...,b'_M(S)) D''_J C'_J^(S+1)
  = diag(b'_J+1,...,b'_M(S)) D'''_J C'_J^(S+1).
```

If the continuing inequality holds, the paper says the inductive statement is
obtained with `J` increased by one.

## Reproduction

Work in the displayed pivot-first residual coordinates.  Let the free chart
coordinate following matrix be an arbitrary matrix

```text
C' : (top pivot column plus post-pivot residual columns) -> tau.
```

Split it into its top row and tail:

```text
C' = verticalBlock C'_top C'_tail.
```

The displayed cleared matrix has the block form

```text
D''' = blockdiag(1, D - x*y).
```

Therefore

```text
D''' C' = verticalBlock C'_top ((D - x*y) C'_tail).
```

Projecting to the lower rows discards the top block.  Reindexing the
post-pivot row and column complements by the already-proved equivalences with
the next same-stage domains gives

```text
(D''' C')_lower,reindexed
  =
case2DisplayedPostPivotResidualBlock(n,S,J,residual)
  *
case2DisplayedPostPivotFreeFollowingFactor(n,S,J,C').
```

Here

```text
case2DisplayedPostPivotFreeFollowingFactor
```

is only the tail of the arbitrary pivot-first `C'`, reindexed from the old
post-pivot column complement to `Case2ResidualColIndex n S (J+1)`.

This calculation does not require `C'` to be `Q^-1 C` for any total
source-coordinate following factor.  The existing constructed-source theorem
is a separate reverse-coordinate witness; this slice only proves the direct
free-coordinate lower-row identity.

## Boundary Checks

- The source only motivates the pivot-first free coordinate `C'` through the
  displayed equation `C' = Q^-1 C`.  This Lean slice proves what follows from
  an arbitrary supplied `C'`; it does not prove that every such `C'` is reached
  by a source chart in an analytic atlas.
- The lower-row identity is independent of the printed Case 2 exponent-vector
  mismatch.  It uses only the displayed block form of `D'''`.
- The continuing branch still needs the explicit branch hypothesis
  `J+2 <= prefixMinNat n (S+1)` when one wants nonemptiness of the next
  residual center.  The bare matrix identity itself is meaningful without
  that nonemptiness assertion.
- The post-data in any packaged source-chart theorem remains the corrected
  selected-label post-data already isolated in earlier A4 slices, not a
  chart-produced recurrence or exponent theorem.

## Formalisation Target

Lean should add:

```text
case2DisplayedPostPivotFreeFollowingFactor
case2DisplayedFreeCprime_eq_verticalBlock
case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
```

and, if the low-level theorem lands cleanly, a source-chart package:

```text
sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData
```

The package may combine the free-`C'` product identity with the existing
corrected exponent, level, least-value-gap, and `case2Gap` fields.  It must
not claim chart coverage, successor chart-family construction, or source
production of `C'`.

## Kill Conditions

- Do not identify the arbitrary free `C'` with a source-produced
  `C'^(S+1)` without an explicit chart-construction theorem.
- Do not use this as arbitrary-pivot coverage; this is the displayed top-left
  pivot chart only.
- Do not infer regularity, Jacobian exponent, transition invariance,
  termination, normal crossings, pole order, or RLCT extraction.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
- Do not hide the corrected Case 2 exponent-vector choice inside this matrix
  identity.
