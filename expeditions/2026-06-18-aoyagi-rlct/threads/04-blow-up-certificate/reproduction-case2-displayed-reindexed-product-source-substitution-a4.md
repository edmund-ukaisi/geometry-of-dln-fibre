# Reproduction - A4 Case 2 displayed reindexed product source-substitution

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  After choosing the displayed pivot
`(J+1,J+1)`, Aoyagi's finite `Q/P` calculation is reindexed into the next
same-stage source product shape.  This note records only the finite
substitution-block rewrite inside that already-formalised reindexed product.

## Reproduction

Let `p` be the current all-pivot source chart and let the displayed target
pivot be

```text
q = (J+1,J+1).
```

Write

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r
d = x_q = x_(J+1,J+1).
```

Assume

```text
d != 0.
```

The transition-generated displayed chart data are

```text
targetU = u*d,
targetResidual_r = x_r/d.
```

The displayed reindexed next-source product theorem, applied to
`(targetU,targetResidual)`, has lower-left block

```text
P * (diag(pre row weights) * DisplayedSub(targetU,targetResidual))^pivot-first.
```

For the displayed pivot, `DisplayedSub` is just the supplied selected-entry
substitution block for `q`.  The selected-entry transition equality gives

```text
DisplayedSub(targetU,targetResidual)
  = Sub_q(u*d,x/d)
  = Sub_p(u,x).
```

Therefore the same witness `P` from the displayed reindexed product theorem
also proves the reindexed product equality with the left block rewritten as

```text
P * (diag(pre row weights) * Sub_p(u,x))^pivot-first.
```

The right-hand side is unchanged:

- the post state is still `pre.case2Succ targetU`;
- the post-pivot residual block is computed from the transition-generated
  displayed residuals;
- the successor following factor is still the formula-level
  `case2DisplayedSourceSuccessorFollowingFactor targetResidual C`;
- the exponent, level, least-value-gap, and recurrence-gap post-data are the
  same corrected concrete post-data from the displayed reindexed theorem.

This is purely a finite congruence step under matrix multiplication,
`fromBlocks`, and row reindexing.  It does not construct a source-produced
successor following object or suffix.

## Lean Targets

Lean first adds a generic displayed-product rewrite lemma consuming a supplied
block equality.  In this API the `u` parameter of the displayed source product
is already the displayed pivot/source-chart coordinate, so the supplied block
contract is

```text
case2DisplayedSourceSubstitutionBlock n hS hcont u residual = B.
```

Then specialize it to the displayed transition-generated data with

```text
B = case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual.
```

The landed Lean names are:

```text
Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlock
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.case2DisplayedSourceSubstitutionBlock_transition_eq_sourceSelectedSubstitutionBlockOfMem_of_displayed_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_sourceSubstitution_of_displayed_normalized_ne_zero
```

The targeted module build has passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The full gate set also passed:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

## Boundary

- The denominator is the normalized displayed coordinate `d`, not `u*d`.
- The rewrite changes only the left substitution block in the source side of
  the displayed reindexed product.
- The right side remains displayed transition-generated data with
  formula-level successor following factor.
- This proves no source production of `Csucc`, no suffix production, no
  successor chart family, no transition regularity, no chart coverage, no
  normal crossings, no pole order, and no RLCT extraction.

## Kill Conditions

- Do not claim `Csucc` is source-produced.
- Do not rewrite the displayed Schur/post-pivot residual block to a source
  object beyond the already supplied denominator-cleared finite formula.
- Do not replace the denominator hypothesis by `(u*d) != 0`.
- Do not treat the reindexed product equality as analytic chart regularity or
  coverage.
