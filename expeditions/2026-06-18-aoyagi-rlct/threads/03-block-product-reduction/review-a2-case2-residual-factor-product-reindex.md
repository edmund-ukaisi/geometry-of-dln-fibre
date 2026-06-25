# Review - A2 Case 2 residual-factor product reindex

Date: 2026-06-25.

Reviewer: controller, using xhigh source scout `Pasteur` and xhigh Lean/API
scout `Franklin`.

## Verdict

Pass.  The theorem is a finite bridge from the generic two-edge
`residualFactorProduct` unfold to the existing displayed Case 2 two-factor
product, and it keeps all source-producing data as hypotheses.

## Checks

- Source fit: Aoyagi pp. 19-22 support the local finite product
  `D_{J+1} * C'_+`, not a global selected-entry source/image theorem.
- API fit: the bridge lives in a new module importing both `ProductReduction`
  and `BlowupArithmetic`, preserving the lower-level import direction.
- Indexing: the row, middle, and right endpoint equivalences are explicit
  hypotheses and are used only through `Matrix.submatrix_mul_equiv`.
- Scope: the theorem assumes the two factor identities, so it does not
  smuggle in residual-index provenance or a selected-entry coordinate-matrix
  RHS.

## Scout Checks

`Pasteur` confirmed from Aoyagi pp. 11-13 and pp. 19-22 that the finite
interval provenance is source-backed: post-pivot rows and columns are the
next same-stage `(S,J+1)` residual domains, and following-factor tail rows
match the post-pivot residual columns.  The same check found that Aoyagi does
not source-produce fixed-base endpoint equivalences or successor chart data.

`Franklin` independently selected this theorem as the best next Lean target.
The alternatives were either already present Case 2 product RHS readouts or a
useful but lower-priority residual-coordinate/pivot-entry equivalence.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```
