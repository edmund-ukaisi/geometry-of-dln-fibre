# Review - A2 Case 2 residual-coordinate index pivot entries

Date: 2026-06-25.

Reviewer: controller, using xhigh source scout `Pasteur` and xhigh Lean/API
scout `Franklin`.

## Verdict

Pass.  The theorem is only the finite equivalence between the rectangular
residual-coordinate product index and the finite Case 2 center entry set.

## Checks

- Source fit: Pasteur confirmed that Aoyagi pp. 19-22 use the rectangular
  residual block `J+1..M(S)` by `J+1..M^(S+1)`.
- API fit: `AoyagiResidualBlockCoordinateIndex` is definitionally a product
  of row and column types, so the equivalence is not adding structure beyond
  the p.13 scalar-coordinate convention.
- Scope: the result does not choose a pivot chart, does not prove selected
  chart coverage, and does not identify any residual-factor product with a
  selected-entry matrix.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualIndex
```

