# Review - A2 Retained-Passive Solved A3 Derivative

Date: 2026-06-26.

Reviewer: Newton the 4th, xhigh read-only explorer.

## Verdict

No route blocker after controller fixes.

## Route Audit

Newton recommended mirroring the continuity chain:

```text
continuous_retainedPassiveA3WithoutLast
continuous_residualFactorProduct_C
continuous_residualFactorProduct_solvedA1_detChart_subtype
continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
continuous_solvedA3_detChart_subtype
```

The implemented Lean proof follows this route.  The initial dirty worktree
version failed on `Fintype`/`DecidableEq` inference for the `κ'` family; the
controller fixed this by making the residual-product and lower-left-tail
lemmas carry the needed `Fintype` and `DecidableEq` hypotheses.

Newton also recommended using `matrixMulContinuousLinearMap` for heterogeneous
matrix multiplication and avoiding `.mul` for rectangular products.  The final
Lean checkpoint uses the new helper `differentiableAt_matrix_mul` at the
rectangular product sites.

## Residual Risk

This review was route-focused, not a full independent line-by-line proof audit.
The focused Lean build passed after the fixes.  The remaining mathematical risk
belongs to the next layer: assembling the full raw-order map and proving a
formal tangent equivalence/determinant statement without overclaiming.

