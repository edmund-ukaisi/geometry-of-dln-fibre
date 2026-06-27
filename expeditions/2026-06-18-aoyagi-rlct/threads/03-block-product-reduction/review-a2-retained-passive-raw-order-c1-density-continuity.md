# Review - A2 Retained-Passive Raw-Order C1 and Density Continuity

Date: 2026-06-27.

Reviewer: Wegener the 4th, xhigh read-only explorer.

## Verdict

No blocking findings.

## Checks

Wegener reviewed the uncommitted changes in
`RetainedPassiveCoordinatesDerivative.lean`, focusing on the new `ContDiffAt`
helper/C1 layer and the continuity wrappers for `fderiv` and
`topologyTupleEdgeRawOrderFDerivAbsDet`.

The review confirmed:

- determinant-chart dependencies are used at the inverse sites in solved `A1`
  and the lower-left tail sum;
- the raw-order `C^1` assembly mirrors the existing differentiability assembly
  and states only ambient `ContDiffAt Real 1`;
- the derivative-continuity wrappers are appropriate consequences of
  `ContDiffAt ... 1`, with no silent chart-restricted derivative substitution;
- the no-explicit-continuity local lower/upper bound wrappers are sound
  consequences of chart-point density continuity and positivity.

Wegener also ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
git diff --check
```

Both passed.  No files were edited by the reviewer.

## Residual Risk

The remaining risk is downstream use: this theorem supplies continuity and
local bounds for the forward absolute determinant density only.  It is not an
explicit determinant formula, inverse-density measurability theorem,
source-prior transport theorem, normal-crossing theorem, pole-order theorem, or
RLCT theorem.
