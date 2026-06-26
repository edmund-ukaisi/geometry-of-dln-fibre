# Review - A2 Schur-core formal Jacobian unit

Date: 2026-06-26.

Reviewer: controller local check; xhigh agent `Darwin`.

Status: passed after finite side-index repair to the determinant theorem.

## Checked Items

The Lean formulas in `ProductReductionStepJacobian.lean` match the reproduced
fixed-pivot Schur core:

```text
dF2 = -B^{-1} dA2,
dF3 = -dA3 B^{-1},
dC4 = dA4 - dA3 B^{-1} A2 - A3 B^{-1} dA2.
```

The inverse tangent formulas are also source-faithful:

```text
dA2 = -B dF2,
dA3 = -dF3 B,
dA4 = dC4 - dF3 A2 - A3 dF2.
```

The determinant-unit conclusion is obtained only through `LinearEquiv`:
the formal map and inverse compose to the identity using `IsUnit B.det`.

## Boundary Check

The file comments and theorem names say "formal Jacobian" rather than analytic
Jacobian.  The statement is fixed-`B`; it does not include the derivative terms
from varying `B` or the larger product-reduction fields `C1`, `D`, and
`F3_old`.

This is therefore a correct first Jacobian-unit slice, but not the final
p. 13 density-transport theorem.

## Remaining Risks

The exact determinant power

```text
(-1)^(r(m+n)) det(B)^-(m+n)
```

is not computed.  The Lean theorem proves only unit-ness.  This is enough for
nonvanishing/unit-density applications, but not for a future theorem that needs
the exact sign or exponent.

The larger product-step formal differential remains open.

## Xhigh Review Finding

Darwin found that the first determinant theorem version only assumed
`Fintype rho`.  Since `LinearMap.det` can become vacuous outside finite
dimension, the determinant-unit theorem needed finite side-index hypotheses for
the `Matrix rho nu K`, `Matrix mu rho K`, and `Matrix mu nu K` tangent space.

The Lean theorem now assumes `[Finite mu] [Finite nu]` and materializes local
`Fintype` instances in the proof.  The focused build of
`DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian` passes without warnings.
