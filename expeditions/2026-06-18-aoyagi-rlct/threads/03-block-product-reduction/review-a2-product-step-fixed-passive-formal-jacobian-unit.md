# Review - A2 product-step fixed-passive formal Jacobian unit

Date: 2026-06-26.

Reviewer: xhigh independent reviewer `Meitner`.

## Verdict

Pass. No blocking findings.

## Checked Points

The fixed-passive tangent formulas in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean` match the p. 13
coordinate change for the restricted variation where `D`, `A1`, and `A3` are
fixed:

```text
dCtop = dC1 * A1
dF2   = -A1^-1 * dA2
dF3   = dF3old + D*A3*Ctop^-1*dCtop*Ctop^-1
dC    = dA4 - A3*A1^-1*dA2.
```

The positive sign in `dF3` is correct because the source formula is
`F3 = F3old - D*A3*Ctop^-1`.

The inverse formal tangent formulas are also correct:

```text
dC1    = dCtop*A1^-1
dF3old = dF3 - D*A3*Ctop^-1*dCtop*Ctop^-1
dA2    = -A1*dF2
dA4    = dC - A3*dF2.
```

The `LinearEquiv` proof only needs `A1.det` invertible for the actual
cancellations; the `Ctop^-1` terms cancel formally. The determinant-chart
assumption `IsUnit C1.det` is still source-faithful, and with `IsUnit A1.det`
implies `IsUnit (C1*A1).det`.

## Assumption Check

- `[Fintype mu]` is appropriate for products through `mu`.
- `[Finite pi] [Finite nu]` are appropriate for the determinant theorem, after
  local `Fintype.ofFinite` instances.
- No `D.det` hypothesis is needed.
- No separate `Ctop.det` hypothesis is missing.

## Scope Check

The naming and docstrings are restrained: they say `fixed-passive` and
`formal differential`, and the determinant theorem explicitly avoids
source-measure and density transport. The file does not claim the full p. 13
Jacobian, analytic differentiability, normal crossings, pole order, or RLCT.

The reviewer stayed read-only and did not run Lean.
