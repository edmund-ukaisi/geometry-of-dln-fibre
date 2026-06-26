# Review - A2 product-step ambient derivative

Date: 2026-06-26.

Reviewers: controller, after read-only derivative scout from xhigh agent
`Pascal`.

## Verdict

Pass for the first analytic derivative checkpoint.  The Lean statements are
properly scoped to ambient finite-dimensional tuple coordinates and do not
claim determinant-chart change of variables or density transport.

## Mathematical Check

The inverse derivative theorem uses the standard identity

```text
d(A^{-1})[H] = -A^{-1} H A^{-1}
```

for a determinant-unit real square matrix.  The proof correctly reduces the
determinant-unit hypothesis to a matrix unit using
`Matrix.isUnit_iff_isUnit_det` and then invokes Mathlib's normed-ring inverse
derivative.  The explicit rewrites between matrix nonsingular inverse and
`Ring.inverse` avoid changing the meaning of the matrix inverse.

The tuple map

```text
productReductionStepTopologyTupleToChart
```

uses the same p. 13 formulas as `ProductReductionStepRawCoordinates.toChart`:
`Ctop = C1 A1`, `F2 = -A1^{-1} A2`,
`F3 = F3old - D A3 Ctop^{-1}`, and
`C = A4 - A3 A1^{-1} A2`.  The two bridge theorems prove that applying the
tuple map to `x.topologyTuple` recovers both the record-level chart tuple and
the formal chart base tuple.

The `Ctop` derivative theorem is exactly the product rule:

```text
dCtop = dC1 A1 + C1 dA1.
```

Its derivative target is
`LinearMap.toContinuousLinearMap (productReductionStepFormalJacobian_dCtop x)`,
so this is the first component-level analytic identification with the formal
Jacobian.

## Lean/API Check

The derivative module is separate from
`ProductReductionStepJacobian.lean`, preserving the distinction between
finite formal tangent algebra and analytic Frechet derivative statements.
The `Ctop` theorem uses `[Finite pi] [Finite nu]` and locally installs
`Fintype` instances only to obtain finite-dimensional continuous-linear
coercions for the full nested raw tuple.

## Scope Check

The full tuple derivative remains open.  The hard next components are `F2`,
`F3`, and `C`, which require composing the inverse derivative with matrix
products and then simplifying to the already-landed formal Jacobian formulas.
No measure-theoretic pushforward or determinant absolute-value theorem follows
from this checkpoint alone.
