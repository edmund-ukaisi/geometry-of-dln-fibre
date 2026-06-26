# Statement Card - A2 product-step fixed-passive formal Jacobian unit

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

For the fixed-passive p. 13 one-step coordinate change, with `D`, `A1`, and
`A3` fixed and raw variables `(C1,F3old,A2,A4)`, the formal tangent map to chart
variables `(Ctop,F3,F2,C)` is a linear equivalence on the determinant chart.
Consequently its finite linear determinant is a unit.

## Lean Names

```text
ProductStepFixedPassiveRawTangent
ProductStepFixedPassiveChartTangent
productStepFixedPassiveFormalJacobian
productStepFixedPassiveFormalJacobianInverse
productStepFixedPassiveFormalJacobianEquiv
productStepFixedPassiveFormalJacobian_det_isUnit
```

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- fixed matrices `C1`, `D`, `A1`, and `A3`;
- determinant-chart hypotheses `IsUnit C1.det` and `IsUnit A1.det`;
- `[Finite pi] [Finite nu]` for the determinant-unit theorem.

No `D.det` hypothesis is present or needed.

## Not Proved

This is not the full p. 13 formal Jacobian: the variables `D`, `A1`, and `A3`
are fixed. It also does not prove analytic differentiability, source-measure
pushforward, density/Jacobian transport, exact determinant exponent/sign,
normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Verified on 2026-06-26 with the focused module build passing cleanly.
