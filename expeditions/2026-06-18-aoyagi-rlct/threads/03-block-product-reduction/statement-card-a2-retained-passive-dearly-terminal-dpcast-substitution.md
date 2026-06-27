# Statement Card - A2 retained-passive dEarly terminal dPcast substitution

Status: reproduced by controller; Lean target selected.

## Claim

In the terminal retained-passive `dEarly` recurrence, with
`q = Fin.last M`, `p = q.castSucc`, and `r = q.succ`, substitute the
solved-`A1` residual-product product rule into the explicit terminal
`dPcast` term:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

The terminal recurrence becomes

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * (dPsucc_z(v) * solvedA1_z(p)
            + Psucc(z) * d(solvedA1 p)_z(v))
        * Pcast(z)^-1.
```

The derivative of the current solved-`A1` factor remains explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply
```

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`.

## Cited

None.

## Deferred

Derivative formula for `solvedA1 0`; source-staging of `dPcast`; terminal
empty-product cleanup of `Psucc`; target staging; determinant theorem; measure
theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- Use `p.succ`, not `r.succ`, for the successor solved-`A1` product.
- Preserve the factor order
  `Cprod * A3p * Pcast^-1 * (...) * Pcast^-1`.
- Do not replace `(fderiv solvedA1 p)` by a passive source tangent.
- Do not claim determinant equality, measure transport, normal crossings,
  pole order, or RLCT.
