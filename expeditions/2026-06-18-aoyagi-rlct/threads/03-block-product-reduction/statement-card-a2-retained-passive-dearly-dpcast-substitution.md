# Statement Card - A2 retained-passive dEarly dPcast substitution

Status: reproduced by controller; Lean target selected.

## Claim

In the nonterminal retained-passive `dEarly` recurrence, with
`q : Fin M`, `p = q.castSucc`, and `r = q.succ`, substitute the solved-`A1`
residual-product product rule into the explicit `dPcast` term:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

The inverse-derivative contribution becomes

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

All earlier `dCprod`, `dG`, and successor-tail terms remain as in the staged
recurrence.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply
```

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`;
- `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply`.

## Cited

None.

## Deferred

Derivative formula for `solvedA1 0`; complete source-staging of `dPcast`;
iteration/terminal closure of the recurrence; target staging; determinant
theorem; measure theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- Instantiate the solved-`A1` helper with `p = q.castSucc`, not `q.succ`.
- Preserve the factor order
  `Cprod * A3p * Pcast^-1 * (...) * Pcast^-1`.
- Do not replace `(fderiv solvedA1 p)` by a passive source tangent.
- Do not claim determinant equality, measure transport, normal crossings, pole
  order, or RLCT.
