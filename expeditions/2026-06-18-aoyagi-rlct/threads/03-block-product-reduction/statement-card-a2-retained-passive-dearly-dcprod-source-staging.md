# Statement Card - A2 retained-passive dEarly dCprod source staging

Status: reproduced by controller; Lean proved; focused build passed; xhigh
review passed; full verification passed.

## Claim

For `q : Fin M`, set `p = q.castSucc` and `r = q.succ`.  In the retained-
passive `dEarly` product-rule recurrence, the derivative of the stored-`C`
suffix product beginning at `p.succ = r.castSucc` is

```text
dCprod_z(v)
  = dCnext_z(v) * C_z r
    + Cnext(z) * v.2.2.2.1 r.
```

Substituting this into the already dG-staged current summand gives

```text
-((dCnext_z(v) * C_z r + Cnext(z) * v.2.2.2.1 r)
    * A3p(z) * Pcast(z)^-1).
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean names:

```text
fderiv_retainedPassive_C_apply
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply
```

## Dependencies

- `residualFactorProduct_castSucc`;
- `differentiableAt_residualFactorProduct_C`;
- `differentiableAt_C`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply`;
- the matrix multiplication continuous bilinear derivative rule.

## Cited

None.

## Review

Xhigh reviewer `Lovelace` passed the projection derivative, suffix-product
factor order, `q.castSucc`/`q.succ` indexing, and nonclaims.  Review record:
`review-a2-retained-passive-dearly-dcprod-source-staging.md`.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative`, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check` passed.  The axiom audit for
all three new theorem names reports only
`[propext, Classical.choice, Quot.sound]`.

## Deferred

Source staging for `dPcast`; iteration or terminal simplification of
`dCnext`; positive-tail `F3` target staging; determinant theorem; measure
theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- The source tangent must be `v.2.2.2.1 q.succ`.
- The product order must remain
  `dCnext * C_r + Cnext * dC_r`.
- Do not claim `dPcast`, target staging, determinant equality, measure
  transport, normal crossings, pole order, or RLCT.
