# Statement Card - A2 retained-passive dEarly product-rule dG substitution

Status: reproduced by controller; Lean proved; focused build passed; xhigh
review passed; `scripts/sorries`, `git diff --check`, full `DLNFibre` build,
and theorem axiom audit passed.

## Claim

For the retained-passive `dEarly` product-rule recurrence at a nonterminal
current edge `p = q.castSucc`, the `A3p` derivative factor is source-staged:

```text
dA3p_z(v) = v.2.2.1 q.
```

Thus the product-rule term

```text
- Cprod(z) * dA3p_z(v) * Pcast(z)^{-1}
```

becomes

```text
- Cprod(z) * v.2.2.1 q * Pcast(z)^{-1}.
```

All other derivative factors in the recurrence remain explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean names:

```text
fderiv_retainedPassiveA3WithoutLast_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply
```

## Dependencies

- `fderiv_retainedPassiveA3WithoutLast_castSucc_apply`;
- `fderiv_retainedPassiveA3WithoutLast_last_apply`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply`;
- local definitional unfolding of `A3p` at `p = q.castSucc`.

## Cited

None.

## Review

Xhigh reviewer `Averroes` passed the theorem boundary, factor order, and
nonclaims.  Review record:
`review-a2-retained-passive-dearly-product-rule-dg-substitution.md`.
Full verification passed: zero forbidden Lean placeholders by
`scripts/sorries`, clean `git diff --check`, successful full `DLNFibre` build,
and only the standard `[propext, Classical.choice, Quot.sound]` axiom
footprint for both new theorem names.

## Deferred

Terminal boundary companion for the zeroed final lower-left factor; source
staging for `dCprod`; source staging for `dPcast`; iteration of the recurrence
into a closed `dEarly` derivative expression; positive-tail `F3` target
staging; determinant theorem; measure theorem; normal crossings; pole order;
RLCT.

## Kill Conditions

- Do not read this as solved terminal `A3` or `F3` staging.
- Do not commute matrix factors.
- Do not claim `dCprod` or `dPcast` staging.
- Do not claim target staging, determinant equality, measure transport,
  normal crossings, pole order, or RLCT.
