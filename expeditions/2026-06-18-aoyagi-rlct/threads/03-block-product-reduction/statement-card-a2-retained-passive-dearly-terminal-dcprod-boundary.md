# Statement Card - A2 retained-passive dEarly terminal dCprod boundary

Status: reproduced by controller; Lean target selected.

## Claim

Specialize the retained-passive `dEarly` recurrence to
`q = Fin.last M : Fin (M+1)`.  With

```text
p = q.castSucc,
r = q.succ,
```

the successor stored-`C` product is empty and the successor zeroed-final tail
has derivative zero.  The narrow Lean target reduces the `dCprod`-staged
recurrence to

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * dPcast_z(v) * Pcast(z)^-1.
```

The source tangent is `v.C_r = v.2.2.2.1 r`; the `dG` term is the already
source-staged `v.2.2.1 q`.  The mathematical empty-product cleanup
`Cnext(z) = 1`, and hence `Cnext(z) * v.C_r = v.C_r`, is true but deferred
from this Lean slice.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean names:

```text
fderiv_retainedPassive_C_residualFactorProduct_self_apply
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply
```

## Dependencies

- `residualFactorProduct_self`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply`.

## Cited

None.

## Deferred

Source staging for `dPcast`; one-edge simplification of terminal `Cprod`;
empty-product value simplification of `Cnext(z)`; iteration of the
nonterminal `dCnext` recurrence; positive-tail `F3` target staging;
determinant theorem; measure theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- The terminal source index must be `q = Fin.last M : Fin (M+1)`.
- The stored-`C` source tangent must be at `r = q.succ`.
- The product order must remain noncommutative:
  `(0 * C_z r + Cnext(z) * v.C_r) * A3p * Pcast^-1`.
- Do not claim `dPcast`, determinant equality, measure transport, normal
  crossings, pole order, or RLCT.
