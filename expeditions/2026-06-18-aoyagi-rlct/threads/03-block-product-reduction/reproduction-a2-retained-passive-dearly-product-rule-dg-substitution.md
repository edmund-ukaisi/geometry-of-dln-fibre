# Reproduction - A2 retained-passive dEarly product-rule dG substitution

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused build
passed; xhigh review passed; `scripts/sorries`, `git diff --check`, full
`DLNFibre` build, and theorem axiom audit passed.

This note is independent of the quiver-based paper.  It only substitutes the
already source-staged zeroed lower-left factor derivative into the existing
retained-passive `dEarly` product-rule recurrence.

## Setup

The existing product-rule recurrence expands the current summand of the
retained-passive lower-left product-tail derivative.  For a current edge
`p : Fin (M + 1)`, define

```text
A1fun(y)(r) = solvedA1_r(y),
A3fun(y)(r) = retainedPassiveA3WithoutLast(data_y.A3seed)(r),
Cfun(y)(r) = C_r(y),
```

and

```text
Tailfun(y) = retainedPassiveLowerLeftProductTailSum(A1fun y, A3fun y, Cfun y)(p.val),
Cprod(y)  = product of C factors after p,
A3p(y)    = A3fun(y)(p),
Pcast(y)  = product of solved A1 factors from p onward,
Nextfun(y)= successor tail.
```

The previously proved product-rule theorem gives

```text
dTail_z(v)
  = -(dCprod_z(v) * A3p(z) * Pcast(z)^{-1})
    - (Cprod(z) * dA3p_z(v) * Pcast(z)^{-1})
    + Cprod(z) * A3p(z) * Pcast(z)^{-1}
        * dPcast_z(v) * Pcast(z)^{-1}
    + dNext_z(v).
```

## Calculation

Now specialize the current edge to a nonterminal edge

```text
p = q.castSucc,     q : Fin M.
```

Then

```text
A3p(y)
  = retainedPassiveA3WithoutLast(data_y.A3seed)(q.castSucc)
  = y.2.2.1(q),
```

so the earlier source-staging theorem gives

```text
dA3p_z(v) = v.2.2.1(q).
```

Substituting only this factor into the product-rule recurrence yields

```text
dTail_z(v)
  = -(dCprod_z(v) * A3p(z) * Pcast(z)^{-1})
    - (Cprod(z) * v.2.2.1(q) * Pcast(z)^{-1})
    + Cprod(z) * A3p(z) * Pcast(z)^{-1}
        * dPcast_z(v) * Pcast(z)^{-1}
    + dNext_z(v).
```

No matrix factors are commuted.  The order of the substituted term is still
`Cprod * dG * Pcast^{-1}`.

## Lean Scope

Lean adds a uniform endpoint helper:

```text
fderiv_retainedPassiveA3WithoutLast_apply
```

and proves the nonterminal product-rule substitution as:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

The helper only packages the already proved endpoint cases.  The product-rule
substitution theorem is downstream of
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply` and
rewrites the `A3p` derivative factor using
`fderiv_retainedPassiveA3WithoutLast_castSucc_apply`.

## Independent Review

Xhigh reviewer `Averroes` passed the slice.  The review confirmed the endpoint
split, the nonterminal `p = q.castSucc` scope, the unchanged matrix factor
order, and the absence of target-staging, determinant, measure, normal-
crossing, pole-order, or RLCT claims.

Full verification passed after review: `scripts/sorries` reported zero
`sorry`, `#exit`, `native_decide`, and `axiom`; `git diff --check` was clean;
the full `DLNFibre` build succeeded; and the theorem axiom audit reported only
the standard `[propext, Classical.choice, Quot.sound]` footprint for both new
theorems.

## Kill Conditions

- If the theorem is read as staging `dCprod` or `dPcast`, it overclaims.
- If the terminal zeroed `A3` branch is read as solved terminal `A3` or `F3`,
  it is wrong.
- If the matrix factors are commuted or reordered, it is wrong.
- If the theorem is advertised as target staging, determinant equality,
  measure transport, normal crossings, pole order, or RLCT, it overclaims.

## Nonclaims

No `dCprod` staging, no `dPcast` staging, no target staging, no full
positive-tail `F3` target staging, no determinant theorem, no measure
transport, no normal crossings, no pole order, and no RLCT follows from this
substitution slice.
