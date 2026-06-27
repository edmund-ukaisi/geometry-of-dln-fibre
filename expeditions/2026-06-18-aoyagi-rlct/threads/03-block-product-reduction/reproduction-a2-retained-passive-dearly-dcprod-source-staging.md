# Reproduction - A2 retained-passive dEarly dCprod source staging

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; focused build
passed; xhigh review passed; full verification passed.

This note is independent of the quiver-based paper.  It records only the
stored-`C` product derivative used by the retained-passive lower-left
`dEarly` recurrence.

## Setup

Fix `q : Fin M` and set

```text
p = q.castSucc : Fin (M+1),
r = q.succ     : Fin (M+1).
```

The current `dEarly` summand from the already dG-staged product-rule theorem is

```text
- Cprod(z) * dG_z(v) * Pcast(z)^-1
```

together with the remaining `dCprod`, `dPcast`, and successor-tail terms.
Here

```text
Cprod(y) =
  residualFactorProduct C_y (Fin.last (M+1)) p.succ.
```

Since `p.succ = r.castSucc`, this is the suffix product beginning at the edge
`r` in the stored `C` family.  Define the next suffix by

```text
Cnext(y) =
  residualFactorProduct C_y (Fin.last (M+1)) r.succ.
```

The current stored block is `C_y r`.

## Calculation

The algebraic residual-product split gives

```text
Cprod(y) = Cnext(y) * C_y r.
```

Differentiate the noncommutative product in this order:

```text
dCprod_z(v)
  = dCnext_z(v) * C_z r
    + Cnext(z) * d(C_r)_z(v).
```

The stored `C` coordinate is a direct product-coordinate projection, hence

```text
d(C_r)_z(v) = v.2.2.2.1 r.
```

Therefore

```text
dCprod_z(v)
  = dCnext_z(v) * C_z r
    + Cnext(z) * v.2.2.2.1 r.
```

Substituting this into the dG-staged `dEarly` current summand gives the
undistributed source-staged term

```text
-((dCnext_z(v) * C_z r + Cnext(z) * v.2.2.2.1 r)
    * A3p(z) * Pcast(z)^-1).
```

The factor order is essential.  The successor suffix derivative is left of
`C_z r`; the successor suffix value is left of the source tangent
`v.2.2.2.1 r`.  The source tangent is at `r = q.succ`, not at
`q.castSucc`.

## Lean Scope

Lean proves:

```text
fderiv_retainedPassive_C_apply
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

The final theorem wraps the already-landed
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply`
and substitutes the stored-`C` suffix product derivative.  It keeps
`dCnext`, `dPcast`, and the successor-tail derivative explicit.

## Independent Review

Xhigh reviewer `Lovelace` passed the slice.  The review confirmed the stored
`C` projection derivative, the suffix-product factor order, the
`q.castSucc`/`q.succ` indexing, and the nonclaims.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative`, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check` passed.  The axiom audit for
all three new theorem names reports only
`[propext, Classical.choice, Quot.sound]`.

## Kill Conditions

- If the source tangent is taken at `q.castSucc` rather than `q.succ`, the
  statement has the wrong edge.
- If the order is changed to `C_z r * dCnext_z(v)` or
  `v.C_r * Cnext(z)`, the noncommutative product rule is wrong.
- If the theorem stages `dPcast`, closes the `dCnext` recursion, target-stages
  the recurrence, proves determinant equality, measure transport, normal
  crossings, pole order, or RLCT, it overclaims.

## Nonclaims

No `dPcast` staging, no closed finite-sum formula for `dCprod`, no target
staging, no full positive-tail `F3` target staging, no determinant theorem, no
measure theorem, no normal crossings, no pole order, and no RLCT follows from
this slice.
