# Reproduction - A2 retained-passive dEarly terminal dCprod boundary

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean target selected.

This note is independent of the quiver-based paper.  It records the terminal
boundary of the retained-passive lower-left `dEarly` recurrence after the
stored-`C` suffix derivative has been source-staged.

## Setup

Work with one more passive edge than the nonterminal theorem.  Fix
`q = Fin.last M : Fin (M+1)` and set

```text
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

Then `r` is the final stored-`C` edge and `r.succ` is the final endpoint.  The
already source-staged `dCprod` theorem gives a current summand of the form

```text
-((dCnext_z(v) * C_z r + Cnext(z) * v.C_r)
    * A3p(z) * Pcast(z)^-1)
```

together with the source-staged `dG` term, the still-explicit `dPcast` term,
and the successor-tail derivative.

## Calculation

At the terminal boundary,

```text
Cnext(y) =
  residualFactorProduct C_y finalEndpoint finalEndpoint = 1.
```

Therefore

```text
dCnext_z(v) = 0.
```

The zeroed-final retained-passive tail also has no successor contribution:

```text
dNextTail_z(v) = 0.
```

Substituting these two terminal identities into the `dCprod`-staged recurrence
gives the narrow theorem target

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * dPcast_z(v) * Pcast(z)^-1.
```

Here

```text
dG = v.2.2.1 q,
v.C_r = v.2.2.2.1 r.
```

Mathematically `Cnext(z)` is the empty product, so the displayed first term
can be simplified further to `-(v.C_r * A3p(z) * Pcast(z)^-1)`.  The current
Lean theorem intentionally does not claim that value simplification.  It only
collapses `dCnext_z(v)` and the successor-tail derivative, leaving `Cnext(z)`,
`Cprod(z)`, and `dPcast_z(v)` explicit.  The value `Cprod(z)` is a one-edge
stored-`C` product at this boundary, but that cleanup is also deferred.

## Lean Scope

Planned Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassive_C_residualFactorProduct_self_apply
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply
```

The first helper states, for every self suffix index, that the Frechet
derivative of the empty stored-`C` residual product is zero.  The second
specializes
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`
at `q = Fin.last M`, rewrites the empty `Cnext` derivative, and discharges the
successor tail by the terminal zero-tail simplification.

## Kill Conditions

- If the terminal index is not `q = Fin.last M : Fin (M+1)`, the successor
  `Cnext` need not be empty.
- If the source tangent is taken at `q.castSucc` rather than `r = q.succ`, the
  stored-`C` derivative is indexed incorrectly.
- If this theorem stages `dPcast`, closes all `Cprod` recurrences, target-
  stages the recurrence, proves determinant equality, measure transport,
  normal crossings, pole order, or RLCT, it overclaims.

## Nonclaims

No `dPcast` staging, no closed finite-sum formula for all `dCprod`, no target
staging, no full positive-tail `F3` target staging, no determinant theorem, no
measure theorem, no normal crossings, no pole order, and no RLCT follows from
this terminal-boundary slice.
