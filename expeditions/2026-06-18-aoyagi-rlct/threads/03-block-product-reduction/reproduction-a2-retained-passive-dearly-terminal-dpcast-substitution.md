# Reproduction - A2 retained-passive dEarly terminal dPcast substitution

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean target selected.

This note is independent of the quiver-based paper.  It records the terminal
counterpart of the retained-passive `dEarly` `dPcast` substitution, after the
terminal `dCprod` boundary has already killed the empty stored-`C` derivative
and the successor zeroed-final tail.

## Setup

Use the terminal retained-passive recurrence with

```text
q = Fin.last M : Fin (M+1),
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

The landed terminal theorem gives

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * dPcast_z(v) * Pcast(z)^-1.
```

Here

```text
Pcast(y) = residualFactorProduct solvedA1_y final p.castSucc.
```

Define the successor solved-`A1` suffix

```text
Psucc(y) = residualFactorProduct solvedA1_y final p.succ.
```

## Calculation

The solved-`A1` product-rule helper applies at the same terminal `p`:

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

Substituting only this identity into the already terminal recurrence gives

```text
dEarly_terminal,z(v)
  = -((0 * C_z r + Cnext(z) * v.C_r) * A3p(z) * Pcast(z)^-1)
    - Cprod(z) * dG * Pcast(z)^-1
    + Cprod(z) * A3p(z) * Pcast(z)^-1
        * (dPsucc_z(v) * solvedA1_z(p)
            + Psucc(z) * d(solvedA1 p)_z(v))
        * Pcast(z)^-1.
```

This is still only product-rule substitution.  Although terminally
`Psucc(y)` is the empty product and `dPsucc_z(v) = 0`, this slice deliberately
does not perform that value/derivative cleanup.  Keeping `Psucc` explicit
matches the nonterminal dPcast substitution and avoids extra cast pressure.

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply
```

The proof should call
`fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply`,
then rewrite `(fderiv ℝ Pcast z) v` using
`fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply` with
`M := M + 1` and `p := (Fin.last M).castSucc`.

## Kill Conditions

- If the theorem uses `r.succ` instead of `p.succ` for `Psucc`, it advances one
  solved-`A1` factor too far.
- If it moves the rightmost `Pcast(z)^-1` inside the substituted sum, it
  changes noncommutative order.
- If it replaces `d(solvedA1 p)_z(v)` by a passive source tangent, it
  overclaims and is false when `M = 0`.
- If it claims terminal empty-product cleanup for `Psucc`, target staging,
  determinant equality, measure transport, normal crossings, pole order, or
  RLCT, it overclaims.

## Nonclaims

No derivative formula for `solvedA1 0`, no source-staging of `dPcast`, no
terminal cleanup of `Psucc`, no closed finite-sum formula, no target staging,
no determinant theorem, no measure theorem, no normal crossings, pole order,
and no RLCT follows from this terminal substitution slice.
