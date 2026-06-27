# Reproduction - A2 retained-passive dEarly dPcast substitution

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean target selected.

This note is independent of the quiver-based paper.  It records the narrow
substitution of the solved-`A1` residual-product product rule into the
retained-passive `dEarly` recurrence after the `dCprod` and `dG` factors have
already been staged.

## Setup

Use the nonterminal retained-passive recurrence with `q : Fin M`, and set

```text
p = q.castSucc : Fin (M+1),
r = q.succ     : Fin (M+1).
```

The existing staged recurrence contains the inverse-derivative contribution

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * dPcast_z(v)
  * Pcast(z)^-1.
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

The residual-factor product rule for solved `A1` gives

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

Substituting this into the inverse-derivative contribution gives

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * d(solvedA1 p)_z(v))
  * Pcast(z)^-1.
```

This is only a product-rule substitution.  The derivative
`d(solvedA1 p)_z(v)` remains explicit.  In the downstream nonterminal
`dEarly` recurrence, `p = q.castSucc`; this must not be replaced by `q.succ`.

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply
```

The proof should call
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`,
then rewrite `(fderiv ℝ Pcast z) v` using
`fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply` with
`p := q.castSucc`.

## Kill Conditions

- If the theorem changes the noncommutative order around `Pcast(z)^-1`, it is
  wrong.
- If it instantiates the solved-`A1` helper with `p := q.succ`, it stages the
  wrong factor.
- If it replaces `d(solvedA1 p)_z(v)` by a passive source tangent, it
  overclaims and is false at `p=0`.
- If this theorem is advertised as complete source-staging of `dPcast`, target
  staging, determinant equality, measure transport, normal crossings, pole
  order, or RLCT, it overclaims.

## Nonclaims

No derivative formula for `solvedA1 0`, no complete source-staging of
`dPcast`, no closed finite-sum formula, no target staging, no determinant
theorem, no measure theorem, no normal crossings, no pole order, and no RLCT
follows from this substitution slice.
