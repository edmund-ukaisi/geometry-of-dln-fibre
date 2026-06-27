# Reproduction - A2 retained-passive dEarly zero dPcast substitution

Date: 2026-06-27.

Status: xhigh pen-and-paper scout reproduced; controller route selected.

This note is independent of the quiver-based paper.  It records the first-index
specialization of the retained-passive `dEarly` recurrence after the solved-`A1`
residual-product derivative has already been split into zero and successor
current-factor branches.

## Setup

Use the nonterminal retained-passive recurrence with one more passive step.
Write

```text
q = 0 : Fin (M+1),
p = q.castSucc : Fin ((M+1)+1),
r = q.succ     : Fin ((M+1)+1).
```

Thus the current solved-`A1` factor in the `dPcast` term is the zero solved
top-left block.  The existing staged `dEarly` recurrence contains

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * dPcast_z(v)
  * Pcast(z)^-1.
```

Here

```text
Pcast(y) = residualFactorProduct solvedA1_y final p.castSucc,
Psucc(y) = residualFactorProduct solvedA1_y final p.succ.
```

For the zero solved block, set

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = d(Tfun)_z(v),
dCtop   = v.Ctop,
Ctop    = data.Ctop.
```

## Calculation

The zero-current solved-`A1` residual-product helper gives

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) *
        (Tail^-1 * dCtop - Tail^-1 * dTail * Tail^-1 * Ctop),
```

with `p = 0` after the first-index specialization.  Substituting this into the
explicit inverse-product derivative contribution gives

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) *
          (Tail^-1 * dCtop - Tail^-1 * dTail * Tail^-1 * Ctop))
  * Pcast(z)^-1.
```

The already-staged `dCprod`, `dG`, and successor-tail terms are unchanged:

```text
-(((dCnext_z(v) * C_r + Cnext(z) * dC_r) * A3p(z) * Pcast(z)^-1))
- Cprod(z) * dG * Pcast(z)^-1
+ [the substituted inverse-product contribution]
+ dNext_z(v).
```

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply
```

The proof should instantiate the existing nonterminal `dEarly` wrapper at
`M := M+1` and `q := 0`, then replace the generic `dPcast` bracket using the
zero-current residual-product helper.

## Kill Conditions

- Do not use `q : Fin M := 0`; that wrongly requires nonempty `Fin M`.
- Do not commute matrix factors.  The substitution sits between
  `Cprod * A3p * Pcast^-1` and the final `Pcast^-1`.
- Do not identify `Psucc` with `Tail`.
- Do not unfold the first-summand pointwise factor `solvedA1_z(p)`.
- Do not expand `dTail`.
- Do not terminal-clean the theorem, even when `M = 0`.
- Do not advertise this as target staging, determinant equality, measure
  transport, normal crossings, pole order, or RLCT.

## Nonclaims

No `Psucc = Tail` cleanup, no recursive `dTail` formula, no terminal cleanup,
no target staging, no determinant theorem, no measure theorem, no normal
crossings, no pole order, and no RLCT follows from this slice.
