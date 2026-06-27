# Reproduction - A2 retained-passive dEarly successor dPcast substitution

Date: 2026-06-27.

Status: xhigh pen-and-paper scout reproduced; controller route selected.

This note is independent of the quiver-based paper.  It records the
non-first-index successor-current specialization of the retained-passive
`dEarly` recurrence.

## Setup

Use the nonterminal retained-passive recurrence one dimension up from the
generic wrapper.  Let `s : Fin M` and set

```text
q = s.succ       : Fin (M+1),
u = s.castSucc   : Fin (M+1),
p = q.castSucc   : Fin ((M+1)+1),
r = q.succ       : Fin ((M+1)+1).
```

The current solved-`A1` factor in the `dPcast` term is `p`.  Since

```text
u.succ = s.castSucc.succ = s.succ.castSucc = q.castSucc = p,
```

by `Fin.succ_castSucc`, this is a genuine successor solved-`A1` factor with
predecessor `u`.

The existing staged `dEarly` recurrence contains

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

## Calculation

The successor-current solved-`A1` residual-product helper gives

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * v.A1passive_u.
```

Because `u = s.castSucc`, the tangent term is exactly

```text
v.1 s.castSucc.
```

Substituting into the explicit inverse-product derivative contribution gives

```text
Cprod(z) * A3p(z) * Pcast(z)^-1
  * (dPsucc_z(v) * solvedA1_z(p)
      + Psucc(z) * v.1 s.castSucc)
  * Pcast(z)^-1.
```

The already-staged `dCprod`, `dG`, and successor-tail terms are unchanged.

## Lean Scope

Planned Lean addition in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply
```

The proof should instantiate the existing nonterminal `dEarly` wrapper with
`M := M+1` and `q := s.succ`, then use the successor-current
residual-product helper with helper index `u := s.castSucc`.

## Kill Conditions

- Do not use the first-index theorem or a bare `q : Fin M` parameter.
- Do not pass `q := s.succ` to the successor `dPcast` helper; pass
  `s.castSucc`.
- Do not use tangent `v.1 s`, `v.1 q`, or `v.1 s.succ`; the correct tangent
  is `v.1 s.castSucc`.
- Do not commute matrix factors.  The substitution remains between
  `Cprod * A3p * Pcast^-1` and the final `Pcast^-1`.
- Do not expand `dPsucc`, simplify `Psucc`, terminal-clean, introduce
  `dTail`, or claim target staging, determinant equality, measure transport,
  normal crossings, pole order, or RLCT.

## Nonclaims

No zero-branch formula, no `dTail` formula, no `Psucc` cleanup, no terminal
cleanup, no target staging, no determinant theorem, no measure theorem, no
normal crossings, no pole order, and no RLCT follows from this slice.
