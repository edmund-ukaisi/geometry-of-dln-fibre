# Reproduction - A2 retained-passive dPcast successor solvedA1 substitution

Date: 2026-06-27.

Status: xhigh pen-and-paper scout reproduced; controller route selected.

This note is independent of the quiver-based paper.  It records the
successor-current-factor specialization of the retained-passive solved-`A1`
residual product derivative.

## Setup

Fix `q : Fin M` and set

```text
p = q.succ : Fin (M+1),
A_s(y) = solvedA1_y(s),
Pcast(y) = residualFactorProduct A(y) final p.castSucc,
Psucc(y) = residualFactorProduct A(y) final p.succ.
```

The determinant-chart hypothesis on `z` is inherited from the generic
residual-product derivative theorem.  The successor solved-`A1` derivative
itself is chart-free.

## Calculation

The already-proved solved-`A1` product rule gives

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

For `p = q.succ`, the successor solved-`A1` derivative branch gives

```text
d(solvedA1(q.succ))_z(v) = v.1 q.
```

Substitution yields

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(q.succ)
    + Psucc(z) * v.1 q.
```

The noncommutative factor order is unchanged.  The second summand is
`Psucc(z) * v.1 q`, not `v.1 q * Psucc(z)`.

## Kill Conditions

- Do not use `v.1 q.succ` or `v.1 p`; the source tangent is indexed by the
  predecessor `q : Fin M`.
- Do not simplify `solvedA1_z(q.succ)` to a stored source coordinate in this
  theorem.  This slice substitutes only the derivative of the current factor.
- Do not expand or simplify `dPsucc`.
- Do not treat this as a direct downstream `dEarly` specialization.  The
  existing `dEarly` wrapper uses a local current factor `q.castSucc`, so it
  needs a separate zero/successor split or reindexing step.
- Do not claim determinant equality, measure transport, normal crossings,
  pole order, or RLCT.

## Nonclaims

No zero branch, no terminal `Psucc` cleanup, no expansion of `dPsucc`, no
downstream `dEarly` substitution, no determinant theorem, no measure theorem,
no normal crossings, no pole order, and no RLCT follows from this slice.
