# Reproduction - A2 retained-passive dPcast zero solvedA1 substitution

Date: 2026-06-27.

Status: xhigh pen-and-paper scout reproduced; controller route selected.

This note is independent of the quiver-based paper.  It records the first
source-staging specialization of the retained-passive solved-`A1` residual
product derivative: the current factor is the zero solved top-left block, and
only that current-factor derivative is substituted.

## Setup

Let

```text
p = 0 : Fin (M+1),
A_s(y) = solvedA1_y(s),
Pcast(y) = residualFactorProduct A(y) final p.castSucc,
Psucc(y) = residualFactorProduct A(y) final p.succ.
```

For the zero solved block, write

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = d(Tfun)_z(v),
dCtop   = v.Ctop,
Ctop    = data.Ctop.
```

The determinant-chart hypothesis on `z` remains part of the statement because
the zero solved block contains the inverse of `Tail`.

## Calculation

The already-proved solved-`A1` product rule gives

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(0)
    + Psucc(z) * d(solvedA1 0)_z(v).
```

The zero solved-`A1` derivative branch gives

```text
d(solvedA1 0)_z(v)
  = Tail^-1 * dCtop - Tail^-1 * dTail * Tail^-1 * Ctop.
```

Substituting this branch, and not expanding any other factor, yields

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(0)
    + Psucc(z) *
        (Tail^-1 * dCtop - Tail^-1 * dTail * Tail^-1 * Ctop).
```

This is the selected Lean boundary for this slice.  It keeps `dPsucc`
explicit, leaves the pointwise factor `solvedA1_z(0)` in the first summand,
and keeps `dTail` as the actual Frechet derivative of the passive top-left
tail map.  The optional pointwise unfold
`solvedA1_z(0) = Tail^-1 * Ctop`, and any later cancellation with a
`Psucc = Tail` theorem, are separate cleanups.

## Kill Conditions

- Do not commute factors.  The correction term sits inside the right
  multiplication by `Psucc(z)`:
  `Psucc(z) * (Tail^-1 * dTail * Tail^-1 * Ctop)`.
- Do not replace `dPsucc` by `dTail` in this theorem.
- Do not expand `dTail` into the recursive passive-tail product derivative.
- Do not collapse the whole formula to `dCtop`; that would require additional
  pointwise product identities not included here.
- Do not advertise this as a full `dPcast` source-staging theorem, a `dEarly`
  theorem, a determinant theorem, a measure theorem, normal crossings, pole
  order, or RLCT.

## Nonclaims

No `Psucc = Tail` cleanup, no recursive `dTail` formula, no full `dPcast`
source-staging, no downstream `dEarly` specialization, no target staging, no
determinant theorem, no measure theorem, no normal crossings, no pole order,
and no RLCT follows from this slice.
