# Reproduction - A2 Retained-Passive Formal Non-Edge Recovery

Date: 2026-06-27.

Status: pen-and-paper reproduction for a formal raw-order inverse bookkeeping
slice.  This is about the point-specialized formal map, not the actual
Frechet derivative of `topologyTupleEdgeRawOrder`.

## Setup

For a retained-passive raw tuple `z`, write

```text
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
Tail  = retainedPassiveA1TailAfterFirst data.A1seed,
Last  = coord.solvedA1 (Fin.last M),
u     = retainedPassiveFormalRawOrderJacobianAt z v.
```

The formal raw-order apply formula is

```text
u.A1passive_p = v.A1passive_p,
u.F2_p        = -(A_p + H_p G_p) v.F2_p + H_p v.C_p,
u.A3passive_p = v.A3passive_p,
u.C_p         = -G_p v.F2_p + v.C_p,
u.Ctop        = Tail^{-1} * v.Ctop,
u.F3          = v.F3 * (-Last).
```

The edge-pair inverse/recovery for `F2` and `C` already exists.  This slice
records the remaining non-edge branches.

## Recovery Formulas

The passive top-left branch is diagonal:

```text
u.A1passive_p = v.A1passive_p.
```

The first top-left branch is recovered by left multiplication with `Tail`:

```text
Tail * u.Ctop
  = Tail * (Tail^{-1} * v.Ctop)
  = v.Ctop.
```

The determinant-chart hypothesis gives `IsUnit Tail.det` from the passive
`A1` determinant units, so the last equality is the nonsingular inverse
cancellation.

The terminal lower-left branch is recovered by right multiplication with the
inverse of `-Last`:

```text
u.F3 * (-Last)^{-1}
  = (v.F3 * (-Last)) * (-Last)^{-1}
  = v.F3.
```

The determinant-chart hypothesis gives `IsUnit Last.det`, hence
`IsUnit (-Last).det`, so the last equality is the right nonsingular inverse
cancellation.

## Kill Conditions

- These are formal-map recovery identities.  They do not say that the actual
  Frechet derivative has already been converted into the formal map by a
  determinant-one target-side equivalence.
- The `Ctop` and `F3` recovery lemmas need determinant-chart hypotheses for
  `Tail` and `Last`; dropping those hypotheses is not justified by this
  calculation.
- These formulas do not source-stage the `Ctop` or `F3` branches.  The actual
  derivative still has the tail-inverse derivative correction in `Ctop` and the
  early-tail/terminal-top corrections in `F3`.

## Nonclaims

No source staging, no target-side `LinearEquiv`, no determinant-one shear, no
actual derivative determinant equality, no density or measure theorem, no
normal crossings, no pole order, and no RLCT statement is proved by this slice.
