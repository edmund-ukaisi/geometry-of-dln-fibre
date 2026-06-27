# Reproduction - A2 Retained-Passive Ctop Tail Endpoint Substitution

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

## Setup

The existing Ctop bridge after inverse-tail substitution has the form

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
  + Tail^{-1} * dTail * Tail^{-1} * coord.Ctop
= formal(z)(v).Ctop.
```

Here

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = d(Tfun)_z(v).
```

The previous tail-inverse slice already fixed the sign: this term is positive
because the raw derivative contained `-d(Tail^{-1}) * coord.Ctop` and

```text
d(Tail^{-1}) = -Tail^{-1} * dTail * Tail^{-1}.
```

This slice only substitutes the endpoint formulas for `dTail`.

## Empty Tail

When `M=0`, the tail after the first edge is the empty product.  The endpoint
tail theorem gives

```text
dTail = 0.
```

Therefore the Ctop bridge reduces to

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
= formal(z)(v).Ctop.
```

No determinant-chart hypothesis is added for the tail derivative itself; the
existing Ctop bridge still has its determinant-chart hypothesis because it
passes through the inverse-tail theorem.

## First Passive Step

For a nonempty passive tail, with first passive source index

```text
q = 0,
p = q.succ,
Psucc(y) = residualFactorProduct A1seed(y) (Fin.last ...) p.succ,
```

the endpoint tail theorem gives

```text
dTail = d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_q.
```

Substituting this into the Ctop bridge gives

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
  + Tail^{-1}
      * (d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_q)
      * Tail^{-1}
      * coord.Ctop
= formal(z)(v).Ctop.
```

The product order is not rearranged.  The new source tangent is the right
factor in `Psucc(z) * v.A1passive_q`, and the entire substituted `dTail`
remains between the two `Tail^{-1}` factors.

## Kill Conditions

- If the sign of the tail contribution becomes negative, this contradicts the
  already checked inverse-tail substitution.
- If the substituted `dTail` is moved outside the two inverse-tail factors,
  the matrix product order is wrong.
- If the `Psucc(z) * v.A1passive_q` term is reversed, the recurrence order is
  wrong.
- If the theorem includes dummy `A1seed 0` as a tail factor, it is not the
  retained-passive tail after the first edge.
- If the theorem claims a closed finite-sum expansion for `dTail`, determinant
  equality, measure transport, normal crossings, pole order, or RLCT, it
  overclaims.

## Nonclaims

This is not a closed finite-sum formula for `dTail` and not a full `Ctop`
source staging theorem.  It leaves the suffix derivative `d(Psucc)` explicit.
It proves no `F3` staging, determinant equality, measure transport, normal
crossings, pole order, or RLCT.
