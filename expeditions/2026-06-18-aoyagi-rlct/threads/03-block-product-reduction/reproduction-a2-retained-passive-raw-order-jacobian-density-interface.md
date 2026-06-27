# Reproduction - A2 Retained-Passive Raw-Order Jacobian Density Interface

Date: 2026-06-27.

Status: pen-and-paper reproduction for the first retained-passive raw-order
Jacobian-density interface after the ambient `fderiv` determinant-unit theorem.
This slice is deliberately density-local: it proves pointwise positivity of
the absolute determinant and records that local two-sided bounds require a
separate continuity input.

Source anchor: Aoyagi 2023 pp. 10-13, especially the block-elimination and
product-reduction coordinate changes used in the proof of Lemma 2 and Theorem
3.  No quiver-paper input is used.

## Setup

Let

```text
S = topologyTupleDetChartSet,
f = topologyTupleEdgeRawOrder.
```

For `z in S`, the previous slice proved

```text
det(Df_z) is a unit in R.
```

Here `Df_z` denotes the ambient Frechet derivative, as a finite-dimensional
real linear endomorphism of the retained-passive raw tuple space.

Define the forward absolute Jacobian determinant by

```text
Jabs(z) = |det(Df_z)|.
```

This is the scalar factor that a later change-of-variables theorem would use
on the source side.  The definition alone is not a measure theorem and does
not identify a transported source density.

## Pointwise Positivity

For `z in S`, the determinant-unit theorem gives

```text
det(Df_z) != 0.
```

Over `R = real`, absolute value is positive precisely away from zero.  Hence

```text
0 < |det(Df_z)| = Jabs(z).
```

Since `S` is open, if `z0 in S`, then `z in S` for all sufficiently nearby
`z`.  Applying the same pointwise argument to each nearby chart point gives

```text
eventually in nhds(z0), 0 < Jabs(z).
```

This eventual positivity uses openness of the chart domain, not continuity of
`Jabs`.

## Supplied-Continuity Local Bounds

The pointwise unit statement does not imply a quantitative lower bound in a
neighborhood.  To get such a bound at `z0`, assume separately that

```text
Jabs is continuous at z0.
```

By pointwise positivity, `Jabs(z0) > 0`.  Continuity at `z0` applied to the
open ray

```text
(Jabs(z0) / 2, infinity)
```

gives

```text
eventually in nhds(z0), Jabs(z0) / 2 <= Jabs(z).
```

Thus there exists `epsilon > 0` such that

```text
eventually in nhds(z0), epsilon <= Jabs(z).
```

The same continuity hypothesis applied to the upper ray

```text
(-infinity, Jabs(z0) + 1)
```

and then enlarged by `max (Jabs(z0) + 1) 1` gives a positive upper bound:

```text
there exists K > 0 such that eventually in nhds(z0), Jabs(z) <= K.
```

## Boundary

This slice does not prove continuity of `z |-> Df_z`, continuity of `Jabs`, a
closed determinant formula, a pushforward/change-of-variables theorem, a
transported source density identity, normal crossings, pole order, or an RLCT
statement.  Those require either an explicit derivative-family computation or
a separate measure-theoretic chart theorem.
