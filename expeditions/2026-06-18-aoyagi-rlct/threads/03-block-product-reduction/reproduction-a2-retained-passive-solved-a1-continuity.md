# Reproduction - A2 Retained-Passive Solved-A1 Continuity

Date: 2026-06-26.

Status: first inverse-dependent endpoint-continuity layer for the
nonredundant retained-passive determinant chart.

## Question

The nonredundant retained-passive chart stores passive top-left blocks

```text
A1passive p,  p : Fin M,
```

and an active top block `Ctop`.  The full top-left family used by the source
map is not stored directly.  It is solved from the passive tail and `Ctop`:

```text
Tail(A1seed) = A1_M * ... * A1_1,
solvedA1 0 = Tail(A1seed)^-1 * Ctop,
solvedA1 p = A1seed p,  p != 0.
```

The goal of this rung is only continuity of these solved `A1` components on
the determinant-chart subtype.

## Tail Product

The passive tail is

```text
retainedPassiveA1TailAfterFirst(A1seed)
  = residualFactorProduct A1seed last (0.succ).
```

The product is finite.  Reading it from the right endpoint, the base case is
the constant identity matrix.  The induction step is

```text
Product(p.castSucc) = Product(p.succ) * A1seed p.
```

The previously proved projection-continuity layer gives continuity of
`data ↦ data.A1seed p`; matrix multiplication is continuous over the normed
field.  Therefore the passive tail is continuous as a function of the
nonredundant coordinate data.

## Determinant-Chart Inverse

On the determinant-chart subtype, each passive block `A1passive p` has unit
determinant.  The helper

```text
toCoordinateData_passiveA1_units
```

turns this into the older side condition

```text
IsUnit (A1seed p).det,  p != 0.
```

The finite product theorem

```text
retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
```

then gives `IsUnit det(Tail(A1seed))` at every point of the determinant-chart
subtype.  The existing matrix-inverse continuity theorem applies to the
continuous tail family, so

```text
data ↦ Tail(data.A1seed)^-1
```

is continuous on the subtype.

Multiplying by the already continuous `Ctop` projection proves continuity of

```text
data ↦ Tail(data.A1seed)^-1 * data.Ctop,
```

which is exactly the zero component of `solvedA1`.

## Passive Components

For `p != 0`, the solved family is just the seed family:

```text
solvedA1 p = A1seed p.
```

Thus the nonzero components are continuous by the componentwise `A1seed`
continuity theorem.

## Lean Boundary

Lean proves:

```text
continuous_retainedPassiveA1TailAfterFirst
continuous_solvedA1_detChart_subtype
```

The first is global continuity of the passive tail product.  The second is
componentwise continuity of the solved full `A1` family on
`{data // data.detChart}`.

## Nonclaims

This rung does not prove continuity of `solvedA3`, `toCoordinateData`, or
`edgeMatrix`.  It does not prove image openness, source-rank coverage,
source/image equality, measure transport, density/Jacobian accounting, normal
crossings, pole order, or RLCT extraction.
