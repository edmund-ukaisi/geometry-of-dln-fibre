# Reproduction - A2 Retained-Passive Solved A1 Derivative

Date: 2026-06-26.

Status: pen-and-paper reproduction for the first retained-passive derivative
foothold.  The Lean checkpoint proves differentiability only, not an explicit
derivative formula or determinant.

## Coordinate Setup

Work in the retained-passive nonredundant tuple coordinates

```text
z = (a, (f, (ell, (c, (s, h)))))
```

where the top-left passive family is

```text
a : Fin M -> Matrix rho rho R
```

and the endpoint top-left variable is `s : Matrix rho rho R`.

The full top-left seed used by the retained-passive coordinate data is

```text
A1seed_0 = 0
A1seed_(q+1) = a_q.
```

The determinant chart requires the passive top-left blocks to be determinant
units.  Define the tail product

```text
T = retainedPassiveA1TailAfterFirst A1seed.
```

With the local product convention in Lean, the solved endpoint is

```text
solvedA1_0 = T^{-1} * s,
solvedA1_(q+1) = a_q.
```

The Lean continuity layer had already proved this endpoint solve is continuous.
The derivative checkpoint upgrades only the differentiability part needed for
the future raw-order derivative theorem.

## Differentiability Reproduction

The passive coordinate projections are differentiable because the ambient tuple
space is a finite product of matrix coordinate spaces.  The zero-filled dummy
slots

```text
A1seed_0
F2full_last
A3seed_last
```

are constant functions, hence differentiable.  The nonzero slots are coordinate
projections.

The tail product `T` is differentiable by descending induction over the same
product recursion used in the continuity proof:

```text
residualFactorProduct(..., j, j) = 1
residualFactorProduct(..., j, p.castSucc)
  = residualFactorProduct(..., j, p.succ) * A1seed_p.
```

The base case is constant.  The induction step uses differentiability of square
matrix multiplication, since both factors are `rho x rho` matrices.

At a determinant-chart tuple, every passive top-left factor is a determinant
unit, so the product `T` is a determinant unit.  Matrix inversion is
differentiable at determinant-unit square matrices, using the already-proved
one-step inverse derivative lemma.  Therefore

```text
z |-> T(z)^{-1}
```

is differentiable at the tuple.  Multiplying by the endpoint coordinate `s`
gives differentiability of

```text
z |-> solvedA1_0(z) = T(z)^{-1} * s(z).
```

For successors, `solvedA1_(q+1)` is just the corresponding passive coordinate
projection.  Thus every solved top-left block is differentiable on the tuple
determinant chart.

## Lean Scope

The Lean checkpoint intentionally stops at:

```text
differentiableAt_retainedPassiveA1TailAfterFirst
differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
```

plus coordinate-projection helpers for the retained-passive tuple fields.

The lower-left endpoint solve, the full raw-order endomap
`topologyTupleEdgeRawOrder`, the tangent map, determinant unit, Jacobian
density, measure pushforward, normal-crossing theorem, pole order, and RLCT
remain unproved.

