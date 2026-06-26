# Reproduction - A2 Retained-Passive Solved-A3 Continuity

Date: 2026-06-26.

Status: endpoint-continuity layer for the solved lower-left family in the
nonredundant retained-passive determinant chart.

## Question

After the solved `A1` continuity rung, the remaining endpoint family used by
the retained-passive source map is the solved lower-left family:

```text
solvedA3 = retainedPassiveSolvedA3 solvedA1 A3seed C F3.
```

It is seed-valued away from the final edge and solves the final lower-left
block from the active source-left target `F3`.

## Formula

For a determinant-chart point `data`, write

```text
A p = (data.toCoordinateData).solvedA1 p,
B p = data.A3seed p,
C p = data.C p,
F = data.F3.
```

The zeroed final lower-left family is

```text
Bearly p = retainedPassiveA3WithoutLast B p
         = 0,       if p = Fin.last M,
         = B p,     otherwise.
```

The finite early tail is

```text
earlyTail =
  retainedPassiveLowerLeftProductTailSum A Bearly C 0 (Nat.zero_le (M+1)).
```

The final solved lower-left block is

```text
CtopLast =
  residualFactorProduct A (Fin.last (M+1)) (Fin.last M).castSucc

solvedA3 (Fin.last M) = -(F - earlyTail) * CtopLast.
```

For non-final indices,

```text
solvedA3 p = B p.
```

## Tail-Sum Continuity

The lower-left product-tail sum is a decreasing finite sum with terminal value
zero.  Its recurrence at an edge `p` is

```text
Tail(p.castSucc) =
  -(Ctail(p.succ) * Bearly p * Atail(p.castSucc)^-1)
  + Tail(p.succ),
```

where

```text
Ctail(p.succ) = residualFactorProduct C last p.succ,
Atail(p.castSucc) = residualFactorProduct A last p.castSucc.
```

Continuity of each summand uses:

- continuity of stored `C` products by finite product induction;
- continuity of `Bearly p`, since it is either a stored `A3seed` component or
  constant zero;
- continuity of solved `A1` products by finite product induction from the
  already banked solved-`A1` component continuity;
- determinant-unit propagation for solved `A1` products, using the
  determinant-chart hypotheses and the solved-`A1` unit theorem;
- matrix-inverse continuity for `Atail(p.castSucc)^-1`;
- continuity of matrix multiplication, negation, and addition.

Thus every fixed tail

```text
retainedPassiveLowerLeftProductTailSum A Bearly C m hm
```

is continuous on `{data // data.detChart}`.

## Solved-A3 Continuity

For `p != Fin.last M`, continuity follows from the seed readback formula
`solvedA3 p = A3seed p` and the already banked `A3seed` continuity theorem.

At `p = Fin.last M`, the formula

```text
data ↦ -(data.F3 - earlyTail data) * CtopLast data
```

is continuous by continuity of `F3`, the early-tail theorem, solved-`A1`
product continuity for `CtopLast`, subtraction, negation, and multiplication.

## Lean Boundary

Lean proves:

```text
continuous_retainedPassiveA3WithoutLast
continuous_residualFactorProduct_C
solvedA1_det_isUnit_of_detChart
continuous_residualFactorProduct_solvedA1_detChart_subtype
residualFactorProduct_solvedA1_det_isUnit_of_detChart
continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
continuous_solvedA3_detChart_subtype
```

These are endpoint-continuity and finite-tail support lemmas.  They do not
prove continuity of `toCoordinateData` or `edgeMatrix`.

## Nonclaims

This rung does not prove continuity of `edgeMatrix`, image openness,
source-rank coverage, source/image equality, measure transport,
density/Jacobian accounting, normal crossings, pole order, or RLCT
extraction.
