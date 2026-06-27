# Reproduction - A2 Retained-Passive Raw-Order C1 and Density Continuity

Date: 2026-06-27.

Status: pen-and-paper reproduction for upgrading the retained-passive
raw-order differentiability checkpoint to `C^1` regularity and continuity of
the forward absolute Jacobian determinant.  This is still chart-coordinate
regularity only.

## Elementary C1 Closure

The raw-order map is built from finite products, sums, negations, block
projections, block assembly, and matrix inverse at points where the relevant
top-left determinant is a unit.  Each operation is `C^1` over `Real`:

- finite coordinate projections are continuous linear maps;
- finite matrix multiplication is bounded bilinear;
- finite block projection and block assembly are continuous linear maps;
- matrix inverse is `C^1` at determinant-unit square matrices, by rewriting
  nonsingular inverse as ring inverse and using the standard `ringInverse`
  smoothness theorem.

Thus every differentiability proof already reproduced for the retained-passive
raw-order chart has a parallel `C^1` proof, provided every inverse site carries
the same determinant-unit hypothesis.

## Recursive Products

For a descending residual product

```text
R_i = R_{i+1} * C_i
```

the terminal product is the constant identity, hence `C^1`.  If `R_{i+1}` and
`C_i` are `C^1`, bounded bilinear matrix multiplication gives `R_i` is `C^1`.
The same induction proves:

```text
retainedPassiveA1TailAfterFirst
residualFactorProduct C
residualFactorProduct solvedA1
```

as functions of the ambient topology tuple.

For solved `A1`, the only inverse is

```text
(retainedPassiveA1TailAfterFirst A1seed)^-1.
```

On the tuple determinant chart, the passive `A1` unit hypotheses imply the
tail determinant is a unit, so inverse is `C^1`; multiplying by `Ctop` gives
the zero-index solved `A1`, while successor solved `A1` values are seed
projections.

## Lower-Left Tail

The lower-left product-tail sum has terminal value `0` and step

```text
S_i =
  -( residualFactorProduct C * A3_without_last_i
       * (residualFactorProduct solvedA1)^-1 )
  + S_{i+1}.
```

The `C` residual product, zeroed `A3` family, and solved-`A1` residual product
are already `C^1`.  The inverse is `C^1` because the tuple determinant chart
gives determinant units for solved-`A1` residual products.  Matrix
multiplication, negation, and addition close the step.

For solved `A3`, nonterminal indices are seed projections.  The terminal value
uses the reproduced formula

```text
-(F3 - lowerLeftTail) * residualFactorProduct solvedA1.
```

Both factors are `C^1`, hence the terminal solved `A3` is `C^1`.

## Raw-Order Assembly

The raw-order target components are the same formulas as in the
differentiability reproduction:

```text
A1passive target q =
  A_(q.succ) + F_(q.succ.succ) * L_(q.succ)

F2 target p =
  -(A_p * F_(p.castSucc))
    + F_(p.succ) * (C_p - L_p * F_(p.castSucc))

A3passive target q =
  L_(q.castSucc)

C target p =
  C_p - L_p * F_(p.castSucc)

Ctop target =
  A_0 + F_((0 : Fin (M+1)).succ) * L_0

F3 target =
  L_(Fin.last M).
```

Since all ingredients are `C^1`, every component is `C^1`, and finite pi/product
assembly gives `ContDiffAt Real 1 topologyTupleEdgeRawOrder z` on the
determinant chart.

## Density Continuity

The standard `ContDiffAt.continuousAt_fderiv` theorem turns the forward `C^1`
statement into continuity of

```text
z |-> fderiv Real topologyTupleEdgeRawOrder z.
```

Applying a continuous determinant map on continuous linear endomorphisms and
then absolute value gives continuity of

```text
topologyTupleEdgeRawOrderFDerivAbsDet z.
```

The existing lower/upper local boundedness lemmas required this continuity as
a hypothesis.  The new chart-point continuity theorem supplies it, yielding
no-extra-hypothesis local positive lower and upper bounds at determinant-chart
points.

## Lean Scope

The Lean checkpoint adds `contDiffAt_*` analogues for the forward raw-order
coordinate chain, plus:

```text
contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet
continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
```

## Nonclaims

This does not prove an explicit Jacobian determinant formula, inverse-density
measurability, original source-prior transport, selected-entry target-image
equality, source-rank coverage, normal crossings, pole order, or RLCT.
