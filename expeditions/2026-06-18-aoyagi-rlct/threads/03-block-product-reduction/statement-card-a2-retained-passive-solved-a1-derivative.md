# Statement Card - A2 Retained-Passive Solved A1 Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre.lean
```

## Lean Names

```text
differentiableAt_matrix_inv_of_isUnit_det
differentiableAt_A1passive
differentiableAt_F2
differentiableAt_A3passive
differentiableAt_C
differentiableAt_Ctop
differentiableAt_F3
differentiableAt_A1seed
differentiableAt_F2full
differentiableAt_A3seed
differentiableAt_retainedPassiveA1TailAfterFirst
differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a1-derivative.md
```

## Claim

In the retained-passive tuple coordinate space over `Real`, the coordinate
projections and zero-filled seed slots are differentiable.  The passive
top-left tail product

```text
z |-> retainedPassiveA1TailAfterFirst (ofTopologyTuple z).A1seed
```

is differentiable.  At a tuple in `topologyTupleDetChartSet`, every solved
top-left block

```text
z |-> (ofTopologyTuple z).toCoordinateData.solvedA1 p
```

is differentiable.

## Method

The tail-product proof mirrors the existing continuity proof by descending
induction on `residualFactorProduct`.  The induction step uses square matrix
multiplication.  The endpoint solve uses the existing determinant-unit matrix
inverse derivative and the determinant-chart proof that the passive tail
product has determinant unit.

The projection lemmas use finite product-space differentiability.  Their public
hypotheses are `Finite` for the tuple-index types, with local `Fintype`
instances created by `Fintype.ofFinite` only inside the proofs.

## Role

This is the first analytic derivative foothold for the retained-passive
raw-order Jacobian program.  It establishes differentiability of the solved
top-left family, which is one required component of the future
`topologyTupleEdgeRawOrder` differentiability theorem.

## Nonclaims

No solved lower-left differentiability, full raw-order derivative, tangent
equivalence, determinant formula, Jacobian density, measure pushforward, image
equality, source-rank coverage, normal crossings, pole order, or RLCT
statement is proved here.

