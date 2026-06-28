# A2 retained-passive formal-density change of variables: reproduction

## Scope

The retained-passive measure theorem already proves the local raw-order
change-of-variables identity

```text
map raw ((m.restrict S).withDensity (ofReal actualAbsDet)) = m.restrict T,
```

where

```text
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
actualAbsDet z = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

The determinant checkpoint proves on `S` that `actualAbsDet` is the formal
raw-order determinant, and also the solved-`A1` product formula.  Therefore the
source density can be replaced a.e. under `m.restrict S`.

## A.E. Replacement

Let

```text
formalAbsDet z = retainedPassiveFormalRawOrderJacobianAbsDetAt z.
```

For `z ∈ S`, the determinant bridge gives

```text
actualAbsDet z = formalAbsDet z.
```

Since `m.restrict S` is concentrated on `S`,

```text
ofReal formalAbsDet =ᵐ[m.restrict S] ofReal actualAbsDet.
```

Mathlib's `withDensity_congr_ae` then rewrites

```text
(m.restrict S).withDensity (ofReal formalAbsDet)
  =
(m.restrict S).withDensity (ofReal actualAbsDet).
```

Composing with `raw` and using the existing measure theorem gives the formal
density change-of-variables statement.

## Product Density

The product density is

```text
|((retainedPassiveA1TailAfterFirst data.A1seed)^-1).det| ^ card ρ
  * (∏ p, |(coord.solvedA1 p).det| ^ card (κ' p.castSucc))
  * |(coord.solvedA1 (Fin.last M)).det| ^ card (κ' (Fin.last (M + 1))).
```

This is packaged as

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt.
```

The same a.e. replacement proof applies using the actual determinant product
theorem.

## Case Split

The determinant checkpoint is currently split into:

```text
zero-tail:     M = 0,
positive-tail: M = M' + 1.
```

The measure specializations keep this split:

```text
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail
```

## Nonclaims

This checkpoint does not construct an original-source prior, identify a
signed-box source density, prove normal crossings, compute a pole order, or
extract an RLCT.  It only specializes the retained-passive local chart
change-of-variables theorem by a.e. density replacement on the determinant
chart.
