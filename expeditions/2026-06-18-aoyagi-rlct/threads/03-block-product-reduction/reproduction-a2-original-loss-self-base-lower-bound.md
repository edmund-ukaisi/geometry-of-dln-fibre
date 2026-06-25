# Reproduction - A2 original loss self-base lower bound

Date: 2026-06-25.

Status: pen-and-paper reproduction, Lean implementation, and independent
review passed.

## Source Anchor

This is a source-filter lower-bound bridge at the fixed Aoyagi base point.  It
combines two already-formalised elementary ingredients:

- the p.13 self-base product-reduction lower bound from cleaned
  regular-plus-residual coordinates to the fixed adapted endpoint square-sum;
- the finite endpoint basis comparison from the fixed adapted endpoint
  square-sum to original square-Frobenius `lossDLN`.

It is not the product-chart finite-integral theorem.  In particular, it does
not introduce an independent regular fiber variable `u`; it only treats the
one-parameter edge family `Cedge x`.

## Derivation

Let `E(x)` be the reversed edge family `Cedge x`, and write

```text
T(E(x)) = chainMap(reverseVertex W, E(x), 0, last),
T(B)    = chainMap(reverseVertex W, reverseEdge W B, 0, last).
```

The existing self-base p.13 theorem gives a positive constant `a > 0` such
that eventually on the source-rank stratum,

```text
(a / 2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x).
```

Equivalently, using the fixed adapted Frobenius/square-sum identification,

```text
(a / 2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceFrobeniusLoss(x).
```

The endpoint basis-comparison theorem gives a second positive constant
`b > 0`, independent of `x`, such that for every `x`,

```text
b * adaptedProductDifferenceFrobeniusLoss(x)
  <= lossDLN d [T(B)]_b (chainMapMatrixTuple b E(x)).
```

Multiplying the first inequality by `b` and composing with the second gives

```text
b * ((a / 2) * (regularSquareSum(x) + residualSquareSum(x)))
  <= lossDLN d [T(B)]_b (chainMapMatrixTuple b E(x)).
```

Set `c = a * b`.  Since `a > 0` and `b > 0`, `c > 0`, and elementary ring
arithmetic rewrites the left side as

```text
(c / 2) * (regularSquareSum(x) + residualSquareSum(x)).
```

Thus eventually on the source-rank stratum,

```text
(c / 2) * (regularSquareSum(x) + residualSquareSum(x))
  <= lossDLN d [T(B)]_b (chainMapMatrixTuple b E(x)).
```

The target matrix must be `[T(B)]` in the same original endpoint bases used by
`chainMapMatrixTuple`.  Reusing the fixed adapted block target in original
coordinates would be a different statement.

## Lean Target

The intended Lean theorem belongs near the endpoint comparison results:

```text
exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
```

It should assume:

- `sourceData : PaperEndpointFixedBaseRegularCoordinateSourceData ... Cedge H r rEdge`;
- original bases `b`;
- `ContinuousAt Cedge x0`;
- the self-base condition `Cedge x0 = reverseEdge W B` as continuous linear
  maps.

It should conclude an existential positive constant and an eventual source
filter lower bound for original `lossDLN`.

## Boundary

This theorem is a one-parameter source-filter lower bound.  It does not
construct the p.13 product chart, identify a fiber variable with regular
coordinates, prove signed-box source measure transport, prove density/Jacobian
transport, produce normal crossings, compute pole order, or extract an RLCT.
