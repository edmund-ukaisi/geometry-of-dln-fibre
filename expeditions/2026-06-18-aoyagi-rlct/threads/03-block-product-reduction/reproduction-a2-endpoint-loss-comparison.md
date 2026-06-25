# Reproduction - A2 endpoint loss comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean implementation; independent
review pending.

## Source Anchor

This is finite-dimensional real linear algebra connecting two endpoint
coordinate expressions for the same chain-map product difference.  It is not a
new theorem from Aoyagi.  Its role is to connect the fixed adapted endpoint
Frobenius loss already formalised from the p. 13 block coordinates to the
repository's original `lossDLN` square-Frobenius loss for tuples built from
the same edge maps.

## Derivation

Let `E` be a variable reversed Aoyagi edge family and let `B` be the base
paper-order chain.  Write

```text
T(E)  = chainMap(reverseVertex W, E, 0, last),
T(B)  = chainMap(reverseVertex W, reverseEdge W B, 0, last).
```

Fix two endpoint basis pairs for the same endpoint linear maps:

```text
a_0, a_last  : fixed adapted endpoint bases from B and U0,
b_0, b_last  : arbitrary original endpoint bases.
```

The fixed adapted endpoint Frobenius loss is

```text
A(E) = || [T(E) - T(B)]_{a_0,a_last} ||_F^2.
```

The chain-map loss bridge identifies the original DLN loss of the tuple
formed from the same edge maps in the `b_j` bases as

```text
O(E) = lossDLN d [T(B)]_{b_0,b_last} (chainMapMatrixTuple b E)
     = || [T(E) - T(B)]_{b_0,b_last} ||_F^2.
```

The finite basis-change comparison applies to the single linear map

```text
f(E) = T(E) - T(B).
```

Since the two endpoint basis pairs are fixed, there is a constant `c > 0`,
depending only on the basis changes, such that for every endpoint map `f`,

```text
c * || [f]_{a_0,a_last} ||_F^2
  <= || [f]_{b_0,b_last} ||_F^2.
```

Applying this to `f(E)` gives

```text
c * A(E) <= O(E).
```

The target matrix on the original-loss side must be the matrix of the base
endpoint map in the original endpoint bases.  Reusing the adapted block
matrix `[[I,0],[0,0]]` as a raw original-coordinate target would be a
different statement and is not justified by this argument.

## Lean Shape

Lean implements this in

```text
lean/DLNFibre/DLN/Aoyagi/EndpointLossComparison.lean
```

with names

```text
chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
```

The first theorem rewrites `chainMapMatrixFrobeniusLoss` as the coordinate
square-sum of `LinearMap.toMatrix ... (T - T0)`.  The second theorem applies
the uniform basis-change comparison between the fixed adapted endpoint bases
and arbitrary original endpoint bases.  The third theorem rewrites the right
side through `lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius`.

## Boundary

This is only a finite endpoint basis comparison for square-Frobenius losses.
It applies to the `lossDLN` tuple only when the tuple is
`chainMapMatrixTuple b E` for the same edge family `E`.

It does not compare statistical, KL, covariance, or noisy losses; it does not
construct the p. 13 chart, prove source coverage, transport density/Jacobian
factors, prove residual integrability, produce normal crossings, compute pole
order, or extract an RLCT.
