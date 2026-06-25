# Statement Card - A2 chain-map loss bridge

## Statement

Let `M = chainMapMatrixTuple b A` be the core tuple obtained by writing each
edge `A_p : V_p -> V_{p+1}` in fixed bases `b_j`.  For any endpoint target
matrix `B`,

```text
lossDLN d B M
  =
trace(( [chainMap_A(0,last)]_{b_0,b_last} - B )^T
  * ( [chainMap_A(0,last)]_{b_0,b_last} - B )).
```

If the target matrix is the endpoint matrix of another chain `A0`, then

```text
lossDLN d [chainMap_A0(0,last)] M
  =
trace(( [chainMap_A(0,last)] - [chainMap_A0(0,last)] )^T
  * ( [chainMap_A(0,last)] - [chainMap_A0(0,last)] )).
```

For Aoyagi, the target chain can be the base paper-order chain after reversing
vertices: `A0 = reverseEdge W Bpaper`.

## Lean Names

```text
chainMapMatrixFrobeniusLossAgainst
chainMapMatrixFrobeniusLoss
lossDLN_chainMapMatrixTuple_eq_trace
lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius
lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius
```

## Dependencies

- `lossDLN`;
- `chainMapMatrixTuple`;
- `mult_chainMapMatrixTuple`;
- fixed endpoint bases.

## Role In A2

This removes the next loss-wrapper blocker after the tuple/product bridge:
`lossDLN` can now be unfolded to a Frobenius trace on endpoint chain-map
matrices for a tuple built from edge coordinates.

## Nonclaims

No adapted-to-original basis comparison, no positive lower-bound comparison,
no statistical/KL/covariance loss comparison, no product chart, no
density/Jacobian transport, no normal crossings, no pole order, and no RLCT
extraction is proved.
