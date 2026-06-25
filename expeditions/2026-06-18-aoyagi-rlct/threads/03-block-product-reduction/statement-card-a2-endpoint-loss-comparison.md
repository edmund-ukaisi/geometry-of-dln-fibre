# Statement Card - A2 endpoint loss comparison

## Statement

For a reversed Aoyagi edge family `E`, let `T(E)` be its total endpoint
chain map and let `T(B)` be the base endpoint chain map.  Fix the adapted
endpoint bases determined by `B,U0,hU0` and any original endpoint bases `b`.
There exists `c > 0`, depending only on these fixed endpoint bases, such that
for all parameters `x`,

```text
c * paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss W B U0 hU0 Cedge x
  <= chainMapMatrixFrobeniusLoss b (T(Cedge x)) (T(B)).
```

Equivalently, for the tuple obtained by expressing the same edges in the
original bases,

```text
c * adapted endpoint Frobenius loss
  <= lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

The target matrix in `lossDLN` is the base endpoint map expressed in the
original endpoint bases.

## Lean Names

```text
chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
```

## Dependencies

- `paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum`;
- `paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum`;
- `exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change`;
- `chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum`;
- `lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius`.

## Role In A2

This closes the finite endpoint-coordinate bridge from the fixed adapted
endpoint Frobenius loss to the original square-Frobenius `lossDLN` for
chain-coordinate tuples.  It supplies the previously assumed
`c0 * adapted <= loss` input for exactly this original square-Frobenius loss.

## Nonclaims

No arbitrary-tuple comparison, no statistical/KL/covariance loss comparison,
no chart construction, no source coverage, no density/Jacobian transport, no
residual integrability theorem, no normal-crossing theorem, no pole-order
computation, and no RLCT extraction is proved.
