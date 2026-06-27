# Statement Card - A2 retained-passive conditional determinant/Jacobian bridge

## Claim

If a target-side linear equivalence `T` sends the actual retained-passive
raw-order Frechet derivative at `z` to the point-specialized formal raw-order
Jacobian and has absolute determinant one, then the actual forward raw-order
absolute Jacobian determinant equals the formal raw-order absolute determinant.

The product-form corollary rewrites this common value using the existing
formal product determinant formula.

## Lean names

```text
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_of_target_linearEquiv
```

## Hypotheses

- `z : RetainedPassiveRawTopologyTuple rho kappa' R`.
- `T : RetainedPassiveRawTopologyTuple rho kappa' R ~=l[R]
  RetainedPassiveRawTopologyTuple rho kappa' R`.
- For every tangent `v`,
  `T ((fderiv R topologyTupleEdgeRawOrder z) v) =
  retainedPassiveFormalRawOrderJacobianAt z v`.
- `|det T| = 1`.

No determinant-chart membership hypothesis is needed for this pure determinant
identity.  Chart membership is needed elsewhere to construct or bound the
actual derivative and formal determinant, and to prove positivity.

## Proof shape

1. Extensionality turns the pointwise hypothesis into
   `retainedPassiveFormalRawOrderJacobianAt z = T.comp D`.
2. `LinearMap.det_comp` gives
   `det(F_z) = det(T) * det(D)`.
3. Absolute values and `|det T| = 1` give
   `|det(F_z)| = |det(D)|`.
4. Unfold the two local absolute determinant definitions.
5. For the product corollary, rewrite the formal side using
   `retainedPassiveFormalRawOrderJacobianAbsDetAt_eq`.

## Dependencies

- `topologyTupleEdgeRawOrderFDerivAbsDet` from
  `RetainedPassiveCoordinatesDerivative.lean`.
- `retainedPassiveFormalRawOrderJacobianAt` and
  `retainedPassiveFormalRawOrderJacobianAbsDetAt` from
  `RetainedPassiveCoordinatesJacobian.lean`.
- `retainedPassiveFormalRawOrderJacobianAbsDetAt_eq` for the product formula.
- `LinearMap.det_comp` and elementary absolute-value algebra.

## Nonclaims

This does not construct the target-side determinant-one linear equivalence.
It does not assert that the current componentwise sheared derivative packaging
is already a determinant-one linear equivalence.  It does not prove source-prior
transport, inverse-density pushforward, normal crossings, pole order, or RLCT.

## Review focus

- The theorem must be conditional on a supplied `LinearEquiv`.
- The pointwise comparison must use the same vector space and the actual
  Frechet derivative of `topologyTupleEdgeRawOrder`.
- The determinant-one hypothesis must be absolute-value `= 1`, not signed
  determinant `= 1`.
- The product corollary must be only a rewrite through the formal determinant
  formula.
