# Statement Card - A2 retained-passive actual derivative tuple shear assembly

Status: reproduced and Lean-proved; xhigh review pending.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent vector
`v`, the tuple obtained from the actual raw-order Frechet derivative by the
landed component corrections agrees componentwise with the point-specialized
formal raw-order Jacobian:

```text
shearedTopologyTupleEdgeRawOrderFDerivAt z v
  = retainedPassiveFormalRawOrderJacobianAt z v.
```

## Lean Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New names:

```text
shearedTopologyTupleEdgeRawOrderFDerivAt
sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Focused local build passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

## Dependencies

- all retained-passive actual derivative component bridges:
  `A1passive`, `F2`, passive `A3`, `C`, `Ctop`, and terminal `F3`;
- formal raw-order apply formula through
  `retainedPassiveFormalRawOrderJacobianAt`;
- product extensionality for the nested retained-passive raw tuple.

## Nonclaims

This proves a tuple-level component assembly only.  It does not prove that the
actual Frechet derivative has the same determinant as the formal raw-order map,
does not construct a determinant-one shear equivalence, and does not imply a
measure, normal-crossing, pole-order, or RLCT statement.
