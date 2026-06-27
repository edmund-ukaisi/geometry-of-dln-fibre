# Review - A2 retained-passive conditional determinant/Jacobian bridge

Reviewer: xhigh `Noether the 2nd`

Verdict: PASS.

## Scope

Artifacts reviewed:

- `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`
  - `topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv`
  - `topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_of_target_linearEquiv`
- `reproduction-a2-retained-passive-conditional-determinant-jacobian-bridge.md`
- `statement-card-a2-retained-passive-conditional-determinant-jacobian-bridge.md`

## Findings

No required fixes.

The Lean bridge matches the pen-and-paper determinant bridge.  The hypotheses
are exactly a supplied target-side linear equivalence `T`, the pointwise
identity

```text
T ((fderiv topologyTupleEdgeRawOrder z) v)
  = retainedPassiveFormalRawOrderJacobianAt z v,
```

and `|det T| = 1`.  The proof converts the pointwise identity to
`F = T.comp D`, applies `LinearMap.det_comp`, and unfolds the actual and formal
absolute determinant definitions.

The product corollary is only a rewrite.  It first invokes the conditional
bridge, then rewrites the formal side using
`retainedPassiveFormalRawOrderJacobianAbsDetAt_eq`.  It does not construct `T`
and does not assert source-prior transport, normal crossings, pole order, or
RLCT.

The reproduction and statement card are aligned with the formal scope.  Both
record the determinant-one supplied-equivalence assumption and the nonclaims.

## Independent checks

The reviewer checked read-only that `git diff --check` was clean and that there
were no downstream uses of the new theorem names beyond the product corollary
and the two docs.  The reviewer did not run Lean; the controller ran the Lean
builds and axiom audits separately.
