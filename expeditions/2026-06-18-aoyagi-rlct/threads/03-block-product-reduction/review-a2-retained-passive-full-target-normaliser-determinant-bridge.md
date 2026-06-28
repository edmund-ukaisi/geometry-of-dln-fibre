# Review - A2 retained-passive full target normaliser determinant bridge

Reviewer: `Sartre the 2nd`, xhigh read-only reviewer.

Verdict: PASS.

Scope:

- `retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_A3passive`.
- `retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_eq_formalRawOrderJacobianAt`.
- `retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_eq_formalRawOrderJacobianAt`.
- `topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_posTail`.
- `topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_zeroTail`.
- `topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail`.
- `topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail`.
- The reproduction note, statement card, thread entry, and scope boundaries.

Findings:

- Full tuple coverage is present for `A1passive`, `(F2,C)`, `A3passive`,
  `Ctop`, and `F3` before product extensionality in both positive-tail and
  zero-tail proofs.
- The new `A3passive` preservation helper is correctly scoped to the `Ctop`
  stage and proves that `T123.A3passive = T12.A3passive`.
- Positive-tail indexing is consistent: the public theorem is for actual tail
  `M + 1`, while the positive-tail normaliser itself is instantiated with
  parameter `M`.
- Zero-tail determinant and product bridges use the zero-tail target map and
  matching determinant-one theorem.
- The notes state the zero-tail and positive-tail full raw-tuple and
  determinant/product results and explicitly exclude measure transport, normal
  crossings, pole order, RLCT, and a single all-`M` theorem.

Checks reported by reviewer:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian: passed
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check: passed
forbidden-marker search in touched Lean file: no hits
```
