# Statement Card - A2 retained-passive full target normaliser determinant bridge

Status: PROVED in Lean, reviewed.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Main Lean names:

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_A3passive
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_eq_formalRawOrderJacobianAt
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_posTail
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_zeroTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail
```

Mathematical content:

- The zero-tail and positive-tail determinant-one target normalisers send
  `(fderiv raw z) v` to the full formal raw-order Jacobian.
- The full tuple equality is assembled componentwise from already proved
  `A1passive`, `(F2,C)`, `A3passive`, `Ctop`, and `F3` bridges.
- The actual raw-order Frechet derivative absolute determinant equals the
  point-specialized formal raw-order absolute determinant in both cases.
- The actual raw-order Frechet derivative absolute determinant satisfies the
  solved-`A1` product formula in both cases.

Inputs used:

- The determinant-one composed target maps for zero-tail and positive-tail
  cases.
- Component bridges through the edge-pair, `A1passive`, `Ctop`, and `F3`
  stages.
- The conditional determinant bridge and its product-form theorem.

Checks:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian: passed
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check: passed
code-only forbidden-marker search in RetainedPassiveCoordinatesJacobian.lean: no hits
```

Review:

`Sartre the 2nd` passed the checkpoint in
`review-a2-retained-passive-full-target-normaliser-determinant-bridge.md`.

Nonclaims:

- No measure transport theorem.
- No normal-crossing theorem.
- No pole-order theorem.
- No RLCT theorem.
- No single all-`M` wrapper theorem; the Lean statements are zero-tail and
  positive-tail cases.
