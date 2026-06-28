# Statement Card - A2 retained-passive formal-density change of variables

Status: PROVED in Lean, reviewed.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobianMeasure.lean
```

Main Lean names:

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail
map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail
map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail
```

Mathematical content:

- The retained-passive raw-order change-of-variables theorem can use the formal
  raw-order determinant density instead of the abstract actual Frechet
  determinant density.
- It can also use the solved-`A1` product determinant density.
- The proof is by `withDensity_congr_ae` on the determinant chart, using the
  zero-tail or positive-tail determinant bridge.

Checks:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure: passed
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre: passed with pre-existing warning noise
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check: passed
code-only forbidden-marker search in RetainedPassiveCoordinatesJacobianMeasure.lean: no hits
```

Review:

`Volta the 2nd` passed the checkpoint in
`review-a2-retained-passive-formal-density-cov.md`.

Nonclaims:

- No original-source prior.
- No signed-box source-density identification.
- No normal-crossing theorem.
- No pole-order theorem.
- No RLCT theorem.
- No single all-`M` wrapper theorem; the Lean statements are zero-tail and
  positive-tail cases.
