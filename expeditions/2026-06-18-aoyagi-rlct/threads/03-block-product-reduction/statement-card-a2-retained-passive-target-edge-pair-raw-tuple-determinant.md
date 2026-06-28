# Statement card: A2 retained-passive target edge-pair raw-tuple determinant

## Claim

For fixed retained-passive `z` in the determinant chart, the full raw-tuple
target edge-pair shear linear equivalence has determinant one.  The theorem is
about the full raw tuple

```text
w = (A1passive, F2, A3passive, C, Ctop, F3),
```

not about the formal separated `(F2,C)` equivalence alone.

## Proposed Lean Surface

```text
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_abs_det_eq_one
```

Supporting generic determinant infrastructure:

```text
linearMap_det_finSuccUpperTriangular_eq_prod
linearMap_det_finSuccUpperUnitriangular_eq_one
finSuccUpperUnitriangularLinearMap_det_eq_one
```

## Hypotheses

Use the same finite-index hypotheses as the raw-tuple equivalence layer, plus
`hz : z ∈ topologyTupleDetChartSet`, needed for the formal edge-pair inverse.

## Lean Status

Proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
The inverse shear is conjugated by the edge-block regrouping
`(A1_q,A3_q,F_q,C_q)`, then proved successor-upper-triangular with
determinant-one same-edge diagonal blocks.  The forward equivalence determinant
follows from `det(e) * det(e.symm) = 1`, and the absolute determinant theorem
is the real absolute-value wrapper around determinant one.

Focused builds of
`DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, as did
`scripts/sorries`, `git diff --check`, and the code-only forbidden-marker
search.

## Proof Plan

1. Regroup the full raw tuple into edge blocks in determinant-friendly order.
2. In those coordinates, split the inverse shear into same-edge diagonal
   shears and successor off-diagonal contributions.
3. Use the generic `Fin` successor-upper-triangular determinant lemma to
   reduce the determinant to the product of same-edge determinants.
4. Prove each same-edge block shear has determinant one by lower-triangular
   product determinant lemmas.
5. Transport the determinant back across the regrouping equivalence.

## Nonclaims

This does not prove determinant one for
`retainedPassiveFormalRawF2CLinearEquivAt`; that map has nontrivial diagonal
factors.  It also does not prove determinant equality for the actual
raw-order Frechet derivative, source-prior transport, inverse-density
pushforward, normal crossings, pole order, or RLCT.
