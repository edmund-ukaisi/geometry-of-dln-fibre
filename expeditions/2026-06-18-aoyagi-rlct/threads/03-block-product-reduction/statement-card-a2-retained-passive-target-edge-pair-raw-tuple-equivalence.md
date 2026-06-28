# Statement card: A2 retained-passive target edge-pair raw-tuple equivalence

## Claim

For fixed retained-passive `z` on the determinant chart, the target-side
edge-pair normalization extends to a linear equivalence of the full retained
passive raw topology tuple by fixing `A1passive`, `A3passive`, `Ctop`, and
`F3`, and replacing only `(F2,C)` by
`retainedPassiveTargetEdgePairShearAt z w`.

## Proposed Lean Surface

```text
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
retainedPassiveTargetRecoveredF2At_rawTupleInverse
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_apply
```

## Hypotheses

Use the same finite-index assumptions as the retained-passive target linear-map
package, plus the determinant-chart membership `hz` only where the formal
edge-pair inverse is used.

## Lean Status

Current checkpoint proves the forward raw-tuple linear map, the inverse
raw-tuple linear map, their apply formulas, the two direction identities, and
the resulting `LinearEquiv` package:

```text
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst
retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_leftInverse
retainedPassiveTargetRecoveredF2At_rawTupleInverse
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_apply
```

A separate determinant card now records the determinant-one theorem for this
full raw-tuple equivalence.

## Proof Plan

1. Define the forward full-tuple linear map by pairing the existing
   `retainedPassiveTargetEdgePairShearLinearMapAt` with identity maps on the
   side fields.
2. Define the inverse linear map using only
   `X := ((retainedPassiveFormalRawF2CLinearEquivAt hz).symm (y.F2,y.C)).1`;
   do not use the formal inverse's second component as a recovered raw `C`
   field for arbitrary target tuples.
3. Prove the formal inverse first component of the forward pair is exactly
   `retainedPassiveTargetRecoveredF2At z w`.
4. Prove the target recovery recurrence on the inverse tuple returns the
   formal-inverse first component.
5. Use these two recovery facts to prove the two linear maps are mutual
   inverses and package them as a `LinearEquiv`.
6. Later, prove determinant control by a unitriangular factorization or direct
   determinant computation; do not infer determinant one from the formal
   edge-pair equivalence.

## Lean Proof Note

The mutual-inverse proof is deliberately not one broad `simp` pass.  It uses
local readback lemmas for tuples that replace only `(F2,C)` while fixing
`A1passive`, `A3passive`, `Ctop`, and `F3`; rewrites successor recovery from
the first-component lemma; unfolds `retainedPassiveTargetEdgePairShearAt` only
after the relevant component goals are isolated; and closes the additive
cancellations componentwise.

## Nonclaims

No determinant-one theorem is included in this card unless the proof factors
the map into determinant-one shears or computes the determinant directly.  No
normalizer for `A1passive`, `A3passive`, `Ctop`, `F3`, the full formal
Jacobian, measure transport, normal crossings, pole order, or RLCT is claimed
here.
