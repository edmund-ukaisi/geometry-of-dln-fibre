# Review - A2 retained-passive edge-pair source-staged tuple assembly

Date: 2026-06-27.

Status: PASS.

## Scope

This review covers the hybrid whole-tuple retained-passive package in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, with the
matching reproduction and statement card:

- `reproduction-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`;
- `statement-card-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.

## Checks

Xhigh read-only reviewer `Dalton` checked that the raw tuple order is
`(A1passive, F2, A3passive, C, Ctop, F3)` and that
`edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt` keeps
`old.1`, `old.2.2.1`, and `old.2.2.2.2`, replacing only the `F2` and `C`
families by the all-edge source-staged normalized families.

The proof of
`edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
uses the old tuple equality for `A1passive`, passive `A3`, and `(Ctop,F3)`,
and the all-edge source-staged `(F2,C)` equality for `F2` and `C`.

The documentation states that only `(F2,C)` is source-staged and that the
other branches remain derivative-staged.  The nonclaim boundary is explicit.

## Verdict

PASS.  No mathematical or Lean fixes required.

## Nonclaims Preserved

This package is not a target-side `LinearEquiv`, not a determinant-one shear,
not an actual derivative determinant formula, not a measure transport theorem,
not normal crossings, not pole order, and not RLCT.
