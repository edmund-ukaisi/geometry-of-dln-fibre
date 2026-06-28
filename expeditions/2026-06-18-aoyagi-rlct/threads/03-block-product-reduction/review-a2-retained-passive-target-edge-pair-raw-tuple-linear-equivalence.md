# Review: A2 retained-passive target edge-pair raw-tuple linear equivalence

Reviewer: xhigh `Gauss the 2nd`.

## Verdict

PASS.  No blocking concerns found.

The new layer stays within the intended boundary:

- `retainedPassiveTargetRecoveredF2At_rawTupleInverse` proves only the first
  component of the formal `(F2,C)` inverse on `(w.2.1, w.2.2.2.1)`.  It does
  not claim raw `C` recovery for arbitrary tuples.
- `retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse` uses
  that first-component theorem only to identify the successor `F2`; the `C`
  component is recovered by direct raw shear cancellation.
- `retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt` asserts a
  `LinearEquiv`, but the checkpoint contains no determinant-one theorem or
  determinant-one overclaim.

## Proof-Shape Note

The inverse proofs are tightly coupled to the tuple field layout and exact
apply/readback lemmas, especially
`retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply`,
`rawEdgeTupleA1_replaceF2C`, and `rawEdgeTupleA3_replaceF2C`.  This is expected
for this checkpoint, not a mathematical concern.
