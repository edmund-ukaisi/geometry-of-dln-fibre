# Statement Card - A2 retained-passive target edge-pair linear map

## Lean Names

Expected in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredF2LinearMapAt
retainedPassiveTargetRecoveredF2LinearMapAt_apply
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt
retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply
retainedPassiveTargetEdgePairShearLinearMapAt
retainedPassiveTargetEdgePairShearLinearMapAt_apply
```

## Mathematical Content

For a fixed retained-passive tuple `z`, the target-side backward recovered
`F2` family is linear in an arbitrary target raw tuple `w`.  The induced
successor family is also linear.  Consequently the all-edge target-side
normalized `(F2,C)` pair

```text
w |-> retainedPassiveTargetEdgePairShearAt z w
```

is packaged as a linear map from the raw tuple space to the separated `(F2,C)`
family space.

## Dependencies

```text
retainedPassiveTargetRecoveredF2At
retainedPassiveTargetRecoveredSuccessorF2At
retainedPassiveTargetEdgePairShearAt
rawEdgeTupleA1
rawEdgeTupleA3
LinearEquiv.cast
```

## Non-Claims

This does not construct a target-side `LinearEquiv`, a whole raw-tuple
normalizer, determinant-one or absolute-determinant-one facts, the raw
coordinate Jacobian determinant equality, source-prior transport, normal
crossings, pole order, RLCT, or analytic extraction.

## Status

Sorry-free and reviewed.  Xhigh review by `Lovelace the 2nd` passed in
`review-a2-retained-passive-target-edge-pair-linear-map.md`.
