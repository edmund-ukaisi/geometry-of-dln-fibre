# Statement Card - A2 p.13 product-step inverse-density finite-integral handoff

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`

## Claim

The local p.13 finite-integral handoff can be specialized from an arbitrary
positive continuous density factor to the concrete chart-side inverse
product-step Jacobian density along the left-endpoint regular-coordinate tuple.

## Lean Names

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase
```

## Inputs

- The fixed paper chain `V`, edge family `Bv`, and complement `U0`.
- A source-data package for the p.13 regular-coordinate finite-side theorem.
- Explicit self-base hypotheses:
  `ContinuousAt CedgeBase x0` and
  `CedgeBase x0 = fun p => LinearMap.toContinuousLinearMap (reverseEdge V Bv p)`.
- The same loss lower bound, residual-source positivity/integrability, and
  signed-box residual-source hypotheses required by the existing abstract
  finite-integral handoffs.

## Method

The concrete density is

```text
productReductionStepRawOrderInverseJacobianDensity
  (paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase xu).
```

The previous p.13 tuple theorem supplies continuity and positivity at
`(x0,0)`, so the existing continuous-density finite-integral theorem applies.
The signed-box version first obtains the residual-source hypotheses from the
existing weighted signed-box constructor and then delegates to the concrete
density theorem.

## Not Proved

No product chart, source coverage, source/prior transport, product-step
pushforward identity, signed-box density identification, normal crossings, pole
order, or RLCT theorem is proved here.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Passed on 2026-06-26.
