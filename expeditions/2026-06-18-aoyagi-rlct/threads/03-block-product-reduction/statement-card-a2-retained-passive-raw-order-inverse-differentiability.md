# Statement Card - A2 Retained-Passive Raw-Order Inverse Differentiability

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
differentiableAt_matrix_submatrix
differentiableAt_matrix_fromBlocks
differentiableAt_topLeftCorner
differentiableAt_upperRightBlock
differentiableAt_lowerLeftBlock
differentiableAt_lowerRightBlock
differentiableAt_schurResidualBlock
differentiableAt_chartLocalSuffixState_step_fields
differentiableAt_chartLocalSuffixState_suffixState_fields
differentiableAt_sourceReadbackSuffixState_fields
differentiableAt_sourceReadbackTransformedEdge
differentiableAt_rawEdgeTupleA1
differentiableAt_rawEdgeTupleA3
differentiableAt_edgeFamilyOfRawOrderTuple
differentiableAt_topologyTuple_sourceReadback
differentiableAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-inverse-differentiability.md
```

## Verification

Review:

```text
review-a2-retained-passive-raw-order-inverse-differentiability.md
```

passed by xhigh read-only explorer `Nash the 4th`, with a low
dependency-hygiene caveat about reusing generic matrix-calculus helpers from
`ProductReductionStepDerivative`.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
```

## Claim

The raw-order readback inverse

```text
topologyTupleEdgeRawOrderInverse
```

is differentiable at every point of

```text
topologyTupleRawOrderSourceRecursiveDetChartSet.
```

## Role

This provides the inverse differentiability side needed before proving a
formal tangent equivalence and determinant unitness for the retained-passive
raw-order chart.

## Nonclaims

No derivative formula, tangent equivalence, determinant unit theorem,
determinant formula, density, measure transport, source-rank coverage, normal
crossing, pole order, or RLCT statement is part of this slice.
