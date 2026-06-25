# Review - A2 product-family suffix-field construction

Date: 2026-06-25.

## Verdict

Passed at the finite matrix-algebra scope now covered by the one-step lemmas
and the global suffix-iteration theorem.

## Checks

Pen-and-paper sign review found no sign or shape error.  The review checked
the suffix update definitions

```text
transformedEdge E p S = [1 S.B; 0 1] * E p
step.B = topLeft(M)^-1 * upperRight(M)
step.Ctop = S.Ctop * topLeft(M)
step.D = S.D * schurResidualBlock(M)
```

against the proposed edge shapes.  It confirmed:

- `[I, 0; -F3, C]` gives `lowerLeftBlock L = F3`;
- `[C, -C F2; 0, C0]` gives `B = -F2`, so the coordinate map reads
  `-B = F2`;
- the single-edge lower-left block must be `-F3 C`, with lower-right
  correction `C0 + F3 C F2`.

Lean review found no findings for:

```text
topLeftCorner_fromBlocks
upperRightBlock_fromBlocks
lowerLeftBlock_fromBlocks
lowerRightBlock_fromBlocks
ChartLocalSuffixState.step_finalF3_fromBlocks
ChartLocalSuffixState.step_middleResidualFactor_fromBlocks
ChartLocalSuffixState.step_leftEndpointF2Ctop_fromBlocks
ChartLocalSuffixState.step_singleEdgeF2F3Ctop_fromBlocks
ChartLocalSuffixState.suffixState_tail_fields_of_productFamily_transformedEdges
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one
ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_succSucc
paperEndpointFixedBaseRegularBlockF2F3SquareSum_eq_suffixState_B_lowerLeftBlock
```

The reviewer specifically checked names against content, sign consistency, and
absence of analytic/RLCT overclaim.

## Residual Risk

The fixed-base continuous-linear-map wrapper is not yet proved.  The finite
theorems require transformed-edge block-shape hypotheses; a later constructor
still has to show the actual supplied `CedgeProd` produces those transformed
edges and satisfies the needed continuity/source conditions.
