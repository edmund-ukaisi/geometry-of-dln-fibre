# Statement Card - A2 product-family suffix-field construction

Date: 2026-06-25.

## Claim

The finite suffix-state algebra needed for a concrete p.13 product family has
been reduced to checked one-step field identities and a global suffix-iteration
theorem for chains with at least two edges.  The edge shapes from the
pen-and-paper construction create the intended suffix fields:

```text
[I, 0; -F3, C]                    creates F3 and starts D with C;
[I, 0; 0, C]                      preserves F3 and multiplies D by C;
[Ctop, -Ctop F2; 0, C0]           creates B = -F2 and Ctop;
[Ctop, -Ctop F2; -F3 Ctop, ...]   handles the N = 1 combined edge.
```

Separately, the fixed-base `F2/F3` square-sum is now exposed as exactly the
square-sum of the suffix-state fields `-S.B` and `lowerLeftBlock S.L`.

For a chain with at least two edges, if the transformed right endpoint is
`[I, 0; -F3, C_last]`, every middle transformed edge is `[I, 0; 0, C_p]`, and
the transformed left endpoint is `[Ctop, -Ctop F2; 0, C_0]`, the final suffix
state has

```text
B = -F2,
Ctop = Ctop,
D = residualProduct E last 0,
L = [I, 0; F3, I].
```

## Lean Artifacts

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

## Inputs Kept Explicit

- the transformed edge has the displayed block shape;
- previous suffix fields such as `S.Ctop = 1`, `S.D = Dprev`, and
  `S.L = fromBlocks 1 0 F3 1`;
- `IsUnit Ctop.det` exactly where inverse cancellation is used;
- residual factors are supplied edge-by-edge through the transformed Schur
  residual API, not by an arbitrary final `D`;
- the global theorem assumes transformed-edge block shapes; it does not build
  the original fixed-base edge family that realizes them.

## Nonclaims

No fixed-base continuous edge family `CedgeProd` is constructed.  No source
coverage, analytic product chart, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```
