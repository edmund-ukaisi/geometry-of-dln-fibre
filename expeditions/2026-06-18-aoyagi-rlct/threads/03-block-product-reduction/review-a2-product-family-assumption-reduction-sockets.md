# Review - A2 product-family assumption-reduction sockets

Date: 2026-06-25.

Reviewer: xhigh Gauss the 5th.

## Scope

Reviewed the Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseRegularBlockF2F3SquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source
```

## Findings

No fidelity issues found.

The `F2/F3` smallness definition matches the p.13 regular sub-square-sum: it
uses only the two regular tags for `F2` and `F3`, excluding `Ctop - 1` and
the residual `D` block.

The cleaned-to-literal direction is correct for the socket:

```text
cleaned <= 2 * literal.
```

It is proved pointwise from `F2/F3 <= 1` and then lifted under the same source
filter and regular-ball guard.

The shape theorem uses only the two component identities

```text
regularBlock(CedgeProd(x,u)) = u,
residualBlock(CedgeProd(x,u)) = residualBlock(CedgeBase x),
```

plus the existing cleaned product-difference square-sum split.  It does not
claim a chart or analytic-coordinate construction.

The composed wrapper preserves the previous socket boundary: it assumes the
square-sum shape, derives only the cleaned-to-literal comparison from
`F2/F3` smallness, and keeps the product-reduction certificate and triangular
multiplier bound explicit.  It also keeps `0 < Rmax`, so the old empty-ball
issue is not reintroduced.

## Verdict

Passed.

Follow-up review by xhigh Gibbs the 5th also passed the fully composed wrapper

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source
```

with no findings.  The reviewer checked that `hshape` is replaced by
`hregular`/`hresidual`, the cleaned-to-literal hypothesis is replaced by
`F2/F3` smallness, and `0 < Rmax`, product-reduction certificates, and the
triangular multiplier bound remain explicit.  The theorem remains only an
eventual finite square-sum lower bound.

Residual gaps remain as intended: construction of `CedgeProd`, source
coverage/nonvacuity, density/Jacobian transport, normal crossings, pole order,
and RLCT extraction are out of scope.  The final wrapper still takes
square-sum `hshape`; the newer fully composed wrapper removes that input when
the component identities are available.

Verified by reviewer with:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

## Radius-Derived Smallness Review

Reviewer: xhigh Peirce the 5th.

Scope:

```text
aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_add_le_coordinateSquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source
```

Findings: no mathematical overclaim in the `F2/F3` smallness derivation.  The
proof relies on literal coordinate equality to `u`, Euclidean ball membership,
and `Rmax <= 1`; it introduces no hidden norm-comparison assumption.  The
`F2/F3` index split matches the local regular-coordinate encoding.

Two low hygiene findings were fixed in notes/docstrings: `0 < Rmax` is not
used by the finite smallness proof and is currently carried by the composed
socket as a positive-radius interface/nonvacuity condition; the intermediate
radius-derived eventual theorem is vacuous on an empty ball, while the final
`regularRadius_le_one` wrapper includes `0 < Rmax`.

Verified by reviewer with:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
git diff --check -- lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```
