# Statement card - A2 canonical product-difference coefficient-field continuity

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-a2-canonical-product-difference-field-continuity.md`.

Review:
`review-a2-canonical-product-difference-field-continuity.md`.

## Target

Expose the canonical coefficient fields in the Aoyagi product-difference
entry-ideal boundary as continuous fixed-base local functions, and show that
the self-base fields are centered at zero.

## Expected Lean Artifacts

Expected declarations in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

```text
paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt

paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt

paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt
```

The explicit-chart theorem should assume a continuous reversed-edge family and
the recursive determinant-chart hypotheses at the base point.  The self-base
theorem should replace those chart hypotheses by the base equality
`Cedge x0 = reverseEdge B`.

Both should conclude continuity at `x0` of the concrete fields:

```text
S.Ctop - 1,
-S.B,
lowerLeftBlock S.L,
S.D.
```

and preserve the determinant-unit conclusion for `S.Ctop.det`.

The centered self-base theorem should additionally prove:

```text
(S x0).Ctop - 1 = 0
-(S x0).B = 0
lowerLeftBlock (S x0).L = 0
(S x0).D = 0
```

## Kill Conditions

- Do not state analytic regularity, only `ContinuousAt`.
- Do not assert source-rank or exact-rank openness.
- Do not infer chart coverage, analytic ideal transport, regular suspension,
  normal crossings, pole order, or RLCT.
- Do not repackage the product-difference ideal equality unless the
  continuity conclusion is present.
- Do not identify `S.D` with a raw untransformed product; only its centered
  basepoint value is proved here.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
```

The preferred `scripts/lb` wrapper is unavailable in this sandbox because the
environment rejects writes to the shared `~/.lake-shared` lock pool.  The
fallback checks used one Lean worker and the already-linked shared packages.
