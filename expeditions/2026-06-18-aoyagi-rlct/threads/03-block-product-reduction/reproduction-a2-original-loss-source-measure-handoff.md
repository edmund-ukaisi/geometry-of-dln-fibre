# Reproduction - A2 original loss source-measure handoff

Date: 2026-06-25.

Status: reproduced; Lean implementation landed in
`DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure`.

## Source Anchor

This is measure plumbing for the self-base original-loss lower bound.  It does
not add a new Aoyagi calculation; it transports the already reproduced
source-filter lower bound to the restricted local source measure, matching the
existing local-measure discipline used for adapted p.13 bounds.

## Derivation

The previous source-filter theorem gives `c > 0` and

```text
eventually x in nhdsWithin x0 sourceStratum,
  (c / 2) * (regularSquareSum(x) + residualSquareSum(x))
    <= lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

The generic local-measure handoff says that if a property `P(x)` holds
eventually in `nhdsWithin x0 S`, and `S` is measurable, then there is an open
neighborhood `U` of `x0` such that `P(x)` holds almost everywhere for

```text
mu.restrict (U inter S).
```

Applying this with `S = sourceStratum` and `P(x)` equal to the original-loss
lower bound gives

```text
exists U open, x0 in U,
  ae x with respect to mu.restrict (U inter sourceStratum),
    (c / 2) * (regularSquareSum(x) + residualSquareSum(x))
      <= lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

The product-first version is the same handoff followed by the first-projection
quasi-measure-preserving fact for the product measure:

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

The asserted inequality still depends only on `z.1`; it is not a
fiber-uniform product-coordinate lower bound.

## Lean Implementation

The Lean implementation lives in a source-measure module importing
`EndpointLossComparison` and `LocalMeasureHandoff`, with names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
```

## Boundary

This is only an a.e. localization of the one-parameter source-filter bound. It
does not construct the product chart, identify a regular fiber variable,
prove signed-box source transport, prove density/Jacobian transport, produce
normal crossings, compute pole order, or extract an RLCT.
