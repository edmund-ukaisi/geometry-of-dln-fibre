# Reproduction - A2 original loss source-measure continuous-edge wrapper

Date: 2026-06-25.

Status: reproduced; Lean implementation landed in
`DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure`.

## Source Anchor

This is not a new Aoyagi calculation.  It is a convenience wrapper around the
original-loss source-measure handoff, using the already-proved fact that a
globally continuous fixed-base edge family has a measurable source-rank
stratum.

## Derivation

The existing source-measure theorem assumes

```text
MeasurableSet sourceStratum
```

and returns, after shrinking to an open source neighborhood `U`,

```text
ae x for mu.restrict (U inter sourceStratum),
  (c / 2) * (regularSquareSum(x) + residualSquareSum(x))
    <= lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

The source-rank measurability theorem says that if

```text
Continuous Cedge,
```

then

```text
MeasurableSet (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

The same global continuity also gives the `ContinuousAt Cedge x0` input needed
by the self-base source-filter lower bound.  Therefore the wrapper only
replaces the two inputs

```text
ContinuousAt Cedge x0
MeasurableSet sourceStratum
```

by a single global continuity hypothesis

```text
Continuous Cedge.
```

The product-first version is identical: use the same measurable source stratum
and apply the existing product first-projection handoff.

## Lean Implementation

The Lean implementation adds two wrappers to
`DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
```

## Boundary

This proves only measurability discharge for the restricted-source a.e.
handoff.  It does not prove source-rank openness, product chart construction,
signed-box pushforward, density/Jacobian transport, normal crossings, pole
order, or RLCT extraction.
