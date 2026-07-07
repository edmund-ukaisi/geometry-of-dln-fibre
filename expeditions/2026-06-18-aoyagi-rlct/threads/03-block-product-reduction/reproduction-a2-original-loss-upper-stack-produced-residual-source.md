# A2 original-loss upper stack with produced residual-source hypotheses

## Object-level calculation

The base produced residual-source wrapper returns a rank-cut source

```text
rankCutSource = (p13SourceSet cap readback^{-1} V) cap sourceStratum
```

and its continuation consumes `rawHaar`, source data, basis/Haar choices,
adapted-product lower bounds, and regular-coordinate density bounds.  It no
longer consumes

```text
muPrior.restrict rankCutSource {E | fixedResidual E = 0} = 0.
```

The upper original-loss wrappers above the base theorem are Lean-local
specializations:

```text
local source bounds
  -> adapted-product radius and constant
  -> pulled-back density bounds
  -> prior-density product-zero specialization
  -> finBasis endpoint specialization
  -> Euclidean volume regular-coordinate specialization
  -> source-data construction from rank equations.
```

Each step only changes the continuation arguments after the same returned
rank-cut source package.  Therefore the residual zero-locus-nullity argument
can be removed uniformly from every continuation in the upper stack, provided
each theorem carries the strict source-image-density and prior-density inputs
required by the base residual-source producer:

```text
sourceImageDensity,
ContinuousAt (sourceImageDensity o sourceChart) z0,
sourceImageDensity(sourceChart z0) < infinity,
epsilon < sourceImageDensity(sourceChart z0),
epsilon != 0,
priorDensity(sourceChart z0) < Kprior.
```

The adapted-lower, pulled-back-density, product-zero, finBasis, volume, and
rank-equation proofs are otherwise unchanged.  They continue to prove local
finite integrability by shrinking radii and building source data, then call
the lower produced-residual-source wrapper instead of the old zero-nullity
wrapper.

## Lean target

The parallel stack lives in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorLossProducedRankCutBridge.lean
```

The top theorem is:

```text
exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_rank_eq_of_source_base_of_continuousAt_pos_priorDensity_product_zero_finBasis_volume
```

The old zero-nullity stack remains available in
`RetainedPassiveCase2PassiveThetaOriginalPriorLossRankCutBridge.lean`.

## Boundary

This removes only the exposed residual zero-locus-nullity continuation from
the upper original-loss stack.  It does not construct the source-image
density, identify the statistical prior with a source-chart image measure,
prove determinant/raw Haar transport, prove fixed-base centering or the two
rank equations, prove product-zero density hypotheses, prove source-rank or
atlas coverage, construct normal crossings, compute pole order, or extract
RLCT.
