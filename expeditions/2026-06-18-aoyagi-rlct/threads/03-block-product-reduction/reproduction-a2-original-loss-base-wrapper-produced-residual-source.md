# A2 original-loss base wrapper with produced residual-source hypotheses

## Object-level calculation

The base rank-cut original-loss bridge previously used the residual-source
bridge in a zero-locus-nullity form.  On the returned rank-cut source

```text
rankCutSource = (p13SourceSet cap readback^{-1} V) cap sourceStratum,
```

its continuation asked for

```text
muPrior.restrict rankCutSource {E | fixedResidual E = 0} = 0
```

and then obtained:

```text
forall^ae E with respect to muPrior.restrict rankCutSource,
  0 < fixedResidual E,

residualNegPowerIntegrableOn rankCutSource muPrior t.
```

The radius-free strict rank-cut residual-source theorem now produces these two
facts directly.  It first chooses selected-entry signed-box radii internally,
shrinks inside the source cylinder, produces the theta-side product-residual
positivity and local density bounds, and returns the residual positivity and
negative-power integrability package for the same rank-cut source.

Therefore the original-loss handoff no longer needs the zero-locus-nullity
continuation at the base wrapper.  The local-source loss socket consumes only:

```text
hpos_source : fixedResidual > 0 a.e. on muPrior.restrict rankCutSource,
hbase_source : residualNegPowerIntegrableOn rankCutSource muPrior t,
```

plus the already explicit local source data, adapted-product lower bound, and
regular-coordinate density bounds.

## Lean target

The new declaration should live in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorLossRankCutBridge.lean
```

and call:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

before feeding:

```text
exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
```

## Boundary

This removes only the residual zero-locus-nullity socket at the base
original-loss handoff.  It adds the honest strict residual-source inputs:
source-image density continuity and finite base value, a strict source-density
lower value `epsilon`, `epsilon != 0`, and a strict prior-density upper bound
`Kprior`.

It does not construct the source-image density, identify the statistical prior
with a source-chart image measure, prove determinant/raw Haar transport,
produce source data or adapted-product lower bounds, prove source-rank or atlas
coverage, construct normal crossings, compute pole order, or extract RLCT.
