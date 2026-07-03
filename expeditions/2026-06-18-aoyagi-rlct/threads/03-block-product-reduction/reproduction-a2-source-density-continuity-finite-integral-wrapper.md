# A2 source-density continuity finite-integral wrapper

Date: 2026-07-03.

## Calculation

The previous density package proves, for the concrete endpoint source chart,
that the two upper-density constants needed by the coordinate-source
finite-integral handoff can be chosen internally:

```text
exists CJ CS,
  CJ < top and CS < top,
  forall eventually z in nhds z0, jacobianDensity z <= CJ,
  forall eventually z in nhds z0, sourceDensity z <= CS.
```

The assumptions for the source side are exactly:

```text
ContinuousAt sourceDensity z0,
sourceDensity z0 < top,
```

where

```text
sourceDensity z = sourceImageDensity (sourceChart z).
```

The finite-integral handoff already consumes the two eventual bounds.  The
next wrapper simply:

1. applies the density package to obtain `CJ`, `CS`, and the two eventual
   upper bounds;
2. passes those hidden witnesses into the existing eventual-density
   coordinate-source finite-integral theorem;
3. returns the same passive local set, passive self-restriction, following
   patch, source neighborhood `V`, source-chart support facts, positivity
   a.e. conclusion, and finite negative-power integral conclusion.

No new measure comparison is proved in this wrapper.  The work is only the
composition of the density-bound selector with the already proved
same-shrink finite-integral theorem.

## Lean Target

The wrapper theorem is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceDensity_continuousAt_lt_top
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

It uses:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_finite_eventually_jacobianDensity_sourceDensity_bounds_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_sourceDensity_continuousAt_lt_top
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_eventually_density_bounds
```

## Boundary

This proves the finite-integral endpoint only under explicit local
source-density continuity and finite base value.  It does not construct
`sourceImageDensity`, prove source-density continuity, or prove the finite
base-value hypothesis.

It also proves no determinant-Haar/raw-Haar transport, original-prior
transport, normal crossings, pole order, or RLCT extraction.
