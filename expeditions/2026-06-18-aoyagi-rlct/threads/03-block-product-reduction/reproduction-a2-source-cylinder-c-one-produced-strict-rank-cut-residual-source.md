# A2 source-cylinder and C-one produced/strict rank-cut residual-source wrappers

## Object-level calculation

The base source-cylinder rank-cut bridge asks for three terminal analytic
inputs on the returned outer shrink `W` and inner rank-cut source:

```text
rankCutSource subset sourceChart '' (W cap sourceCylinder),
forall^ae z with respect to baseJ.restrict W, epsilon <= sourceDensity z,
forall^ae E with respect to originalVolume.restrict rankCutSource,
  density E <= Kprior,
forall^ae z with respect to coordinateSourceMeasure.restrict V,
  0 < productResidual z.
```

The produced-product source-cylinder wrapper removes the last input.  It first
uses the coordinate-source product-residual finite-integral theorem to produce
an open positivity shrink `Vpos` around `z0`, then runs the source-cylinder
bridge inside `Vpos`.  The final rank-cut shrink satisfies

```text
V subset W subset Vpos,
```

so positivity transfers from `coordinateSourceMeasure.restrict Vpos` to
`coordinateSourceMeasure.restrict V` by monotonicity of restricted measures
and absolute continuity.

The strict-density source-cylinder wrapper removes the source-density lower,
prior-density upper, and `epsilon != infinity` terminal inputs.  It fixes
`epsilon` and `Kprior` before choosing the shrink.  Continuity and the strict
basepoint inequalities give a neighborhood `Gbounds` on which

```text
epsilon <= sourceImageDensity(sourceChart z),
density(sourceChart z) <= Kprior.
```

The wrapper applies the produced-product source-cylinder theorem inside
`G cap Gbounds`.  Since the returned `W` lies in `Gbounds`, the source-density
lower bound holds a.e. on `baseJ.restrict W`.  Since

```text
rankCutSource subset sourceChart '' V
```

and `V subset W subset Gbounds`, the prior-density upper bound holds
pointwise on `rankCutSource`, hence a.e. for
`originalVolume.restrict rankCutSource`.  The missing
`epsilon != infinity` input is derived from

```text
epsilon < sourceImageDensity(sourceChart z0) < infinity.
```

The C-one produced-product and C-one strict-density wrappers replace
source-cylinder support by the pointwise condition

```text
forall E in rankCutSource, cOneReadout E in signedBox.
```

The rank-cut image equality gives `rankCutSource subset sourceChart '' V`.
The local left inverse identifies the C-one readout of `sourceChart z` with
the theta-side selected-entry coordinate, so C-one support yields

```text
rankCutSource subset sourceChart '' (V cap sourceCylinder).
```

Finally `V subset W` widens this to the source-cylinder socket on `W`.

## Lean artifacts

The produced-product source-cylinder declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
```

The produced-product C-one declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_cOneReadout_mem_signedBox_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
```

The strict-density source-cylinder declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_subset_sourceChart_image_inter_sourceCylinder_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

The strict-density C-one declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_cOneReadout_mem_signedBox_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

All four declarations are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

## Boundary

These are still support and measure-domination wrappers.  They do not prove
source-cylinder support, the C-one signed-box condition, positivity of the
source density at the basepoint, prior-density strict upper bounds at the
basepoint, determinant/raw Haar transport, source-prior transport,
source-rank or atlas coverage, normal crossings, pole order, or RLCT
extraction.
