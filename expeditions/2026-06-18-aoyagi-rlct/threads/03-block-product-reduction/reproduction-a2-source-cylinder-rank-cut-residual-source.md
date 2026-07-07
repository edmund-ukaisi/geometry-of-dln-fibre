# A2 source-cylinder rank-cut residual-source bridge

## Object-level calculation

The active-containment rank-cut residual-source bridge still asked the caller
for the endpoint-patch containment

```text
endpointPatch subset activeWriteback '' (activeChart '' (W cap sourceCylinder)).
```

For the source-cylinder route we instead expose the chart-piece support

```text
rankCutSource subset sourceChart '' (W cap sourceCylinder),
```

where

```text
rankCutSource = (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

This is the natural support hypothesis consumed by the existing
source-cylinder prior readback package.  That package already proves the
raw/source endpoint containment internally from source-cylinder support,
raw-chart injectivity, raw-order injectivity, raw/source compatibility, and
the active selected-entry writeback factorization.

The rank-cut residual handoff still works on the inner shrink `V`.  The
rank-cut image equality gives

```text
rankCutSource subset sourceChart '' V.
```

Since `V subset W subset G`, the generic support-sharpening lemma moves the
readback domination from the ambient source-neighborhood target

```text
coordinateSourceMeasure.restrict G
```

to the inner rank-cut target

```text
coordinateSourceMeasure.restrict V.
```

The residual-source handoff then uses this same-shrink domination together
with theta-side product-residual positivity on `V`.

## Lean artifact

The new declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

## Boundary

This proves only the source-cylinder support wrapper.  It does not prove that
the rank-cut source lies in the source cylinder, does not prove the C-one
signed-box condition, and does not prove source-density positivity, prior
density bounds, determinant/raw Haar transport, source-prior transport,
source-rank or atlas coverage, normal crossings, pole order, or RLCT
extraction.
