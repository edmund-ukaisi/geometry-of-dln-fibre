# A2 C-one rank-cut residual-source bridge

## Object-level calculation

The source-cylinder rank-cut residual-source bridge consumes

```text
rankCutSource subset sourceChart '' (W cap sourceCylinder).
```

The C-one wrapper replaces this with the pointwise support condition

```text
forall E in rankCutSource, cOneReadout E in signedBox.
```

The rank-cut image equality gives

```text
rankCutSource subset sourceChart '' V.
```

For `E = sourceChart z` with `z in V`, the local left inverse identifies the
C-one readout with the theta-side selected-entry coordinate:

```text
cOneReadout(sourceChart z) = z.1.yNext.
```

Therefore C-one signed-box support on `rankCutSource` gives

```text
rankCutSource subset sourceChart '' (V cap sourceCylinder).
```

Since `V subset W`, this widens to the support socket required by the
source-cylinder bridge:

```text
rankCutSource subset sourceChart '' (W cap sourceCylinder).
```

The rest is inherited unchanged from the source-cylinder bridge.

## Lean artifact

The new declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_cOneReadout_mem_signedBox_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

## Boundary

This proves only the C-one support wrapper over the source-cylinder bridge.
It does not prove C-one signed-box support for the rank-cut source, source-
density positivity, prior-density bounds, determinant/raw Haar transport,
source-prior transport, source-rank or atlas coverage, normal crossings, pole
order, or RLCT extraction.
