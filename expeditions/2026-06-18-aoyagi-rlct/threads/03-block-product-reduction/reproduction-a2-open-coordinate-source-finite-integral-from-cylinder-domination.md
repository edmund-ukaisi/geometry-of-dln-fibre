# A2 open coordinate-source finite integral from cylinder domination

Date: 2026-07-03.

## Calculation

The previous coordinate-source finite-integral wrapper returns a following
patch and then asks for the continuation

```text
V subset {z | z.2 in followingPatch}.
```

To discharge that continuation by source-chart shrinking later, the returned
patch must be open.  The existing matrix-entry constructor already gives an
open finite following patch:

```text
exists_matrixEntryReferenceMeasure_finite_open_followingPatch_of_reindexed_det_isUnit
```

The finite-integral proof only used the following facts about the patch:

```text
MeasurableSet followingPatch,
matrixEntryReferenceMeasure followingPatch < infinity,
det unit on followingPatch,
inverse square-sum <= K on followingPatch.
```

The open constructor supplies all of these, plus

```text
IsOpen followingPatch.
```

Therefore the finite source-cylinder theorem and the dominated-target socket
can be replayed with the open patch witness, carrying the extra openness field
through the existential package.  The coordinate-source wrapper then reuses
the same domination calculation:

```text
referenceSource.restrict V <= Cpassive • localSourceMeasure

coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cpassive)) • localSourceMeasure
```

and applies the dominated-target socket to

```text
targetMeasure = coordinateSourceMeasure.restrict V,
C = CS * (CJ * Cpassive).
```

## Source-chart use

Once the open patch is in scope, the cylinder

```text
{z | z.2 in followingPatch}
```

is open by

```text
isOpen_case2PassiveThetaWithFollowingFactor_followingPatchCylinder.
```

A later source-chart theorem can call the existing local source-chart API with
the ambient open set intersected with this cylinder.  That later theorem is
the one that should prove the continuation

```text
V subset {z | z.2 in followingPatch}.
```

## Lean targets

The endpoint open-patch dominated-target socket is:

```text
exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_of_measure_le_smul_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
```

The concrete coordinate-source open-patch wrapper is:

```text
exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
```

The source-chart shrinking wrapper is:

```text
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse_subset_followingPatchCylinder
```

## Boundary

This strengthening still proves no passive local comparison measure
construction, no passive support theorem, no Jacobian-density upper bound, no
source-density upper bound, no source-chart shrinking theorem, no
determinant-Haar/raw-Haar transport, no original-prior transport, no normal
crossings, pole order, or RLCT extraction.
