# A2 unit source-image density finite-integral wrapper

Date: 2026-07-03.

## Question

The coordinate-source endpoint is now proved under:

```text
ContinuousAt sourceDensity z0
sourceDensity z0 < top
```

where:

```text
sourceDensity z = sourceImageDensity (sourceChart z).
```

For the chart-produced source-image base measure itself, the source-image
density is the unit density:

```text
sourceImageDensity E = 1.
```

This is not an original-prior or external-source statement.  It only selects
the unweighted chart-produced source-image measure already present in the
coordinate-source construction.

## Calculation

With `sourceImageDensity E = 1`, the composed source density is constant:

```text
sourceDensity z = 1.
```

Therefore:

```text
ContinuousAt sourceDensity z0
```

by continuity of constant functions, and:

```text
sourceDensity z0 < top
```

because `1 < top` in `ENNReal`.

The already proved continuity wrapper can then be applied with this fixed
unit source-image density.  The Jacobian bound is still obtained internally
from the determinant-sector endpoint theorem, and the source-density bound is
now the trivial local bound by `1`.

## Lean Target

Add a theorem in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

specializing:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceDensity_continuousAt_lt_top
```

to:

```text
sourceImageDensity = fun _ => 1.
```

## Boundary

This removes the source-density continuity and finite-base-value assumptions
only for the unweighted chart-produced source-image measure.  It does not
construct or identify an original DLN prior, prove source-image coverage,
prove determinant-Haar/raw-Haar transport, prove source-rank coverage, prove
normal crossings, compute pole order, or extract the RLCT.
