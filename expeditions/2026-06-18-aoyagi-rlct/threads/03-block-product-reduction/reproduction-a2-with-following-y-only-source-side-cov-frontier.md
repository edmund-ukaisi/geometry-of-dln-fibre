# Reproduction - A2 with-following Y-only source-side COV frontier

Date: 2026-07-06.

Status: pen-and-paper frontier reproduction after the with-following
coordinate-count gate. This note fixes the source-side density convention for
the endpoint topology-tuple map. It is not a Lean theorem and proves no Haar
transport.

## Source Boundary

Aoyagi Lemma 2, PDF pp. 10-11, gives the one-step Schur substitution

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2,
```

with inverse formulas for `A2`, `A3`, and `A4`. Aoyagi Theorem 3, PDF
pp. 11-13, iterates this substitution and displays the final p.13 reduced
block

```text
[ C1 - Er,  -F2
  -F3,       prod_s C^(s) - F3 F2 ].
```

These pages justify the block-coordinate algebra used in the Lean endpoint
topology-tuple map. They do not state a measure pushforward theorem,
determinant-chart Haar transport, raw-Haar transport, source-image coverage,
or a local change-of-variables theorem.

## Coordinate Map Under Discussion

After the coordinate-count gate, the full-dimensional source is

```text
Theta+ = Case2PassiveThetaWithFollowingFactor.
```

Its fields are:

```text
passive fields: A1passive, F2, A3passive, Ctop, F3,
selected-entry center: yNext,
following factor: followingFactor.
```

The endpoint topology-tuple map is

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z.
```

Field by field, this map sends:

```text
passive fields       -> the same retained-passive endpoint fields,
followingFactor      -> active C 0, after eNext : tau ~= k1,
yNext                -> active C 1, through the selected-entry chart,
Ctop                 -> the top retained block.
```

Thus the only nonlinear endpoint-coordinate piece in `Y` is the
selected-entry chart on the active `C 1` block. The following factor is an
independent linear coordinate block; it must not be confused with Aoyagi's
original untransformed following matrix before the endpoint normalization.

## Reference Measure Convention

Lean names the unweighted coordinate-product source as

```text
case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
```

and the selected-entry source density as

```text
case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity z
  = ofReal(sourceDensity pivotNext z.1.yNext).
```

The named with-following reference source measure is already the unweighted
source with this selected-entry density:

```text
referenceSource =
  unweightedSource.withDensity selectedEntrySourceDensity.
```

Therefore the correct `Y`-only source-side statement has two equivalent
readings:

```text
Measure.map Y ((unweightedSource.withDensity selectedEntrySourceDensity).restrict V)
  = endpointReferenceImage(V),
```

or, by definition of `referenceSource`,

```text
Measure.map Y (referenceSource.restrict V)
  = endpointReferenceImage(V).
```

This endpoint reference image is an actual image measure. It is not
determinant-chart Haar measure and it is not raw-order Haar measure.

## Pen-And-Paper Jacobian Check

Relative to unweighted coordinates on `Theta+`, the differential of `Y` is
block triangular after finite coordinate reindexing:

```text
D Y =
  [ I_passive       *              *
    0               D chart_yNext  *
    0               0              I_following ].
```

The passive blocks and following-factor block are identity or finite
coordinate reindexing blocks in the normalized endpoint coordinates, so their
absolute determinant contribution is a positive constant, normalized to `1`
in the current Lean coordinate-product convention. The selected-entry block
is the known nonzero-pivot chart

```text
yNext |-> chartMap pivotNext yNext,
```

whose forward density is exactly

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext yNext.
```

Hence the source-side forward density for `Y` is the selected-entry density,
with no retained-passive raw-order determinant factor. The raw-order factor

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
```

enters only after composing `Y` with

```text
topologyTupleEdgeRawOrder.
```

This separation is load-bearing. Folding the retained-passive raw-order factor
into the `Y`-only COV double-counts the raw-order step.

## Existing Lean State

The following with-following source-image facts are already in Lean:

```text
exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_eq_p13SourceEdgeFamilySet_inter_readback_preimage

exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_rankEq_eq_p13SourceEdgeFamilySet_inter_readback_preimage_inter_sourceRankStratum
```

They provide a same-shrink image equality

```text
sourceChart '' V = p13SourceSet cap readback^{-1} V
```

and a rank-refined version. They are image theorems, not measure transport.

The endpoint-reference file already records the definition-level source-side
pushforward:

```text
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_unweighted_withDensity_selectedEntrySourceDensity_restrict_eq_endpointReferenceImageMeasure
```

This is the `Y`-only source convention above. It identifies the endpoint
reference image as an actual pushforward of the selected-entry weighted source
measure. It does not identify that image with determinant Haar.

Downstream formal-product/source-image contract theorems also exist, but the
strongest equality-based one still assumes the unsupported raw pushforward

```text
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

That equality should not be introduced as a theorem unless the local raw-image
coverage and Jacobian/Haar comparison have actually been proved.

## Current Frontier

There are now two honest source-moving routes.  After interruption
reorientation, Route A is not the next Lean target: it is already represented
in the current Lean tree.

### Route A: Set-Level Raw Endpoint-Patch Containment - Landed

Use the existing raw-image handoff, which can turn endpoint-patch domination
into raw-patch domination, but first prove the geometric containment it
requires on the same shrink:

```text
let P := rawSourceSet cap rawChart^{-1} chartPiece

rawDetChart cap rawOrderOnEndpoint^{-1} P
  subset activeWriteback '' (activeChart '' (V cap sourceCylinder)).
```

The chart piece should be supplied by the same-shrink with-following image
data:

```text
chartPiece subset p13SourceSet,
chartPiece subset readback^{-1} V.
```

This route does not prove exact raw-Haar pushforward.  It supplies the set
containment needed by the already-landed domination handoff.

Reorientation check, 2026-07-06: the containment route is already present in
Lean.  The generic set theorem is

```text
endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
```

and the with-following downstream wrappers include:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower

exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_continuousAt_priorDensity_comp_sourceChart_upper

exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_p13SourceSet_readback_preimage_continuousAt_priorDensity_comp_sourceChart_upper

exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
```

Thus a new theorem duplicating the endpoint/raw patch containment would be
wasteful.

### Route B: Direct Local COV For `Y`, Then Raw-Order Composition

Formalize the elementary finite-dimensional COV for `Y` on a local shrink:

```text
Measure.map Y ((unweightedSource.withDensity selectedEntrySourceDensity).restrict V)
  = endpointReferenceImage(V),
```

then compose with the already-formalized retained-passive raw-order COV. This
route still targets actual local images such as `Y '' V` or `rawMap '' V`,
not the full determinant chart or full raw source chart unless a separate
coverage theorem is proved.

## Controller Decision

Before any new Lean measure theorem, use the `Y`-only convention above as the
pen-and-paper gate:

1. `referenceSource` already contains the selected-entry density.
2. `endpointReferenceImage` is a pushforward image measure, not Haar.
3. The retained-passive raw-order determinant is a later factor.
4. Same-shrink image equality and the raw/endpoint patch-containment route are
   already available in Lean.

The smallest Lean-facing next theorem should therefore not duplicate Route A.
The live local-integrability frontier is to expose the natural patch

```text
p13SourceSet cap readback^{-1} V
```

as an actual local/open neighborhood when possible, or to record the exact
weakest open-neighborhood support hypotheses needed.  Separately, any future
source/product-coordinate COV should keep the `Y`-only image measure separate
from determinant/raw Haar transport.

The strongest currently proved with-following original-prior theorem is

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_continuousAt_priorDensity_comp_sourceChart_upper
```

It returns an open theta-neighborhood `V`, proves

```text
sourceChart '' V = p13SourceSet cap readback^{-1} V,
```

proves measurability of that natural patch, and proves finite integral of the
with-following readback product-residual negative power against the original
edge-family prior restricted to the whole natural patch.

The actual remaining gates, in order, are:

1. **Open-patch/local-neighborhood packaging.**  The natural patch is
   measurable and locally image-equal, but not yet exposed as an edge-family
   open neighborhood.  This is not a bare wrapper: the with-following readback
   contains the selected-entry inverse
   `preimageOfPivotNeZero`, which is continuous only at nonzero-pivot target
   values.  The honest next Lean layer is therefore a pivot-guarded local
   continuity theorem for
   `case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback`, followed
   by an open-patch wrapper.
2. **Actual-prior regularity input.**  The theorem assumes continuity, or an
   upper-bound consequence, for the supplied prior density pulled back along
   `sourceChart`.
3. **Loss-to-product-residual bridge.**  The integrand is the with-following
   readback product-residual square-sum, not yet the final `lossDLN` statement.
4. **Source-rank and atlas coverage.**  Rank-refined local equality exists, but
global source-rank/chart-family coverage belongs to the later atlas layer.

Recommended Lean shapes:

```text
continuousAt_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
  (hE : E in p13SourceSet)
  (hpivot : case2PassiveThetaPivotNonzero ... (readback E).1)

isOpen_p13SourceSet_inter_readback_preimage_of_subset_pivot
  (hVopen : IsOpen V)
  (hVpivot : forall z in V, case2PassiveThetaPivotNonzero ... z.1)
```

or, if the caller should not expose `hVpivot`, prove the weaker open set with
`V` replaced by `V cap {z | case2PassiveThetaPivotNonzero ... z.1}`.

## Nonclaims

No formal-product/source-image domination, determinant-chart Haar transport,
raw-Haar pushforward, raw-Haar normalization, original-prior transport,
source-rank coverage, global source-image coverage, normal-crossing theorem,
pole-order theorem, or RLCT extraction is proved here.

## Independent Checks

Xhigh scout `Meitner` independently checked the Aoyagi source boundary and
recommended separating the `Y`-only selected-entry density from the
retained-passive raw-order factor before Lean.

Xhigh scout `Epicurus` independently checked the with-following Lean frontier
and identified the same-shrink endpoint/raw patch containment as the missing
geometric hypothesis for the current raw-image domination route.
