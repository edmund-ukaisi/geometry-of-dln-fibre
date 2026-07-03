# A2 With-Following Readback Product Residual, Original Prior, Source-Cylinder Active Containment

Date: 2026-07-03.

## Target

Discharge the active endpoint-image containment used by the with-following
original-prior product-residual wrapper, under the source support that the
active reference measure actually has.

The strengthened chart-piece hypothesis is

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder),
sourceCylinder = {z | z.1.yNext ∈ signedBox Rres}.
```

The target endpoint containment is

```text
rawDetChart ∩ rawOrderOnEndpoint ⁻¹'
    (rawSourceSet ∩ rawChart ⁻¹' chartPiece)
  ⊆ activeWriteback '' (activeChart '' (V ∩ sourceCylinder)).
```

## Pen-and-paper calculation

Let

```text
P = rawSourceSet ∩ rawChart ⁻¹' chartPiece.
```

Take

```text
y ∈ rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P.
```

Then

```text
rawOrderOnEndpoint y ∈ rawSourceSet
rawChart(rawOrderOnEndpoint y) ∈ chartPiece.
```

The source-cylinder chart-piece hypothesis gives a witness

```text
z ∈ V ∩ sourceCylinder
sourceChart z = rawChart(rawOrderOnEndpoint y).
```

The localized raw/source compatibility theorem gives, for this `z ∈ V`,

```text
Y z ∈ rawDetChart
rawOrderOnEndpoint(Y z) ∈ rawSourceSet
rawChart(rawOrderOnEndpoint(Y z)) = sourceChart z.
```

Therefore

```text
rawChart(rawOrderOnEndpoint y)
  = rawChart(rawOrderOnEndpoint(Y z)).
```

The p.13 raw-chart homeomorphism gives injectivity of `rawChart` on
`rawSourceSet`, hence

```text
rawOrderOnEndpoint y = rawOrderOnEndpoint(Y z).
```

The raw-order inverse theorem gives injectivity of `rawOrderOnEndpoint` on
`rawDetChart`, hence

```text
y = Y z.
```

Finally, the active endpoint factorization says

```text
Y z = activeWriteback(activeChart z).
```

Since `z ∈ V ∩ sourceCylinder`, this proves

```text
y ∈ activeWriteback '' (activeChart '' (V ∩ sourceCylinder)).
```

## Lean Route

The pure set-algebra lemma is:

```text
endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder
```

The concrete with-following finite-integral wrapper is:

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_priorDensity_upper
```

The concrete wrapper first calls the existing raw/source compatibility shrink,
then calls the active endpoint-domination original-prior finite-integral
wrapper.  It constructs the endpoint containment by combining:

```text
topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
```

For Lean performance, the proof extracts only the determinant-chart fact from
the raw/source shrink payload, then derives raw-source membership directly by
`mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet`
and derives the p.13 source-chart equality directly from
`paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData`.

## Boundary

The source-cylinder support is necessary for this theorem shape.  The active
reference image is supported on

```text
activeChart '' (V ∩ sourceCylinder),
```

not on `activeChart '' V`.  Thus the weaker hypothesis

```text
chartPiece ⊆ sourceChart '' V
```

does not give a source-cylinder witness and is not enough unless another
theorem supplies `V ⊆ sourceCylinder` or an equivalent chart-piece support
condition.

This theorem still keeps prior-density upper boundedness and readback
residual pullback measurability explicit.  It does not prove source-image
coverage, normal crossings, pole order, or RLCT extraction.

## Verification

Passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake build DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|admit|axiom|#exit|native_decide|TODO|FIXME" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Direct axiom probe reports:

```text
endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder:
  no axioms

exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_priorDensity_upper:
  [propext, Classical.choice, Quot.sound]
```
