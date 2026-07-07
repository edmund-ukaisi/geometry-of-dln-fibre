# A2 rank-cut residual-source readback nullity wrapper

## Source and role

This is elementary measure/source-image bookkeeping for the A2 rank-cut
residual frontier.  It is not a new cited theorem from Aoyagi.  It specializes
the readback zero-locus handoff to the rank-cut p.13/readback source and then
feeds the resulting nullity into the existing residual-source-hypotheses
wrapper.

## Reproduction

Let

```text
rankCutSource := (p13SourceSet ∩ readback^{-1}(V)) ∩ sourceStratum.
```

Let `fixedResidual E` be the fixed-base p.13 residual square-sum and
`productResidual z` the with-following theta-side product-residual square-sum.

Assume on the restricted original prior over `rankCutSource`:

1. `readback` is a.e.-measurable.
2. `Measure.map readback` of the restricted prior is dominated by
   `Cread • coordinateSourceMeasure.restrict V`.
3. `productResidual` is positive a.e. for
   `coordinateSourceMeasure.restrict V`.

The zero-locus implication needed by the generic readback lemma follows from
the local source-image data:

```text
rankCutSource ⊆ sourceChart '' V,
readback(sourceChart z) = z  for z ∈ V,
fixedResidual(sourceChart z) = productResidual z  for z ∈ V.
```

The last equality is the existing determinant-chart residual comparison,
using the determinant-sector hypothesis on the returned shrink.

Then the generic readback handoff gives

```text
(μprior.restrict rankCutSource) {E | fixedResidual E = 0} = 0.
```

The existing residual-source wrapper converts this nullity plus the existing
negative-power residual integrability into:

```text
∀ᵐ E ∂ μprior.restrict rankCutSource, 0 < fixedResidual E
```

and `residualNegPowerIntegrableOn` on the same rank-cut source.

## Kill conditions

- Reading this as proving the concrete original-prior readback domination.
- Reading this as proving same-shrink domination against
  `coordinateSourceMeasure.restrict V`.
- Reading this as proving theta-side residual positivity.
- Reading this as proving source-rank coverage, determinant/raw-Haar
  transport, normal crossings, pole order, or RLCT extraction.

## Lean targets

```text
originalEdgeFamilyPrior_rankCut_residual_zero_set_eq_zero_of_readback_map_le_smul_productResidual_pos_ae

zero_set_ae_le_readback_preimage_zero_set_of_source_subset_image

exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_readback_map_le_smul_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean`.

## Verification

Focused `lake env lean` for the touched file passed.  Focused module builds
for the touched residual rank-cut bridge and downstream local-loss rank-cut
bridge passed.  `scripts/sorries`, `git diff --check`, touched Lean-file
marker scan, and direct axiom probes passed.  All three declarations report
only `[propext, Classical.choice, Quot.sound]`.
