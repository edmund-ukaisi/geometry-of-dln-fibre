# Statement Card - A2 p.13 Original-prior Volume-source-reference Domination Finite Integral

## Claim

The p.13 original-prior finite-integral wrapper remains valid if the supplied
source reference pulls back to a finite scalar multiple of the coordinate
source measure, rather than exactly to that coordinate source measure.

The final chart-piece handler assumes:

```text
chartPiece measurable
chartPiece ⊆ sourceLocal
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ Kprior
AEMeasurable readback sourceRef
Measure.map readback sourceRef ≤ Csource • coordinateSourceMeasure.restrict W
Csource < infinity
(originalEdgeFamilyVolume b).restrict chartPiece ≤ D • sourceRef
D < infinity
```

and concludes the finite lower integral over

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Names

```text
readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_of_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_le
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceReference_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the formal p.13 restricted-volume-to-source-reference domination bridge;
- generic scalar composition of measure domination;
- the existing original-prior finite-integral theorem;
- finiteness of `cHaar : ENNReal`, `D`, and `Csource`.

## Proof Shape

1. Prove a generic handoff: if `μ ≤ Cμ • sourceRef` and
   `Measure.map readback sourceRef ≤ Csource • thetaRef`, then
   `Measure.map readback μ ≤ (Cμ * Csource) • thetaRef`.
2. Specialize this to `muP13`, where
   `Cμ = (cHaar : ENNReal) * D`.
3. In the finite-integral wrapper, set
   `Cformal := ((cHaar : ENNReal) * D) * Csource`.
4. Prove `Cformal < infinity` from `D < infinity` and `Csource < infinity`.
5. Apply the existing formal-readback finite-integral handler.

## Nonclaims

This theorem does not prove restricted-volume domination, identify a concrete
source reference, prove passive-theta source-image equality, source coverage,
chart-image equality, source-rank coverage, Haar scalar normalization, normal
crossings, pole order, RLCT extraction, or global original-prior integrability
beyond the supplied local chart piece.
