# Statement Card - A2 p.13 Original-prior Volume Source-image Density Finite Integral

## Claim

The p.13 original-prior finite-integral wrapper can consume a structured
source-image density comparison.  For the locally produced passive-theta chart
`V`, set

```text
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The final chart-piece handler assumes

```text
chartPiece measurable
chartPiece ⊆ U ∩ sourceStratum
chartPiece ⊆ sourceChart '' V
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂ originalVolume.restrict chartPiece, density E <= Kprior
originalVolume.restrict chartPiece =
  (sourceRef.withDensity volumeDensity).restrict chartPiece
∀ᵐ E ∂ sourceRef.restrict chartPiece, volumeDensity E <= D
D < infinity
```

and concludes the same finite lower integral for

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the existing source-image reference finite-integral wrapper;
- `restrict_withDensity_le_smul_of_ae_le`;
- the supplied restricted-volume density identity;
- the supplied local a.e. bound on `volumeDensity`.

## Nonclaims

The theorem does not prove the density identity or the density bound.  It also
does not prove source coverage, chart-image equality, Haar scalar
normalization, normal crossings, pole order, RLCT extraction, or global
original-prior integrability beyond the supplied local chart piece.
