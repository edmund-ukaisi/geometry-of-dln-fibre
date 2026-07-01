# Statement Card - A2 p.13 Original-prior Volume Source-image Reference Finite Integral

## Claim

The p.13 original-prior finite-integral wrapper can use a concrete local
source-image reference measure

```text
Measure.map sourceChart (coordinateSourceMeasure.restrict V)
```

where `V` is an open passive-theta neighborhood produced inside the returned
`W`.  The theorem leaves the original-volume domination by this concrete
source image as an explicit hypothesis.

The returned data includes:

```text
W open, z0 ∈ W
U open, base ∈ U
V open, z0 ∈ V, V ⊆ W
∀ z ∈ V, readback (sourceChart z) = z
Set.InjOn sourceChart V
ContinuousOn sourceChart V
MeasurableSet (sourceChart '' V)
∀ E ∈ sourceChart '' V, readback E ∈ V ∧ sourceChart (readback E) = E
```

The final chart-piece handler assumes:

```text
chartPiece measurable
chartPiece ⊆ U ∩ sourceStratum
chartPiece ⊆ sourceChart '' V
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂ originalVolume.restrict chartPiece, density E ≤ Kprior
originalVolume.restrict chartPiece <=
  D • Measure.map sourceChart (coordinateSourceMeasure.restrict V)
D < infinity
```

and concludes the finite lower integral over

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the abstract source-reference domination finite-integral wrapper;
- local passive-theta source-image inverse machinery;
- `V ⊆ W` and restriction monotonicity;
- the explicit original-volume domination by the concrete source-image measure.

## Nonclaims

This theorem does not prove original-volume domination by the source-image
measure, identify a global passive-theta image, prove source coverage,
chart-image equality, source-rank coverage, Haar scalar normalization, normal
crossings, pole order, RLCT extraction, or global original-prior integrability
beyond the supplied local chart piece.
