# Reproduction - A2 p.13 Original-prior Volume Source-image Reference Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean theorem implemented.

## Question

The previous finite-integral wrapper accepts an abstract source reference
`sourceRef`.  Can we specialize that reference to the concrete local
passive-theta source-image measure

```text
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V)
```

for a locally produced passive-theta chart `V ⊆ W`, so that the remaining
source-reference hypothesis is the honest local domination

```text
originalVolume.restrict chartPiece <= D • sourceRef?
```

## Calculation

The existing passive-theta source-image API supplies, after shrinking inside
an open `W`, an open `V` with

```text
V ⊆ W,
readback (sourceChart z) = z       for z ∈ V,
Set.InjOn sourceChart V,
ContinuousOn sourceChart V,
MeasurableSet (sourceChart '' V),
∀ E ∈ sourceChart '' V, readback E ∈ V ∧ sourceChart (readback E) = E.
```

Let

```text
sourceRef := Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The local inverse API gives

```text
AEMeasurable readback sourceRef,
Measure.map readback sourceRef = coordinateSourceMeasure.restrict V.
```

Since `V ⊆ W`, restriction monotonicity gives

```text
coordinateSourceMeasure.restrict V <= coordinateSourceMeasure.restrict W.
```

Therefore

```text
Measure.map readback sourceRef
  <= 1 • coordinateSourceMeasure.restrict W.
```

The previous source-reference domination finite-integral wrapper applies with
`Csource := 1`.  The only remaining measure comparison is the explicit
assumption

```text
originalVolume.restrict chartPiece <= D • sourceRef,
D < infinity.
```

The chart piece is also required to lie in `sourceChart '' V`, so the concrete
source image is the actual local image rather than an asserted global image.

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

Target:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

Use:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_image_eq_self
measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
```

## Kill Conditions

- If the theorem claims the original-volume domination by the source-image
  measure, it overstates this step; that domination remains explicit.
- If it claims global source coverage or chart-image equality, it overclaims.
- If it normalizes the Haar scalar, constructs normal crossings, computes pole
  order, or extracts RLCT, it overclaims.
