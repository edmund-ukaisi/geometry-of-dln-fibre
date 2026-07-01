# Reproduction - A2 p.13 Original-prior Volume-source-reference Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check before Lean.

## Question

The current p.13 original-prior finite-integral theorem consumes formal-product
p.13 readback domination:

```text
AEMeasurable readback muP13,
Measure.map readback muP13 <= Cformal • coordinateSourceMeasure.restrict W,
Cformal < infinity.
```

Can we replace those final chart-piece inputs by a source-reference measure
`sourceRef` and a restricted original-volume domination:

```text
AEMeasurable readback sourceRef,
Measure.map readback sourceRef = coordinateSourceMeasure.restrict W,
(originalEdgeFamilyVolume b).restrict chartPiece <= D • sourceRef,
D < infinity?
```

## Calculation

Let `muP13` be the formal-product p.13 raw-order chart measure restricted to
the same `chartPiece`, and let

```text
cHaar =
  ((Measure.map rawOrderEquiv m).addHaarScalarFactor (originalTupleVolume d)).
```

The existing formal-volume source-reference bridge gives

```text
AEMeasurable readback muP13,
Measure.map readback muP13
  <= ((cHaar : ENNReal) * D) • coordinateSourceMeasure.restrict W.
```

This uses only the supplied source-reference pullback identity and the supplied
restricted-volume domination.  It does not identify `sourceRef` with any
passive-theta image measure.

The scalar supplied to the existing original-prior finite-integral theorem is

```text
Cformal := (cHaar : ENNReal) * D.
```

It is finite from `D < infinity`, because `cHaar : NNReal` is finite as an
`ENNReal` scalar.  The existing theorem then applies to the original prior
using the unchanged hypotheses:

```text
chartPiece measurable,
chartPiece ⊆ sourceLocal,
chartPiece ⊆ p13SourceSet,
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E,
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E <= Kprior.
```

## Lean Target

Add to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Kill Conditions

- If the theorem proves the restricted-volume domination, it overclaims.
- If it identifies `sourceRef` with the passive-theta source image or with a
  coordinate measure, it overclaims.
- If it removes the separate `chartPiece ⊆ sourceLocal` or
  `chartPiece ⊆ p13SourceSet` hypotheses, it overclaims.
- If it proves source coverage, chart-image equality, scalar cancellation,
  normal crossings, pole order, or RLCT extraction, it overclaims.
