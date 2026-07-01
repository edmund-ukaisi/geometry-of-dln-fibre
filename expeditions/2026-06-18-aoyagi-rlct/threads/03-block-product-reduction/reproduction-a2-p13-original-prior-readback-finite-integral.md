# Reproduction - A2 p.13 Original-prior Readback Finite Integral

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This is a consumer theorem composing
two already-proved measure handoffs.

## Question

The passive-theta readback finite-integral socket says that, after choosing a
local theta neighborhood `W` and a local source neighborhood `U`, finite
integrability over a chart-piece source measure follows from the readback-side
domination

```text
Measure.map readback (externalSourceMeasure.restrict chartPiece)
  <= Cpull • coordinateSourceMeasure.restrict W
```

with `Cpull < infinity`.

The p.13 original-prior readback bridge says that if the formal-product p.13
chart measure `muP13` has a supplied readback domination

```text
Measure.map readback muP13 <= Cformal • coordinateSourceMeasure.restrict W,
```

then the original edge-family prior restricted to the same chart piece has
readback domination with

```text
Cpull := (ENNReal.ofReal Kprior * ((cHaar^-1 : NNReal) : ENNReal)) * Cformal.
```

Can we instantiate the passive-theta socket with the original edge-family
prior on the chart piece?

## Calculation

Let

```text
originalPriorPiece :=
  (originalEdgeFamilyPrior b density).restrict chartPiece
```

and let `muP13` be the formal-product p.13 raw-order chart measure restricted
to `chartPiece`.

The existing p.13 bridge gives, from the local density bound

```text
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece,
  density E <= Kprior,
```

and from the supplied formal readback assumptions,

```text
AEMeasurable readback muP13
Measure.map readback muP13 <= Cformal • coordinateSourceMeasure.restrict W,
```

the pair

```text
AEMeasurable readback originalPriorPiece
Measure.map readback originalPriorPiece <= Cpull • coordinateSourceMeasure.restrict W.
```

The finite-scalar helper gives `Cpull < infinity` from `Cformal < infinity`.
Therefore the passive-theta finite-integral socket applies with

```text
externalSourceMeasure := originalEdgeFamilyPrior b density.
```

The source-local side hypotheses are not changed.  The chart piece must still
be measurable, contained in the returned `sourceLocal := U ∩ sourceStratum`,
and contained in the named p.13 source edge-family set.  The pointwise
readback/right-inverse condition on the chart piece is also still required.

## Lean Target

Add a downstream module:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

with imports:

```text
OriginalEdgeFamilyP13SourceMeasureBridge
RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
```

Public theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_formalProductReadback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Kill Conditions

- If the theorem proves or suggests the formal-product readback domination, it
  overclaims.
- If it identifies `muP13` with the passive-theta source-image measure, it
  overclaims.
- If it removes the separate `chartPiece ⊆ sourceLocal` or
  `chartPiece ⊆ p13SourceSet` hypotheses, it overclaims.
- If it claims global original-prior integrability rather than local
  chart-piece integrability, it overclaims.
- If it proves normal crossings, pole order, or RLCT extraction, it overclaims.
