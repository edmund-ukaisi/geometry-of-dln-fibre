# Statement Card - A2 p.13 Original-prior Volume-source-reference Finite Integral

## Claim

The original edge-family prior restricted to a supplied p.13 chart piece feeds
into the Case 2 passive-theta readback finite-integral socket if the restricted
original edge-family volume is dominated by a source reference whose readback
pushforward is the coordinate source measure on the selected theta
neighborhood.

The final chart-piece handler assumes:

```text
chartPiece measurable
chartPiece ⊆ sourceLocal
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ Kprior
AEMeasurable readback sourceRef
Measure.map readback sourceRef = coordinateSourceMeasure.restrict W
(originalEdgeFamilyVolume b).restrict chartPiece ≤ D • sourceRef
D < infinity
```

and concludes the finite lower integral over

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the existing p.13 original-prior finite-integral theorem;
- the p.13 formal-volume source-reference readback bridge;
- the original-prior local density bound against `originalEdgeFamilyVolume`;
- the supplied source-reference readback pullback identity;
- the supplied restricted original-volume domination.

## Proof Shape

1. Invoke the existing original-prior finite-integral theorem to obtain `W`,
   then `U`, and its chart-piece handler.
2. For the supplied chart piece, use the formal-volume source-reference bridge
   with `thetaRef := coordinateSourceMeasure.restrict W`.
3. Set `Cformal := (cHaar : ENNReal) * D`.
4. Prove `Cformal < infinity` from `D < infinity`.
5. Apply the existing original-prior finite-integral handler with the derived
   formal p.13 readback assumptions.

## Nonclaims

This theorem does not prove restricted-volume domination, identify the source
reference with a passive-theta source-image measure, prove source coverage,
chart-image equality, source-rank coverage, Haar scalar normalization, normal
crossings, pole order, RLCT extraction, or global original-prior
integrability beyond the supplied local chart piece.
