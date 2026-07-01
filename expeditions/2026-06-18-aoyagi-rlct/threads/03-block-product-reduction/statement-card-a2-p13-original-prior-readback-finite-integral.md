# Statement Card - A2 p.13 Original-prior Readback Finite Integral

## Claim

The original edge-family prior restricted to a supplied p.13 chart piece feeds
into the existing Case 2 passive-theta readback finite-integral socket, provided
the formal-product p.13 chart measure has the supplied readback domination by
the coordinate source measure.

The final chart-piece handler assumes:

```text
chartPiece measurable
chartPiece ⊆ sourceLocal
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ Kprior
AEMeasurable readback muP13
Measure.map readback muP13 ≤ Cformal • coordinateSourceMeasure.restrict W
Cformal < infinity
```

and concludes the finite lower integral over

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_formalProductReadback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the passive-theta readback finite-integral socket;
- the p.13 original-prior readback domination bridge;
- the p.13 readback-domination scalar finite helper;
- the original-prior local density bound against `originalEdgeFamilyVolume`;
- the supplied formal-product p.13 readback measurability and domination.

## Proof Shape

1. Invoke the existing passive-theta finite-integral socket to obtain `W`, then
   `U`, and the chart-piece finite-integral handler.
2. For a supplied chart piece, split `chartPiece ⊆ U ∩ sourceStratum` into the
   two subset hypotheses expected by the existing handler.
3. Use the p.13 original-prior readback bridge with
   `thetaRef := coordinateSourceMeasure.restrict W`.
4. Use the scalar finite helper to prove the resulting `Cpull` is finite.
5. Apply the existing handler with
   `externalSourceMeasure := originalEdgeFamilyPrior b density`.

## Nonclaims

This theorem does not prove formal p.13 measure domination by the passive
coordinate source measure, identify the formal p.13 measure with a
passive-theta source-image measure, prove source coverage, chart-image equality,
source-rank coverage, Haar scalar normalization, normal crossings, pole order,
RLCT extraction, or global original-prior integrability beyond the supplied
local chart piece.
