# Statement Card - A2 p.13 Original-prior Volume-readback Domination Finite Integral

## Claim

The p.13 original-prior finite-integral wrapper can use the restricted original
edge-family volume itself as the source reference.  The final chart-piece
handler no longer asks for an arbitrary `sourceRef` or scalar `D`; it asks only
for readback domination of the concrete volume piece.

The final chart-piece handler assumes:

```text
chartPiece measurable
chartPiece ⊆ sourceLocal
chartPiece ⊆ p13SourceSet
∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ Kprior
AEMeasurable readback ((originalEdgeFamilyVolume b).restrict chartPiece)
Measure.map readback ((originalEdgeFamilyVolume b).restrict chartPiece)
  <= Csource • coordinateSourceMeasure.restrict W
Csource < infinity
```

and concludes the finite lower integral over

```text
((originalEdgeFamilyPrior b density).restrict chartPiece).prod ν.
```

## Public Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the previous source-reference finite-integral wrapper;
- the instantiation `sourceRef := (originalEdgeFamilyVolume b).restrict chartPiece`;
- the trivial domination `volumePiece <= 1 • volumePiece`;
- `1 < infinity` and the supplied `Csource < infinity`.

## Proof Shape

1. Call the previous source-reference domination finite-integral wrapper.
2. In the final chart-piece handler, set `volumePiece` to the restricted
   original edge-family volume.
3. Apply the previous handler with `sourceRef := volumePiece` and `D := 1`.
4. Discharge the restricted-volume domination by reflexivity after `one_smul`.

## Nonclaims

This theorem does not prove the readback domination for the original volume
piece, identify a passive-theta source image, prove source coverage,
chart-image equality, source-rank coverage, Haar scalar normalization, normal
crossings, pole order, RLCT extraction, or global original-prior integrability
beyond the supplied local chart piece.
