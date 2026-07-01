# Reproduction - A2 p.13 Source-image Finite-integral Internal p.13 Support

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean strengthening implemented and verified.

## Question

The source-image finite-integral wrappers currently ask the chart-piece handler
for both:

```text
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet.
```

Once the returned local image itself is known to lie in `p13SourceSet`, can the
second assumption be removed from the source-image wrappers?

## Calculation

Use the strengthened local source-image support package to produce `V` with:

```text
forall E in sourceChart '' V, E in p13SourceSet.
```

Then in the final chart-piece handler, assume only:

```text
chartPiece subset sourceChart '' V.
```

For any `E in chartPiece`, applying the chart-piece image containment gives
`E in sourceChart '' V`, and applying the returned image-support theorem gives
`E in p13SourceSet`.  Therefore:

```text
chartPiece subset p13SourceSet.
```

This is exactly the old p.13 support hypothesis needed by the lower
source-reference finite-integral socket.  No measure comparison changes.

## Lean Target

Strengthen in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

Targets:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The final chart-piece handler should no longer ask for
`chartPiece subset p13SourceSet`; it should derive that containment from
`chartPiece subset sourceChart '' V`.

## Nonclaims

This does not prove source coverage, source-image equality, original-volume
transport to the source-image reference, the source-image density identity or
bound, Haar or Jacobian transport, normal crossings, pole order, or RLCT
extraction.
