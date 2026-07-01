# Reproduction - A2 p.13 Source-image Finite-integral Internal Readback

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean strengthening proved
and verified.

## Question

The concrete source-image finite-integral wrappers still ask the final
chart-piece handler for:

```text
forall E in chartPiece, readback E in W and sourceChart (readback E) = E.
```

Can this be derived from `chartPiece subset sourceChart '' V` and the returned
local source-image inverse package?

## Calculation

The local package returns:

```text
V subset W
forall E in sourceChart '' V,
  readback E in V and sourceChart (readback E) = E.
```

Assume:

```text
chartPiece subset sourceChart '' V.
```

For `E in chartPiece`, first get `E in sourceChart '' V`.  The local right
inverse gives:

```text
readback E in V
sourceChart (readback E) = E.
```

Since `V subset W`, this implies:

```text
readback E in W
sourceChart (readback E) = E.
```

This is exactly the old final-handler readback hypothesis.

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

The final chart-piece handler should no longer ask for the readback/right
inverse property on `chartPiece`; it should derive it from image containment.

## Nonclaims

This does not prove source coverage, source-image equality, original-volume
transport to the source-image reference, the source-image density identity or
bound, Haar or Jacobian transport, normal crossings, pole order, or RLCT
extraction.
