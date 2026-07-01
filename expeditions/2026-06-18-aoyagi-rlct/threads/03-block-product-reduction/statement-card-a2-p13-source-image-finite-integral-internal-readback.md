# Statement Card - A2 p.13 Source-image Finite-integral Internal Readback

## Claim

The concrete source-image finite-integral wrappers can internalize the
chart-piece readback/right-inverse obligation.  Their final chart-piece
handlers assume:

```text
chartPiece measurable
chartPiece subset U inter sourceStratum
chartPiece subset sourceChart '' V
```

and no longer separately assume:

```text
forall E in chartPiece, readback E in W and sourceChart (readback E) = E.
```

The proof derives that property from the returned local right inverse on
`sourceChart '' V` and the returned containment `V subset W`.

## Public Lean Names

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the returned local right-inverse theorem on `sourceChart '' V`;
- `V subset W`;
- elementary subset composition.

## Nonclaims

This does not prove source coverage, source-image equality, original-volume
transport to the source-image reference, density identity or density bound,
Haar or Jacobian transport, normal crossings, pole order, or RLCT extraction.
