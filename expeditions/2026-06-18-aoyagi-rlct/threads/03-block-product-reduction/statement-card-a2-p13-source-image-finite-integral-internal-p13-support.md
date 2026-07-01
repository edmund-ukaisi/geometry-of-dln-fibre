# Statement Card - A2 p.13 Source-image Finite-integral Internal p.13 Support

## Claim

The concrete source-image finite-integral wrappers can internalize the p.13
source-set support obligation.  Their final chart-piece handlers assume:

```text
chartPiece measurable
chartPiece subset U inter sourceStratum
chartPiece subset sourceChart '' V
forall E in chartPiece, readback E in W and sourceChart (readback E) = E
```

and no longer separately assume:

```text
chartPiece subset p13SourceSet.
```

The proof derives that containment from the returned image support
`forall E in sourceChart '' V, E in p13SourceSet`.

## Public Lean Names

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolumeSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- `exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet`;
- the previous source-reference finite-integral socket;
- elementary subset composition.

## Nonclaims

This does not prove source coverage, source-image equality, original-volume
transport to the source-image reference, density identity or density bound,
Haar or Jacobian transport, normal crossings, pole order, or RLCT extraction.
