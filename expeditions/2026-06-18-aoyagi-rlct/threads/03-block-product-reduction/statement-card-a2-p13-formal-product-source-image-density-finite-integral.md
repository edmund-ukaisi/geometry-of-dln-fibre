# Statement card - A2 p.13 formal-product source-image density finite integral

## Lean theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_formalProductSourceImageReference_eq_withDensity_bounded_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13FormalProductSourceImageFiniteIntegral.lean
```

## Statement

For the Case 2 passive-theta endpoint source chart, the theorem returns the
same `W` as the existing formal-product readback finite-integral socket and an
additional local source-image chart `V subset W`.  The returned `V` has:

```text
readback (sourceChart z) = z on V,
sourceChart injective and continuous on V,
sourceChart '' V measurable,
readback E in V and sourceChart (readback E) = E on sourceChart '' V.
```

For any measurable `chartPiece subset sourceLocal` with
`chartPiece subset sourceChart '' V`, the final handler assumes a prior density
bound and a bounded-density identity

```text
muP13 =
  ((Measure.map sourceChart (coordinateSourceMeasure.restrict V)).withDensity
    formalDensity).restrict chartPiece
```

with `formalDensity <= D` a.e. on the restricted source-image reference and
`D < infinity`.  It concludes the original edge-family prior finite integral
over `chartPiece`.

## Inputs kept explicit

- the formal-product/source-image density identity;
- the a.e. formal-density bound and finite scalar `D`;
- chart-piece measurability and containment in `sourceLocal`;
- chart-piece containment in `sourceChart '' V`;
- the original-prior density upper bound.

## Derived internally

- `chartPiece subset p13SourceSet`;
- `readback E in W` and `sourceChart (readback E) = E` on the chart piece;
- `AEMeasurable readback muP13`;
- `Measure.map readback muP13 <= D • coordinateSourceMeasure.restrict W`.

## Dependencies

- the formal-product readback finite-integral socket;
- `exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet`;
- `map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn`.

## Nonclaims

No formal-product/source-image density identity or density bound is proved.  No
source-image coverage, source-rank coverage, Haar transport, scalar
normalization, normal crossings, pole order, or RLCT extraction is proved.
