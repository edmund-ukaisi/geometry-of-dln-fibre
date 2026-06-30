# Statement Card - A2 chart-piece external-source measure handoff

Date: 2026-06-30.

## Lean Targets

```text
restrict_withDensity_le_smul_restrict_of_ae_le_of_subset

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Statement

After the same Case 2 passive-theta setup and local source neighborhood used by
the existing external-source handoff, Lean returns `U` and
`sourceLocal = U inter sourceStratum`.  For any measurable
`chartPiece subset sourceLocal`, a local equality

```text
externalSourceMeasure.restrict chartPiece
  =
(sourceImageMeasure.withDensity externalDensity).restrict chartPiece
```

and an a.e. bound

```text
externalDensity <= Cext
```

with respect to `sourceImageMeasure.restrict chartPiece`, with `Cext < infinity`,
imply finite loss-power integrability over

```text
(externalSourceMeasure.restrict chartPiece).prod nu.
```

## Proof Inputs

- Existing full-product domination finite-integral socket for
  `(sourceImageMeasure.restrict (U inter sourceStratum)).prod nu`.
- `restrict_withDensity_le_smul_restrict_of_ae_le`.
- `Measure.restrict_mono` for `chartPiece subset sourceLocal`.
- `prod_le_smul_prod_of_le_smul_left`.
- `[SFinite nu]` and `Cext < infinity`.

## Nonclaims

No original/source-prior transport, no chart-image measurability, no
source-image equality, no source-rank coverage, no Haar/Jacobian transport, no
normal crossings, no pole order, and no RLCT extraction.
