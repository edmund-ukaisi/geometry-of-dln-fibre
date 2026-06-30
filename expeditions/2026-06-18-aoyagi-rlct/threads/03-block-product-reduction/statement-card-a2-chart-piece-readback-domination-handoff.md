# Statement Card - A2 chart-piece readback-domination handoff

Date: 2026-06-30.

## Lean Targets

```text
measure_le_smul_restrict_of_le_smul_of_restrict_eq_self
restrict_restrict_eq_self_of_subset
restrict_le_smul_restrict_of_le_smul_of_subset

measure_restrict_piece_le_smul_map_restrict_of_map_readback_restrict_piece_le_smul

exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_map_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Statement

After the same Case 2 passive-theta setup and local finite-integral socket,
Lean returns `W`, `U`, and `sourceLocal = U inter sourceStratum`.  For any
measurable `chartPiece subset sourceLocal`, a caller may supply:

```text
forall E in chartPiece,
  readback E in W and sourceChart (readback E) = E

AEMeasurable readback (externalSourceMeasure.restrict chartPiece)

Measure.map readback (externalSourceMeasure.restrict chartPiece)
  <= Cpull * coordinateSourceMeasure.restrict W

Cpull < infinity.
```

Then Lean proves finite loss-power integrability over

```text
(externalSourceMeasure.restrict chartPiece).prod nu.
```

Here

```text
coordinateSourceMeasure =
  baseJ.withDensity (fun z => sourceImageDensity (sourceChart z)).
```

## Proof Inputs

- Existing full-product domination finite-integral socket for
  `(sourceImageMeasure.restrict sourceLocal).prod nu`.
- `map_withDensity_comp_of_aemeasurable` for
  `Measure.map sourceChart (coordinateSourceMeasure.restrict W) =
  sourceImageMeasure`.
- New generic readback helper
  `measure_restrict_piece_le_smul_map_restrict_of_map_readback_restrict_piece_le_smul`.
- New support/restriction helpers in `LocalMeasureHandoff`.
- `prod_le_smul_prod_of_le_smul_left`, `[SFinite nu]`, and `Cpull < infinity`.

## Nonclaims

No original/source-prior transport, no chart-image equality, no source-rank
coverage, no Haar/Jacobian transport, no normal crossings, no pole order, and
no RLCT extraction.
