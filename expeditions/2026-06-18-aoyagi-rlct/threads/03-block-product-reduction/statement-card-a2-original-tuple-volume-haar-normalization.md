# Statement Card - A2 Original Tuple Volume Haar Normalization

Date: 2026-06-30.

## Claim

The original flattened coordinate volume and tuple-side original coordinate
volume are additive Haar measures. Consequently any additive Haar measure on
the same tuple space differs from `originalTupleVolume d` by Mathlib's
canonical Haar scalar factor.

## Lean Statements

```text
canonicalCoordLinearEquiv
canonicalCoordLinearEquiv_apply
canonicalCoordLinearEquiv_symm_apply

isAddHaarMeasure_originalCoordinateVolume
isAddHaarMeasure_originalTupleVolume

originalTupleVolume_eq_addHaarScalarFactor_smul
originalTupleVolume_addHaarScalarFactor_pos
```

Location:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalPriorHaar.lean
```

Aggregator:

```text
lean/DLNFibre.lean
```

## Dependencies

- `OriginalPrior.originalCoordinateVolume`
- `OriginalPrior.originalTupleVolume`
- `Core.OrbitCodim.canonicalCoord`
- `ChartTopology` matrix topology/Borel bridge instances
- Mathlib `isAddHaarMeasure_volume_pi`
- Mathlib continuous-linear-equivalence Haar pushforward
- Mathlib `isAddLeftInvariant_eq_smul`
- Mathlib `addHaarScalarFactor_pos_of_isAddHaarMeasure`

## Reproduction

`threads/03-block-product-reduction/reproduction-a2-original-tuple-volume-haar-normalization.md`

## Verification

Current local checks:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalPriorHaar.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalPriorHaar
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_original_prior_haar_axioms.lean
```

## Review

`threads/03-block-product-reduction/review-a2-original-tuple-volume-haar-normalization.md`

xhigh `Kant the 2nd` PASS after duplicate-instance repair.

## Nonclaims

This is not a retained-passive source-chart transport theorem. It proves no
equality between original volume and chart-produced source-image measure, no
chart-piece equality, no readback domination, no Aoyagi chart Jacobian theorem,
no source-rank coverage, no normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- `canonicalCoordLinearEquiv` must agree definitionally with the existing
  entry-flattening `canonicalCoord`.
- The tuple topology/Borel structure must remain the product coordinate one;
  the file must not export duplicate matrix topology/Borel instances.
- Downstream users must keep the scalar factor; exact equality is only valid
  after a normalization theorem fixing the Haar measure.
