# Statement Card - A2 Original Edge-Family Volume Haar Normalization

Date: 2026-07-01.

## Claim

Fixed-basis matrix readout packages continuous edge families as a continuous
linear equivalent copy of the original matrix tuple space. Consequently
`originalEdgeFamilyVolume b` is an additive Haar measure on the full
edge-family space, and any additive Haar measure on that same full space
differs from it by Mathlib's canonical Haar scalar factor.

## Lean Statements

```text
edgeFamilyMatrixTupleLinearEquiv
edgeFamilyMatrixTupleLinearEquiv_apply
edgeFamilyMatrixTupleLinearEquiv_symm_apply
edgeFamilyMatrixTupleContinuousLinearEquiv

isAddHaarMeasure_originalEdgeFamilyVolume

originalEdgeFamilyVolume_eq_addHaarScalarFactor_smul
originalEdgeFamilyVolume_addHaarScalarFactor_pos
originalEdgeFamilyVolume_addHaarScalarFactor_coe_lt_top
```

Location:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean
```

Aggregator:

```text
lean/DLNFibre.lean
```

## Dependencies

- `OriginalPriorHaar.isAddHaarMeasure_originalTupleVolume`
- `OriginalEdgeFamilyPrior.edgeFamilyMatrixTuple`
- `OriginalEdgeFamilyPrior.tupleToEdgeFamily`
- `OriginalEdgeFamilyPrior.edgeFamilyMatrixTuple_tupleToEdgeFamily`
- `OriginalEdgeFamilyPrior.tupleToEdgeFamily_edgeFamilyMatrixTuple`
- `OriginalEdgeFamilyPrior.continuous_edgeFamilyMatrixTuple`
- `OriginalEdgeFamilyPrior.continuous_tupleToEdgeFamily`
- Mathlib continuous-linear-equivalence Haar pushforward
- Mathlib `isAddLeftInvariant_eq_smul`
- Mathlib `addHaarScalarFactor_pos_of_isAddHaarMeasure`

## Reproduction

`threads/03-block-product-reduction/reproduction-a2-original-edge-family-volume-haar-normalization.md`

## Verification

Current local checks:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPriorHaar
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries                    # from lean/: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_edge_family_prior_haar_axioms.lean
```

## Review

`threads/03-block-product-reduction/review-a2-original-edge-family-volume-haar-normalization.md`

xhigh `Lagrange the 2nd` PASS.

## Nonclaims

This is not a retained-passive source-chart transport theorem. It proves no
equality between original edge-family volume and chart-produced source-image
measure, no chart-piece equality, no readback domination, no determinant-chart
Haar transport, no Aoyagi chart Jacobian theorem, no source-rank coverage, no
normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- The bundled equivalence must agree definitionally with the existing
  fixed-basis readout and reconstruction maps.
- The file must not install broad global topology/Borel instances for
  continuous-linear-map product spaces.
- Downstream users must keep the scalar factor; exact equality is only valid
  after an additional normalization theorem fixing the Haar measure.
