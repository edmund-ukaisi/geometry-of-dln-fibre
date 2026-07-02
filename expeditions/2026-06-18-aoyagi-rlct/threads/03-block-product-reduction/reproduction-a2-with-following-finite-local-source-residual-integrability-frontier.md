# Reproduction - A2 with-following finite local source residual integrability frontier

Date: 2026-07-02.

Status: controller reproduction after interruption; active-readout Lean slice
implemented, p.13 residual-product theorem still open.

## Source Boundary

Aoyagi's Case 2 calculation introduces a selected-entry chart for the
post-pivot residual block and a separate following factor.  In the current
Lean source this distinction is represented by

```text
Case2PassiveThetaWithFollowingFactor =
  Case2PassiveTheta x Matrix (Case2ResidualColIndex n S (J+1)) tau R
```

and by the enlarged retained-data constructor

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor.
```

For an enlarged coordinate `z = (theta, F)`, the stored active two-edge
factors are:

```text
C 1 = case2DisplayedPostPivotResidualBlock
        (case2SuccessorSelectedEntrySourceResidual theta.yNext eNext),

C 0 = F
```

after the forward endpoint reindexing.  This is formalized by the readout
lemmas in `RetainedPassiveCase2PassiveThetaCFieldReadout.lean`:

```text
Case2PassiveThetaWithFollowingFactor.endpointRetainedData_C_one_submatrix_eq_displayedPostPivotResidualBlock
Case2PassiveThetaWithFollowingFactor.endpointRetainedData_C_zero_submatrix_eq_followingFactor
```

The source-chart readback theorem intentionally recovers `theta.yNext` from
the transported `C 1` block and recovers the independent following factor from
the transported `C 0` block.  It does not use the old residual-product inverse.

## Pen-And-Paper Check

The p.13 fixed-base residual coordinate map used by
`residualNegPowerIntegrableOn` is not the active `C 1` readout.  It is the
coordinate readout of

```text
residualFactorProduct (sourceReadback E).C (Fin.last 2) 0,
```

which, in the two-edge Case 2 window, is the product

```text
(post-pivot residual block) * (following factor).
```

For the no-following selected-entry constructor, the following factor is not
free: it is chosen as the paper `C'`/successor following tail attached to the
same selected-entry matrix.  The existing theorem

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

therefore identifies the full residual factor product with the selected-entry
chart-map matrix.  This is the algebra consumed by

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
```

For the enlarged with-following constructor, the analogous equality is not a
formal consequence of finite following-factor mass.  The full residual product
is generally

```text
D(y) * F,
```

not `D(y)` and not the selected-entry chart matrix by itself.  Thus an
argument that integrates only over `yNext` and multiplies by
`followingMeasure Set.univ` proves an active-`C 1` readout statement, not the
p.13 residual-product statement required by the current
`residualNegPowerIntegrableOn` consumer.

The obstruction is mathematical, not just definitional.  If the following
measure is allowed to be an arbitrary finite measure, it may concentrate on a
degenerate following factor such as `F = 0`; then the full product
`D(y) * F` is identically zero and a.e. positivity of the p.13 residual
product fails.  Even for a locally finite Lebesgue patch, integrability and
positivity near degenerate `F` are separate statements from integrability and
positivity of `D(y)`.

## Correct Routes

There are two honest theorem families.

1. Active-readout source theorem.

   Prove finite integrability for the active `C 1` selected-entry readout of
   the enlarged endpoint topology tuple/source chart.  This matches the
   existing with-following active-readout COV:

   ```text
   measure_map_case2PassiveThetaWithFollowingFactor_activeSelectedEntryChart_referenceSource_eq_prod
   measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_activeReadout_comp_referenceSource_eq_prod
   measure_map_case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_activeReadout_eq_activeSelectedEntryChart_restrict
   ```

   This route is useful only for consumers whose loss/residual function has
   already been reduced to the active `C 1` block.  It does not discharge the
   current p.13 `residualNegPowerIntegrableOn` socket by itself.

2. True p.13 residual-product theorem.

   Prove a with-following analogue of the residual-source socket for the full
   p.13 residual product.  This needs an additional hypothesis or lemma beyond
   finite following mass, for example:

   ```text
   a local following-factor nondegeneracy/comparison
     aoyagiCoordinateSquareSum D <= C *
       aoyagiCoordinateSquareSum (D * F)
   ```

   on the selected local following-factor patch, or a direct product
   integrability theorem for the pair `(D, F)` at the relevant exponent.  This
   would then feed the existing p.13 local finite-integral consumers.

## Landed Active-Readout Slice

The active-readout finite-product statement is implemented in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean`:

```text
case2PassiveThetaWithFollowingFactor_activeReadout_pos_ae_and_lintegral_rpow_neg_prod_finiteMass
```

It states that for

```text
sourceMeasure = (passiveMeasure.prod weightedBox).prod followingMeasure
```

with finite passive mass and finite following mass, the active selected-entry
readout

```text
z |-> CenterCoord.chartMap pivotNext z.1.yNext
```

is positive almost everywhere and has finite negative-power lower integral at
the selected-entry exponent threshold.  The proof pushes the enlarged product
measure through `Prod.fst` and then through the selected-entry chart readout,
getting the selected-entry chart-image measure scaled by the passive and
following total masses.

The theorem includes `[SFinite followingMeasure]` because the `map_fst_prod`
API for the trailing following coordinate requires it.  This is satisfied by
the local Lebesgue/reference patches intended downstream.

Focused local build passed for:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
```

## Consequence For The Next Lean Target

Do not state

```text
residual_pos_ae_and_lintegral_rpow_neg_of_...WithFollowingFactor...
```

with only

```text
followingMeasure Set.univ < infinity
```

unless the residual map in the conclusion is the active `C 1` readout rather
than the p.13 `paperEndpointFixedBaseResidualBlockCoordinateMap`.

The smallest currently honest p.13-facing target is a local comparison socket:

```text
exists_open_subset_followingFactor_patch_residualProduct_controls_activeReadout
```

whose hypotheses include a base following factor and a local nondegeneracy
condition strong enough to compare the full residual product to the active
selected-entry block.  After that comparison, the existing selected-entry
finite-integral theorem can be transferred by domination.

The smallest active-readout target is a finite-product measure theorem over
the enlarged source/reference measure saying that the active `C 1` readout
has the same selected-entry finite negative-power integral, scaled by the
finite mass of the passive plus following side.  That target should be named
so that it cannot be confused with the p.13 residual-product socket.

## Nonclaims

This note proves no Lean theorem.  It does not prove determinant-Haar
transport, raw-Haar pushforward, source-prior/original-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.  It also does not mark the with-following finite-integral
wrapper complete: the p.13 source-side finite integral is still missing.
