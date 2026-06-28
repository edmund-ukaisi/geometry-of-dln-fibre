# Statement Card - A2 retained-passive source-edge-family chart-produced measure

## Claim

For a retained-passive determinant-chart data path, the fixed-base p.13 source
edge-family map produces the selected-entry chart-produced finite-integral
handoff.  The theorem removes separate user-facing hypotheses for source-chart
a.e. measurability, local-source membership, and source-readback residual
factor readout.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction and pp. 19-22 for the selected-entry Case 2 chart shape.  The
proof is finite source-chart bookkeeping and a measure handoff, not a new
normal-crossing or RLCT extraction theorem.  Lean dependencies:

```text
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Expected declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

## Nonclaims

No endpoint-equivalence construction, no label-preserving endpoint provenance,
no original prior or external source measure identification, no Jacobian
comparison for such a prior, no source-rank coverage, no normal crossings, no
pole order, and no RLCT.

Retained hypotheses include the finite-dimensional fixed-base context, the
determinant-chart subtype measurable/open-measurable instances,
`hdet`, `residualCoordEquiv`, `hdataFactor`, the load-bearing
`hretainedData : AEMeasurable (fun y => <retainedData y, hdet y>) signedBox`,
the source data for `Cedge := fun E : EdgeFamily => E`, `0 < Rreg`,
`0 < creg`, `0 <= Creg`, `0 < t`, positive residual radii, the selected-entry
critical inequality, `nu.IsAddHaarMeasure`, the local loss lower bound, and
the local density nonnegativity/boundedness hypotheses.

## Verification Plan

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
Remaining close-out checks: `scripts/sorries`, `git diff --check`,
touched-file forbidden-marker search, direct axiom probe for the new
declaration, and xhigh review.
