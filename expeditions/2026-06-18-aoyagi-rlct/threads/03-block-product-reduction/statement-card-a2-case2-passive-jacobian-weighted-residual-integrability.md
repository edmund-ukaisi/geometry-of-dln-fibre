# Statement Card - A2 Case 2 Passive Jacobian-Weighted Residual Integrability

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Lean Names

```text
ae_of_measure_le_smul
lintegral_lt_top_of_measure_le_smul
map_le_smul_map_of_le_smul
measure_le_smul_of_le_smul_restrict
exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
```

## Reproduction

```text
reproduction-a2-case2-passive-jacobian-weighted-residual-integrability.md
```

## Claim

For the local passive product-domain measure weighted by the retained-passive
solved-`A1` product raw-order Jacobian factor and then mapped by the passive
source chart, the residual coordinate square sum is positive almost everywhere
and its negative-power lintegral is finite below the selected-entry critical
threshold, assuming the passive measure has finite total mass.

## Proved

There exists an open set `U` with `z0 in U` such that, for

```text
weighted =
  (sourceMeasure.restrict U).withDensity (fun z => ofReal (J z))

muJ = Measure.map sourceChart weighted,
```

the theorem proves

```text
for muJ-a.e. E, 0 < aoyagiCoordinateSquareSum (residualMap E)

int^- E,
  ofReal ((aoyagiCoordinateSquareSum (residualMap E))^(-t)) d muJ
  < infinity.
```

The generic helpers prove that a.e. truths and finite lower integrals transfer
from `mu` to any `nu` satisfying `nu <= c • mu` with `c < infinity`, and that
this scalar domination is preserved by measurable maps.

## Assumed

- Finite total passive mass: `passiveMeasure Set.univ < infinity`.
- The selected-entry signed-box radius hypotheses: `forall i, 0 < Rres i`.
- The exponent hypotheses: `0 <= t` and
  `2 * t < ((center.erase (J + 2, J + 2)).card : R) + 1`.
- Passive field continuity and pointwise determinant-unit hypotheses for
  `Ctop` and `A1passive`.
- Measurable/open-measurable/Borel structure for the chart-produced
  `EdgeFamily` measure.

## Cited

None.

## Deferred

Exact localized residual marginal, determinant-chart Haar transport,
raw/source Haar transport, external or original source-prior comparison,
source-prior Jacobian accounting, source-image equality, local inverse/coverage
of arbitrary source points, normal crossings, pole order, and RLCT extraction.

## Status

Proved in Lean.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  `git diff
--check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  Direct axiom probes report
`[propext, Classical.choice, Quot.sound]`.  Archimedes the 3rd xhigh read-only
review found only two stale module-doc boundary comments; both were fixed in
`review-a2-case2-passive-jacobian-weighted-residual-integrability.md`.
