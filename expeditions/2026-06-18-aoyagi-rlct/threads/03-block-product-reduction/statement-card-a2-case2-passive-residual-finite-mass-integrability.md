# Statement Card - A2 Case 2 Passive Residual Finite-Mass Integrability

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Lean Name

```text
residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
```

## Reproduction

```text
reproduction-a2-case2-passive-residual-finite-mass-integrability.md
```

## Claim

For the passive-domain Case 2 chart-produced source measure, the residual
coordinate square sum is positive almost everywhere and its negative-power
lintegral is finite below the selected-entry critical threshold, assuming the
passive measure has finite total mass.

## Proved

For

```text
mu = Measure.map sourceChart (passiveMeasure.prod weightedBox),
```

the theorem proves

```text
for mu-a.e. E, 0 < aoyagiCoordinateSquareSum (residualMap E)

int^- E,
  ofReal ((aoyagiCoordinateSquareSum (residualMap E))^(-t)) d mu
  < infinity.
```

## Assumed

- Finite total passive mass: `passiveMeasure Set.univ < infinity`.
- The selected-entry signed-box radius hypotheses: `forall i, 0 < Rres i`.
- The exponent hypotheses: `0 <= t` and
  `2 * t < ((center.erase (J + 2, J + 2)).card : R) + 1`.
- Passive field continuity and pointwise determinant-unit hypotheses for
  `Ctop` and `A1passive`, as needed by the source chart and residual marginal.
- Measurable/open-measurable/Borel structure for the chart-produced
  `EdgeFamily` measure.

## Cited

None.

## Deferred

Determinant-chart Haar transport, raw/source Haar transport, external or
original source-prior comparison, source-image equality, local inverse/coverage
of arbitrary source points, localization through arbitrary neighborhoods,
normal crossings, pole order, and RLCT extraction.

## Status

Proved in Lean.  Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  `git diff
--check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  Direct axiom probe reports
`[propext, Classical.choice, Quot.sound]`.  Aristotle the 3rd xhigh read-only
review returned PASS in
`review-a2-case2-passive-jacobian-withdensity-and-residual-finite-mass.md`.
