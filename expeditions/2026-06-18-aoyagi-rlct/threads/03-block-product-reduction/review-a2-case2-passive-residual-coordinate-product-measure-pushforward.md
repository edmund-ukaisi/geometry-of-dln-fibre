# Review - A2 Case 2 Passive Residual-Coordinate Product-Measure Pushforward

Date: 2026-06-29.

Reviewers: Faraday the 3rd and Dalton the 3rd, xhigh, read-only scouts.

Verdict: PASS.

## Scope Checked

Lean theorem target:

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
```

## Findings

Both scouts identified the same required theorem shape.  The residual readout
factors through the selected-entry coordinate, so the product-domain
pushforward reduces to the selected-entry chart-map pushforward after applying
`Measure.map_snd_prod`.

The crucial correction is the scalar:

```text
passiveMeasure Set.univ.
```

For arbitrary `passiveMeasure`, omitting this scalar would be false.  A
mass-one or probability hypothesis would be needed to remove it.  The landed
theorem keeps the scalar and therefore has the correct generality.

No source-rank hypotheses are needed.  The determinant-unit hypotheses are
only the existing source-chart packaging inputs.

## Boundary

The theorem is chart-produced residual-coordinate bookkeeping.  It does not
identify an external/original source prior, a determinant-chart Haar measure,
or a raw/source Haar pushforward.  It also does not prove passive Jacobian
accounting for an ambient prior, source-rank coverage, source-image equality,
local inverse/coverage, normal crossings, pole order, or RLCT.

## Gates

Focused build passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

Final status-doc updates, commit, and push are controller integration steps.
