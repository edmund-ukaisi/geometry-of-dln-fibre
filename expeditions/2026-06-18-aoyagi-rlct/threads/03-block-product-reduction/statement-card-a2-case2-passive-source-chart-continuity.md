# Statement Card - A2 Case 2 Passive Source-Chart Continuity

Status: sorry-free focused build; direct axiom probe passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-case2-passive-source-chart-continuity.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

The passive-parameter Case 2 selected-entry retained-passive datum is
continuous in `(theta, y)` when the supplied passive fields are continuous in
`theta`.  Under pointwise determinant-unit hypotheses, the endpoint-transported
fixed-base retained-passive source chart is also continuous in `(theta, y)`.

## Lean

```text
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
```

## Proved

- The finite retained-passive datum built from passive fields and selected-
  entry residual coordinates is continuous.
- The fixed-base source edge-family map produced from the endpoint-transported
  passive datum is continuous once the determinant-chart subtype is available.
- The theorem has no measure input.  Future product-measure work can use this
  continuity to discharge a.e. measurability hypotheses.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of the passive field families `A1passive`, `F2`, `A3passive`,
  `Ctop`, and `F3`.
- For the source-chart theorem only: pointwise unit hypotheses
  `forall theta, IsUnit (Ctop theta).det` and
  `forall theta p, IsUnit ((A1passive theta p).det)`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive block coordinates and p.13
source chart.  The Lean proof is elementary finite-coordinate continuity plus
already-landed continuity of endpoint transport and the fixed-base
retained-passive source chart.

## Deferred

- Construction of a concrete passive product measure.
- Turning continuity into a concrete `AEMeasurable` theorem for a specific
  source measure.
- Source-rank support for such a concrete measure.
- Source-image equality, local inverse, or local coverage for arbitrary source
  points.
- Determinant-chart pushforward, passive Jacobian, bounded-unit density
  accounting, or original source-prior transport.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probes for both theorem names report
`[propext, Classical.choice, Quot.sound]`.
Independent xhigh review by `Nash the 3rd` passed after two docstring wording
fixes; see `review-a2-case2-passive-source-chart-continuity.md`.

## Nonclaims

This card does not prove a product-measure construction, source-rank coverage,
source-image equality, determinant-chart Haar pushforward, raw-Haar transport,
source-prior transport, Jacobian transport, normal crossings, pole order, or
RLCT.
