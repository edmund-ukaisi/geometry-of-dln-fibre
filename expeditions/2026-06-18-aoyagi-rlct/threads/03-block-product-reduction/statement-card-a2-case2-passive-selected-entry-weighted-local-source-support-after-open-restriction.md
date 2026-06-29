# Statement Card - A2 Case 2 Passive Selected-Entry Weighted Local Source Support After Open Restriction

Status: sorry-free focused build and full aggregator build passed; direct
axiom probe passed; xhigh reviews PASS.

Reproduction:

```text
reproduction-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
lean/DLNFibre.lean
```

## Claim

For passive selected-entry Case 2 coordinates, continuity of the passive fields
and determinant-unit hypotheses at one base point produce an open determinant
domain `U`.  For any source-domain measure and any density on the selected-
entry coordinate domain, the pushforward of the weighted restricted measure

```text
(sourceMeasure.restrict U).withDensity density
```

along the fixed-base p.13 source chart is supported on the retained-passive
p.13 local source.

## Lean

```text
exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
```

## Proved

- The open set `U` is inherited from
  `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq`.
- For each `z in U`, the theorem retains pointwise local-source membership
  and source readback of extracted edge matrices.
- The source chart is continuous on `U`, hence a.e. measurable for
  `sourceMeasure.restrict U`.
- `withDensity_absolutelyContinuous` transfers a.e. measurability from
  `sourceMeasure.restrict U` to
  `(sourceMeasure.restrict U).withDensity density`.
- The same absolute-continuity statement transfers the a.e. local-source
  membership supplied by `ae_restrict_mem`.
- The generic support helper
  `measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem`
  proves

```text
let weighted := (sourceMeasure.restrict U).withDensity density
(Measure.map sourceChart weighted).restrict localSource
  =
Measure.map sourceChart weighted.
```

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Basepoint determinant units for `Ctop z0.1` and `A1passive z0.1`.
- An arbitrary source-domain measure `sourceMeasure`.
- An arbitrary density
  `density : eta x (center -> R) -> ENNReal`.
- Borel/measurable-space structure on the source edge-family type when
  stating the support conclusion.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive p.13 block coordinates and
source chart.  The Lean proof is elementary finite-coordinate topology and
measure-support bookkeeping, plus Mathlib absolute continuity for
`withDensity`.

## Deferred

- Identifying `density` with a Jacobian factor.
- Global determinant-unit hypotheses away from the constructed open set.
- Selected-entry source-image equality or local coverage for arbitrary source
  points.
- Source-rank support or source-rank coverage.
- Determinant-chart Haar pushforward, raw-Haar transport, or source-prior
  transport.
- Jacobian change-of-variables or exact localized residual marginal.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure
```

Full aggregator build passed:

```text
scripts/lb DLNFibre
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Independent xhigh reviews by `Nietzsche the 3rd` and `Schrodinger the 3rd`
passed; see
`review-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md`.

## Nonclaims

This card does not prove the density is a Jacobian, source-image equality,
source-rank support or coverage, determinant-chart Haar pushforward, raw-Haar
transport, source-prior transport, Jacobian transport, exact localized
residual marginal, normal crossings, pole order, or RLCT.
