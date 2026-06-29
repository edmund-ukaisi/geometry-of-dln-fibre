# Statement Card - A2 Case 2 Passive-Parameter Pointwise Support Readout

Status: sorry-free focused build; direct axiom probe passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-case2-passive-parameter-pointwise-support-readout.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

The passive-parameter Case 2 fixed-base source chart has a pointwise
source-rank/local-source/residual-readout package.  Under explicit
determinant-unit hypotheses on `Ctop` and `A1passive`, and under supplied
pointwise rank equations, every constructed point `z = (theta, y)` lies in the
specified source-rank stratum and retained-passive p.13 local source, and its
fixed-base residual coordinate map is the selected-entry center-coordinate
chart map at `y`.

## Lean

```text
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

## Proved

- The constructed passive source point lies in the named source-rank stratum
  under `hprod`, `hr0`, and the pointwise successor-rank hypothesis `hr1`.
- The constructed passive source point lies in the retained-passive p.13 local
  source under the `Ctop` and `A1passive` determinant-unit hypotheses.
- The fixed-base residual coordinate map of the constructed source point is
  `SelectedEntrySignedBox.CenterCoord.chartMap pivotNext y`.
- The passive fields do not alter the selected-entry residual readout; they
  enter the support proof only through determinant-chart membership and the
  retained-passive edge matrices.

## Assumed

- Endpoint equivalences `e` and residual-column equivalence `eNext`.
- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Passive field families indexed by an arbitrary type `eta`.
- Unit hypotheses `forall theta, IsUnit (Ctop theta).det` and
  `forall theta p, IsUnit ((A1passive theta p).det)`.
- Rank hypotheses `hprod`, `hr0`, and pointwise `hr1`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive block/product fields and the
p.13 residual product display.  The Lean proof itself is finite
retained-passive rank/readback bookkeeping built from already-landed source
and selected-entry coordinate lemmas.

## Deferred

- Source-rank coverage of arbitrary nearby source points.
- Source-image equality or local coverage of the passive-selected-entry sector.
- Measure pushforward from passive-selected-entry coordinates.
- Passive Jacobian or bounded-unit density accounting.
- External/original source-prior transport.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

Direct axiom probe reports `[propext, Classical.choice, Quot.sound]`.
Independent xhigh review by `Kuhn the 3rd` passed with no findings; see
`review-a2-case2-passive-parameter-pointwise-support-readout.md`.

## Nonclaims

This card does not prove source-rank coverage, selected-entry image coverage,
the determinant-chart pushforward
`m.restrict Sdet = Measure.map chart weightedBox`, full raw-Haar transport,
source-prior transport, normal crossings, pole order, or RLCT.
