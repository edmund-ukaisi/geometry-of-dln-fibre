# Statement Card - A2 Case 2 Passive-Parameter Fixed-Base Source Readback

Status: PASS.  Sorry-free focused build, controller review, and xhigh
read-only review complete.

Reproduction:

```text
reproduction-a2-case2-passive-parameter-fixed-base-source-readback.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Claim

The endpoint-transported Case 2 passive-parameter retained-passive datum gives
a fixed-base p.13 source edge family on the domain
`eta x (center -> R)`.  Under the supplied determinant-unit hypotheses on
`Ctop` and `A1passive`, every point lands in the retained-passive local source,
and source readback of the realized edge matrices has residual factor product
equal to the selected-entry center-coordinate matrix.

## Lean

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
```

## Gloss

For passive field families indexed by `eta` and selected-entry coordinates
`y`, Lean constructs

```text
sourceChart (theta,y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    (endpointTransport e
      (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive ... theta y)).
```

The theorem proves two pointwise facts for all `(theta,y)`: this source edge
family lies in the retained-passive p.13 local source, and source readback of
its fixed-base edge matrices has residual factor product equal to the
selected-entry chart matrix.

## Proved

- A passive-parameter fixed-base source chart is defined pointwise from
  retained-passive data.
- The source chart lands in the retained-passive local source under explicit
  determinant-unit hypotheses.
- Fixed-base source readback recovers the retained-passive datum.
- The recovered residual factor product is the selected-entry center-coordinate
  matrix and is independent of the passive fields except through the
  determinant-chart landing hypotheses.

## Assumed

- Endpoint equivalences `e` and residual-column equivalence `eNext`.
- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Passive field families indexed by an arbitrary type `eta`.
- Unit hypotheses `forall theta, IsUnit (Ctop theta).det` and
  `forall theta p, IsUnit ((A1passive theta p).det)`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive block/product fields and the
p.13 residual product display.  The Lean proof itself is finite fixed-base
coordinate algebra and source-readback bookkeeping.

## Deferred

- Source-image equality or local coverage of arbitrary nearby source points.
- Measure pushforward from passive-selected-entry coordinates.
- Passive Jacobian or bounded-unit density accounting.
- External/original source-prior transport.
- Normal crossings, pole order, and RLCT extraction.

## Route

Use the passive-parameter datum from the previous card.  Determinant-chart
membership gives source-recursive determinant-chart membership for its edge
matrix.  Fixed-base realization by
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData` has exactly
that edge matrix, so source readback returns the datum.  The residual readout
then follows from the passive-parameter endpoint-transported selected-entry
residual theorem.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

Direct axiom probe for the theorem reports only
`[propext, Classical.choice, Quot.sound]`.

## Review

Review passed with no findings:

```text
review-a2-case2-passive-parameter-fixed-base-source-readback.md
```

## Nonclaims

This card does not prove selected-entry image coverage, source-rank coverage,
the determinant-chart pushforward
`m.restrict Sdet = Measure.map chart weightedBox`, full raw-Haar transport,
source-prior transport, normal crossings, pole order, or RLCT.
