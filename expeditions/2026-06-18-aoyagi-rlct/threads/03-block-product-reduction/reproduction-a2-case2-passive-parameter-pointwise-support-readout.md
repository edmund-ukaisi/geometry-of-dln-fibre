# Reproduction - A2 Case 2 Passive-Parameter Pointwise Support Readout

Date: 2026-06-29.

Status: controller reproduction for a pointwise passive-sector support/readout
package.  This is finite retained-passive source bookkeeping, not coverage or
measure transport.

## Question

After the passive-parameter fixed-base source map is available, can each
constructed passive-selected-entry source point be certified to lie in the
specified source-rank stratum and have residual coordinate map equal to the
selected-entry chart coordinates?

Answer: yes, pointwise and under explicit hypotheses.  For
`z = (theta, y)`, use the retained-passive datum

```text
data(z) =
  endpointTransport e
    (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (A1passive theta) (F2 theta) (A3passive theta)
      (Ctop theta) (F3 theta) y eNext).
```

The source point is

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData data(z).
```

If `Ctop theta` and every `A1passive theta p` have unit determinant, then
`data(z)` is in the determinant chart.  If the base-product rank and intended
edge ranks are supplied by

```text
finrank range(paperTotalMap W2 B2) = r
r + card tau = rEdge 0
r + rank(successorSelectedEntryMatrix y) = rEdge 1,
```

then `sourceChart z` lies in the named source-rank stratum, lies in the
retained-passive p.13 local source, and its residual coordinate map is

```text
CenterCoord.chartMap pivotNext y.
```

## Calculation

The retained-passive rank formula gives, on the determinant chart,

```text
rank(edgeMatrix p) = rank(U0) + rank(C p).
```

The complement hypothesis and base-product rank identify `rank(U0)` with the
supplied rank `r` through the already-proved fixed-base source-rank
constructor.  The passive fields affect the edge matrices, but the rank
calculation passes through the stored `C` factors.

For the two Case 2 `C` factors:

```text
rank(C 0) = card tau
rank(C 1) = rank(case2SuccessorSelectedEntryMatrix y).
```

These equalities are the same finite Case 2 block-rank calculations used by
the reduced selected-entry source theorem, because
`case2PostPivotSelectedEntryRetainedPassiveDataWithPassive` keeps the same
stored residual `C` family as the reduced datum.  Endpoint transport preserves
the `C` ranks by reindexing rows and columns.

The residual-coordinate readout is the direct consequence of the previous
source-readback bridge:

```text
residualFactorProduct (sourceReadback(edgeMatrices(sourceChart z))).C
  = CenterCoord.chartMap pivotNext y
```

and the generic retained-passive residual-coordinate-map bridge.

## Lean Verification

New Lean declarations:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

Location:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

## Hypotheses

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and residual-column equivalence `eNext`.
- Passive field families `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- Determinant-unit hypotheses on `Ctop` and `A1passive`.
- Pointwise rank hypotheses `hprod`, `hr0`, and `hr1`.

## Kill Conditions

- Do not read pointwise source-rank membership as source-rank coverage.
- Do not read the constructed image as all nearby source points or all of the
  retained-passive source-family set.
- Do not infer a determinant-chart pushforward, raw-Haar transport, or
  original source-prior transport.
- Do not drop the determinant-unit hypotheses on `Ctop` and `A1passive`.
- Do not drop the pointwise successor-rank hypothesis `hr1`.
- Keep normal-crossing-to-RLCT extraction as the cited analytic boundary.

## Next Boundary

This pointwise package can feed a chart-produced passive-sector measure support
theorem.  It still does not construct a full passive coordinate product
measure, local image/coverage theorem, or passive Jacobian/source-prior
transport.
