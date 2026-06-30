# Reproduction - A2 retained-passive passive-sector construction frontier

Date: 2026-06-30.

Status: controller pen-and-paper construction target; no Lean theorem is
claimed here.

## Question

Can the remaining Case 2 retained-passive determinant-chart pushforward
hypothesis be removed by another selected-entry wrapper?

The live hypothesis has the form

```text
m.restrict Sdet = Measure.map chart weightedBox
```

inside the Case 2 retained-passive local-jacobian lane, for example in

```text
retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

Here `Sdet` is the full retained-passive determinant-chart set in the
`TopologyTuple` coordinate space, while `chart` is the endpoint-transported
selected-entry center-coordinate map from the Case 2 residual block.

## Source Check

Aoyagi PDF pp. 10-13 gives the Schur/block coordinate algebra:

```text
F2 = - A1^{-1} A2
F3 = - A3 A1^{-1}
C4 = - A3 A1^{-1} A2 + A4
```

and iterates it to obtain the p.13 product-difference block

```text
[ C1 - Er, -F2 ;
  -F3, prod_s C^(s) - F3 F2 ].
```

This source material supports the retained-passive coordinate chart and the
residual/loss readout.  It does not state a measure pushforward from the
selected-entry signed-box coordinates to full determinant-chart Haar measure,
nor an external/original source-prior theorem.

## Dimension And Measure Obstruction

The reduced selected-entry chart varies only the residual selected-entry
center coordinates:

```text
center -> R
```

It fixes or suppresses the passive coordinates carried by the retained-passive
p.13 chart.  Therefore the equality

```text
m.restrict Sdet = Measure.map chart weightedBox
```

cannot be proved from the reduced selected-entry chart unless `Sdet` has been
redefined to be the selected-entry image sector.  In the current Lean theorem
it has not: `Sdet` is still the full determinant-chart set for the
retained-passive topology tuple.  A lower-dimensional selected-entry image
cannot replace full determinant-chart Haar measure.

## Existing Lean Bedrock

The retained-passive chart layer already proves the chart-side
change-of-variables theorem:

```text
measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
```

This identifies the direct determinant-chart retained-passive source measure
with the raw-order source-chart measure with inverse-Jacobian density.  It is
not an original source-prior theorem and it does not fill the selected-entry
Case 2 signed-box pushforward hypothesis.

Lean also has the raw-order image/support infrastructure:

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_homeomorph
image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_sourceEdgeFamilySet_eq_self
measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_restrict_sourceEdgeFamilySet
```

These are useful for a full passive-sector theorem, but they do not by
themselves add the missing passive variables to the Case 2 selected-entry
signed-box measure.

## Required Construction

The next source-moving theorem should introduce a passive-sector coordinate
domain, provisionally:

```text
Case2PassiveTheta
```

with coordinates consisting of:

- the selected-entry residual center coordinates used by the current Case 2
  signed box;
- the passive retained p.13 coordinates suppressed by the reduced
  selected-entry section.  In the existing Lean passive datum these fields are
  exactly `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`;
- a nonzero-pivot or small-box sector condition ensuring the determinant chart
  and selected pivot hypotheses.

It should define a map

```text
case2PassiveThetaTopologyTuple :
  Case2PassiveTheta -> TopologyTuple rho kappa' R
```

whose source chart is

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  (ofTopologyTuple (case2PassiveThetaTopologyTuple theta)).
```

The corresponding sector is

```text
case2PassiveThetaSectorSet =
  case2PassiveThetaTopologyTuple '' thetaDomain
```

or, if Lean measure APIs prefer it, a predicate on `TopologyTuple` stating
exactly that the tuple has the selected-entry coordinates in the signed box
and passive coordinates in their retained passive boxes.

## Measure Target

The strongest useful target is an exact sector pushforward:

```text
Measure.map case2PassiveThetaTopologyTuple thetaMeasure
  = m.restrict case2PassiveThetaSectorSet
```

possibly with an explicit bounded positive density:

```text
Measure.map case2PassiveThetaTopologyTuple
  (thetaProductMeasure.withDensity passiveUnitDensity)
  = m.restrict case2PassiveThetaSectorSet.
```

If exact equality is too rigid for the existing measure APIs, the useful
weaker target is a finite-scalar domination or bounded-density comparison in
the direction needed by the finite-integral consumer:

```text
m.restrict case2PassiveThetaSectorSet
  <= C • Measure.map case2PassiveThetaTopologyTuple thetaMeasure
```

for local integrability transfer from the theta-product side to the
determinant-chart side.  Bare mutual absolute continuity is not enough here:
it transfers a.e. positivity but not finiteness of an unbounded negative-power
integral.

The old target

```text
m.restrict Sdet = Measure.map chart weightedBox
```

should not be pursued for the reduced selected-entry `chart`; it is the wrong
dimensional statement.

## Proposed Lean Module Boundary

After this construction is sharpened, the Lean module should be separate from
the existing wrappers, for example:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
```

Likely public names:

```text
Case2PassiveTheta
case2PassiveThetaTopologyTuple
case2PassiveThetaSourceChart
case2PassiveThetaDetSector
case2PassiveThetaPivotSector
case2PassiveThetaMeasure
measure_map_case2PassiveThetaTopologyTuple_eq_restrict_sectorSet
```

## Nonclaims

This note does not prove a Lean theorem.  It does not identify the original
DLN source prior, prove source-rank coverage, prove determinant-chart Haar
transport from the reduced selected-entry section, construct normal crossings,
compute pole order, or extract RLCT.  It only fixes the next construction
boundary: add passive variables first, then prove a sector measure theorem.
