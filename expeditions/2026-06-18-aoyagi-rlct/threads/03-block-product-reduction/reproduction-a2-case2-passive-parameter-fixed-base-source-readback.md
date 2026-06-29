# Reproduction - A2 Case 2 Passive-Parameter Fixed-Base Source Readback

Date: 2026-06-29.

Status: controller reproduction for the fixed-base source-map/readback bridge
following the passive-parameter selected-entry datum.  This is still finite
coordinate algebra and fixed-base source realization, not a measure theorem.

## Question

After the passive-parameter retained-passive datum is available, can we build a
fixed-base p.13 source edge family from passive parameters and selected-entry
residual coordinates, and prove that source readback recovers the same
selected-entry residual matrix?

Answer: yes.  For a passive parameter `theta : eta` and selected-entry
coordinates `y : center -> R`, form the endpoint-transported retained-passive
datum

```text
data(theta,y) =
  endpointTransport e
    (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (A1passive theta) (F2 theta) (A3passive theta)
      (Ctop theta) (F3 theta) y eNext).
```

Then realize it as a fixed-base source edge family by

```text
sourceChart(theta,y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData data(theta,y).
```

If the supplied passive blocks satisfy

```text
IsUnit (Ctop theta).det
forall p, IsUnit ((A1passive theta p).det),
```

then `sourceChart(theta,y)` lies in the retained-passive p.13 local source,
and source readback of its fixed-base edge matrices has residual factor
product equal to the selected-entry center-coordinate matrix.

## Source Calculation

Aoyagi pp. 10-13 justify the retained-passive finite fields through the same
block/product formulas used in the previous card:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4,
```

and the p.13 product-difference display

```text
[ C1 - I        -F2
  -F3    prod C^(s) - F3 F2 ].
```

This reproduction uses only the elementary consequence that the selected-entry
singular residual is read from the stored residual `C` factors.  The passive
fields are carried through the source realization but do not enter the
selected-entry residual matrix.

## Coordinate Domain

The source-chart domain is deliberately larger than the reduced
selected-entry section:

```text
eta x (center -> R).
```

Here `eta` is an abstract passive-parameter type.  The theorem receives field
families

```text
A1passive : eta -> Fin 1 -> Matrix rho rho R
F2        : eta -> forall p : Fin 2, Matrix rho (old domain p) R
A3passive : eta -> forall p : Fin 1, Matrix (old domain p.succ) rho R
Ctop      : eta -> Matrix rho rho R
F3        : eta -> Matrix (old terminal domain) rho R
```

and the selected-entry coordinates supply only the residual `C` family.

This is a genuine source-map/readback step beyond the reduced section: the
source family now depends on passive variables.  It is not yet an image theorem
for all nearby source points.

## Proof Skeleton

For each point `z = (theta,y)`:

1. Determinant-chart membership of `data z` follows from
   `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart`
   and the supplied unit hypotheses on `Ctop theta` and `A1passive theta`.
2. The fixed-base source edge family is defined by
   `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData`.
3. Its fixed-base edge-matrix extraction is exactly `data z.edgeMatrix` by
   `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq`.
4. Source readback recovers `data z` by
   `sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq`.
5. The residual factor product of `data z.C` is the selected-entry
   center-coordinate matrix by
   `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`.

Combining these gives both outputs:

```text
sourceChart z in retainedPassiveP13LocalSource
```

and

```text
residualFactorProduct (sourceReadback(edgeMatrices(sourceChart z))).C
  = selectedEntry center-coordinate matrix y.
```

## Lean Verification

New Lean declaration:

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
```

Location:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

The theorem was placed next to the existing zero-passive Case 2 fixed-base
source/readback bridge, because the surrounding file already hosts the
Case 2 endpoint-transported fixed-base local-source inputs consumed by the
local-measure layer.  It does not add an integrability wrapper.

## Kill Conditions

- Reject any reading of this theorem as source-image equality or coverage.
- Reject any use as the determinant-chart pushforward
  `m.restrict Sdet = Measure.map chart weightedBox`.
- Reject any source-prior or Jacobian transport claim from this theorem alone.
- Reject any proof that drops the `Ctop` and `A1passive` unit hypotheses.
- Reject any statement that lets passive fields alter the selected-entry
  residual exponent.
- Keep normal-crossing-to-RLCT extraction as the cited analytic boundary.

## Next Boundary

This theorem gives a passive-coordinate source map and readback identity.  The
next source-measure boundary remains:

- continuity/measurability of a concrete passive-coordinate chart if a measure
  theorem needs it;
- an image or local coverage theorem for the passive-selected-entry source
  sector;
- Jacobian/passive-unit measure accounting;
- comparison with an external or original source prior, if that prior is to be
  used.
