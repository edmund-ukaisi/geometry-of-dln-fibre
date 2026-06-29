# Reproduction - A2 retained-passive source-edge-family chart-produced source-stratum two-sided iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised.

## Source Anchor

This is the retained-passive source-edge-family-of-data specialization of the
chart-produced source-stratum selected-entry two-sided p.13 loss-density iff.
It is concrete chart bookkeeping for Aoyagi's retained-passive p.13 source
chart, not a source-prior transport theorem or a residual-integrability
theorem.

## Calculation

Let

```text
EdgeFamily := forall p, reverseVertex p.castSucc ->L[Real] reverseVertex p.succ,
base p := reverseEdge p,
sourceChart y :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U0 hU0 (retainedData y).
```

The retained data live in the determinant-chart subtype

```text
DetData := {data : RetainedPassiveNonredundantCoordinateData // data.detChart}.
```

The theorem assumes a.e. measurability of

```text
fun y => (retainedData y, hdet y) : DetData
```

for the unweighted selected-entry signed box.  The retained-passive p.13 source
chart is continuous from `DetData` to `EdgeFamily`, so the concrete
`sourceChart` is a.e. measurable for the signed box.

The retained-passive source-edge-family readback theorem gives, for every
`y`,

```text
sourceChart y in retainedPassiveP13LocalSource
```

and identifies the retained source-readback residual factor product with the
selected-entry residual matrix.  The residual square-sum bridge converts this
to the selected-entry residual readout

```text
residualSquareSum(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

These are exactly the three concrete inputs needed by the chart-produced
source-stratum selected-entry two-sided theorem.

All analytic and comparison content remains supplied:

```text
residualSquareSum x <= Rreg^2
```

for a.e. `x` with respect to the chart-produced measure restricted to the
retained-passive local source, and four source-stratum eventual bounds

```text
cLreg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
loss(x,u) <= CLreg * (residualSquareSum(x) + regularSquareSum(u)),
dRho <= density(x,u),
density(x,u) <= DRho.
```

The conclusion is an open `U` around `base` with

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu < infinity
iff
residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t.
```

## Lean Shape

Lean formalises this in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Main theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

The proof:

1. composes the retained-data a.e. measurable map with the continuous
   retained-passive p.13 source chart to obtain `hsourceChart`;
2. obtains local-source landing and source-readback matrix equality from
   `retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData`;
3. obtains the selected-entry residual readout from the square-sum readout
   bridge;
4. applies the chart-produced source-stratum selected-entry two-sided iff.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

passed after the Lean change.

## Nonclaims

- No proof of residual boundedness or the four source-stratum comparison
  bounds.
- No selected-entry critical inequality, positive signed-box-radius, or
  residual integrability conclusion.
- No signed-box source/image equality, source-rank coverage, or chart atlas
  construction.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No original-loss identification.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
