# Reproduction - A2 selected-entry finite-cover source-stratum restriction

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean.  This is a
restriction of the finite selected-entry sector-cover integral to a supplied
local source-rank subset.  It is not a source-chart coverage theorem.

## Source/Boundary Anchor

The source-backed input is the finite selected-entry sector cover:

```text
signedBoxSet Sres subset union_p chartMap p '' signedBoxSet Rres
```

under `Sres_i <= Rres_i` and `1 < Rres_i`.  The existing original-loss
finite-cover theorem already combines this cover with the per-pivot
selected-entry residual readout, adapted-loss lower bounds, and density bounds.

The new step does not identify the p.13 source-rank stratum with a
selected-entry chart image.  It assumes only a local inclusion into the smaller
signed box:

```text
Ulocal inter sourceStratum subset Ulocal inter signedBoxSet Sres.
```

## Pen-And-Paper Check

Let

```text
S = sourceStratum,
B = signedBoxSet Sres.
```

The finite-cover original-loss theorem gives an open set `Ubox` with
`0 in Ubox` and

```text
int f d((volume.restrict (Ubox inter B)).prod nu) < infinity.
```

Assume `Ulocal` is open, `0 in Ulocal`, and

```text
Ulocal inter S subset Ulocal inter B.
```

Set

```text
U = Ubox inter Ulocal.
```

Then `U` is open and contains `0`.  If `x in U inter S`, then `x in Ubox`,
`x in Ulocal`, and `x in S`; the local inclusion gives `x in B`.  Hence

```text
U inter S subset Ubox inter B.
```

For the nonnegative integrand `f`, product-measure monotonicity gives

```text
int f d((volume.restrict (U inter S)).prod nu)
  <= int f d((volume.restrict (Ubox inter B)).prod nu)
  < infinity.
```

This proves the source-stratum restricted finite integral.

## Lean Target

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## Boundary

- The source-rank stratum is only restricted by an explicit local subset
  hypothesis.
- The theorem does not prove local source-rank coverage, chart image equality,
  source-prior transport, Jacobian compatibility, normal crossings, pole order,
  or RLCT.
- The per-pivot selected-entry residual readout, adapted-loss lower bounds,
  and density bounds remain explicit.
