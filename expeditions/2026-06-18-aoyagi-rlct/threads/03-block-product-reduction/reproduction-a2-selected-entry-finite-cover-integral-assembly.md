# Reproduction - A2 selected-entry finite-cover integral assembly

Date: 2026-06-26.

Status: controller pen-and-paper reproduction before Lean.  This is finite
selected-entry source-coordinate measure bookkeeping.  It is not a source
stratum coverage theorem.

## Source/Boundary Anchor

The input geometry is the finite selected-entry sector cover already reproduced
in `reproduction-a2-selected-entry-finite-sector-cover.md`:

```text
signedBoxSet S subset union_p chartMap p '' signedBoxSet R
```

under `S_i <= R_i` and `1 < R_i`.  The analytic source chart, original
source-measure transport, normal crossings, pole order, and RLCT extraction
are not part of this step.

## Pen-And-Paper Check

For each pivot `p`, suppose the fixed-pivot selected-entry chart-image
finite-integral theorem gives an open set `U_p` with `0 in U_p` and

```text
int f d((volume.restrict (U_p inter I_p)).prod nu) < infinity,
I_p = chartMap p '' signedBoxSet R.
```

Set

```text
U = intersection_p U_p.
```

The center set is finite, so `U` is open, and `0 in U` because `0 in U_p` for
every pivot.

The sector cover gives

```text
signedBoxSet S subset union_p I_p.
```

Therefore

```text
U inter signedBoxSet S subset union_p (U_p inter I_p).
```

Indeed, if `x in U inter signedBoxSet S`, choose `p` with `x in I_p`; since
`x in U`, also `x in U_p`.

Now let `s = U inter signedBoxSet S` and `t_p = U_p inter I_p`.  For a
nonnegative integrand `f : alpha x beta -> ENNReal`, the product-measure
restriction rewrites as

```text
(mu.restrict s).prod nu = (mu.prod nu).restrict (s x univ).
```

Because `s subset union_p t_p`,

```text
s x univ subset union_p (t_p x univ).
```

Thus monotonicity of the lower integral and `lintegral_iUnion_le` give

```text
int f d((mu.restrict s).prod nu)
  <= int f d((mu.prod nu).restrict (union_p (t_p x univ)))
  <= sum_p int f d((mu.restrict t_p).prod nu).
```

The pivot set is finite, and every summand is finite by the fixed-pivot
theorem, so the finite sum is finite.  This proves the finite integral over
`U inter signedBoxSet S`.

For the original square-Frobenius loss wrapper, use the existing finite
endpoint comparison constant `c0 > 0`:

```text
c0 * adaptedProductDifferenceSquareSum <= lossDLN.
```

Combining it with each supplied adapted lower bound gives the selected-entry
finite-cover theorem the required lower bound for the concrete `lossDLN`
integrand, with constant `c0 * creg`.

## Lean Target

Add in `SelectedEntrySignedBoxLocalMeasure.lean`:

```text
lintegral_prod_restrict_lt_top_of_subset_iUnion_finite
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix
```

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## Boundary

- Finite all-pivot selected-entry coordinate cover plus measure bookkeeping.
- The basepoint is `0`, because every selected-entry chart image contains the
  origin.
- Per-pivot local loss, residual readout, density, and edge-matrix hypotheses
  remain explicit.
- No source-rank-stratum equality or coverage.
- No source-measure transport from original DLN coordinates.
- No analytic source chart or Jacobian-density construction.
- No normal-crossing production, pole-order theorem, or RLCT extraction.
