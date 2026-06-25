# Reproduction - A2 selected-entry finite sector cover

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before Lean.  This is finite
selected-entry chart geometry only, not source-stratum coverage.

## Source/Boundary Anchor

Aoyagi's displayed selected-entry substitutions use one pivot coordinate and
quotient-like off-pivot variables:

```text
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p y_i      for i != p.
```

The already-proved finite image theorem characterizes a fixed-pivot image as
the origin plus a nonzero-pivot horn.  This note records the elementary
finite-sector consequence: a smaller signed box is covered by the union of
all selected-entry chart images when the target quotient radii are strictly
larger than `1`.

## Pen-And-Paper Check

Let `S_i <= R_i` for every coordinate and assume `1 < R_i` for every target
chart radius.  Let

```text
x in B_S = { z : |z_i| < S_i for all i }.
```

If `x = 0`, then `x` lies in any selected-entry image by taking chart
coordinate `y = 0`.

If `x != 0`, choose a pivot `p` with maximal absolute coordinate:

```text
x_p != 0,
|x_i| <= |x_p|       for every i.
```

Because `x in B_S` and `S_p <= R_p`,

```text
|x_p| < S_p <= R_p.
```

For every `i != p`,

```text
|x_i / x_p| = |x_i| / |x_p| <= 1 < R_i.
```

The fixed-pivot horn characterization therefore gives

```text
x in Phi_p(B_R).
```

Hence

```text
B_S subset union_p Phi_p(B_R).
```

The strict inequality `1 < R_i` is essential for this maximal-pivot argument:
if a non-pivot coordinate ties the pivot in absolute value, the quotient has
absolute value `1`, so an open radius equal to `1` would not contain it.

## Lean Target

Add in `SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_of_pivot_abs_max
SelectedEntrySignedBox.CenterCoord.exists_pivot_abs_le_abs_of_ne_zero
SelectedEntrySignedBox.CenterCoord.exists_maxPivot_mem_chartMap_image_signedBoxSet_of_mem_signedBoxSet_ne_zero
SelectedEntrySignedBox.CenterCoord.signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt
```

## Boundary

- Finite selected-entry coordinate geometry only.
- No claim that Aoyagi prints an all-pivot analytic cover.
- No local source-stratum equality or source production.
- No fixed-base residual-product identity or residual-coordinate readout.
- No source-measure identification.
- No normal crossings, pole order, or RLCT.
