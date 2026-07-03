# A2 matrix-entry following-factor local patch

Date: 2026-07-02.

## Pen-and-paper reproduction

Fix a following factor

```text
F0 : Matrix ι τ R
```

and an equivalence

```text
e : τ ≃ ι.
```

The square reindexed following factor is

```text
A(F) = F.submatrix id e.symm.
```

Assume `det A(F0)` is a unit.  The determinant-unit locus

```text
{F | IsUnit (det A(F))}
```

is a neighborhood of `F0`, because determinant is a polynomial in matrix
entries and the unit locus in `R = ℝ` is open.

Define the inverse-square-sum function

```text
B(F) =
  sum_{(a,b) in τ × ι}
    (((A(F))^(-1)).submatrix e id a b)^2.
```

At `F0`, this is finite and nonnegative.  Set

```text
K = B(F0) + 1.
```

Then `0 < K` and `B(F0) < K`.  Use the strict sublevel set

```text
{F | B(F) < K}
```

to force a uniform inverse square-sum bound on the patch.

For finite measure, use an entrywise coordinate box rather than a metric ball
on matrix space:

```text
matrixEntryBox(F0, R) =
  {F | for all i,j, F_ij in (F0_ij - R, F0_ij + R)}.
```

For `R = 1`, this box contains `F0`, is measurable, and has finite
`matrixEntryReferenceMeasure` mass.  Indeed, after identifying a matrix with
the Pi type `ι → τ → ℝ`, the box is the nested product

```text
Π_i Π_j (F0_ij - 1, F0_ij + 1),
```

so `Measure.pi_pi` and `Real.volume_Ioo` reduce its measure to a finite
product of finite real interval lengths.

Take the following patch to be

```text
matrixEntryBox(F0, 1)
  ∩ {F | IsUnit (det A(F))}
  ∩ {F | B(F) < K}.
```

Then:

- `F0` lies in the patch;
- the patch is open;
- the patch is measurable;
- its `matrixEntryReferenceMeasure` mass is finite, by monotonicity from the
  entrywise box;
- every patch point has `IsUnit (det A(F))`;
- every patch point has `B(F) ≤ K`.

These are exactly the determinant-chart hypotheses consumed by the finite
following-factor product-residual theorem.

## Lean targets

The reusable matrix-entry box helpers are:

```text
matrixEntryBox
mem_matrixEntryBox_self
measurableSet_matrixEntryBox
isOpen_matrixEntryBox
matrixEntryReferenceMeasure_matrixEntryBox_lt_top
```

The original generic following-factor patch theorem is:

```text
exists_matrixEntryReferenceMeasure_finite_followingPatch_of_reindexed_det_isUnit
```

It returns `followingPatch` and `K` with:

```text
0 < K
F0 ∈ followingPatch
MeasurableSet followingPatch
matrixEntryReferenceMeasure ι τ followingPatch < ∞
∀ F ∈ followingPatch, IsUnit ((F.submatrix id e.symm).det)
∀ F ∈ followingPatch, inverseSquareSum(F) ≤ K
```

The open strengthening is:

```text
exists_matrixEntryReferenceMeasure_finite_open_followingPatch_of_reindexed_det_isUnit
```

It returns the same data and additionally:

```text
IsOpen followingPatch
```

The with-following cylinder helper is:

```text
isOpen_case2PassiveThetaWithFollowingFactor_followingPatchCylinder
```

It allows later source-chart arguments to shrink an open set by the cylinder
`{z | z.2 ∈ followingPatch}`.

The Case 2 consumer wrapper is:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_base_reindexed_det_isUnit
```

It specializes the generic patch theorem to the following factor

```text
Matrix (Case2ResidualColIndex n S (J+1)) τ ℝ
```

and then applies the determinant-chart finite patch theorem to obtain a.e.
positivity and finite negative-power integrability for the p.13 product
residual over the restricted following-patch source measure.

## Boundary

This is not yet the source-chart/original-prior theorem.  It constructs a
finite open measurable following-factor patch from a base determinant-unit
following factor, but it does not derive that determinant condition from
`case2PassiveThetaWithFollowingFactorDetSector`.  That sector constrains the
passive theta fields and imposes no determinant condition on the independent
free following factor.

The construction also does not prove positive patch mass, source-prior
transport, original-prior transport, normal crossings, pole order, or RLCT
extraction.
