# A2 finite-passive source following-patch integrability

Date: 2026-07-02.

## Pen-and-paper reproduction

Fix a full with-following Case 2 passive-theta point

```text
z0 : Case2PassiveThetaWithFollowingFactor n S J.
```

Write the independent following factor as `F0 = z0.2`.  The determinant
condition needed for the local following patch is a separate hypothesis:

```text
IsUnit ((F0.submatrix id eNext.symm).det).
```

It is not a consequence of
`case2PassiveThetaWithFollowingFactorDetSector`; that sector only constrains
the passive-theta fields in `z0.1`.

The matrix-entry local-patch theorem applied to `F0` gives a measurable finite
patch

```text
s : Set (Matrix (Case2ResidualColIndex n S (J+1)) tau R)
```

and a constant `K > 0`, with `F0 in s`, determinant-unit on `s`, and a uniform
bound for the reindexed inverse square-sum on `s`.  The finite-patch product
residual theorem then gives a.e. positivity and finite negative-power integral
for the p.13 product residual with respect to

```text
((passiveMeasure.prod weightedBox).prod (followingRef.restrict s)).
```

Here

```text
passiveMeasure is an arbitrary finite measure on passive fields,
weightedBox  = case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres,
followingRef = matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J+1)) tau.
```

The global named with-following reference source is definitionally

```text
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres
  = (passiveRef.prod weightedBox).prod followingRef,
```

where `passiveRef` is the coordinate-product reference measure on passive
fields.  That global passive reference is not known to have finite total mass,
so the finite-integral wrapper must not silently specialize the finite
`passiveMeasure` hypothesis to `passiveRef`.

For this rung, define the finite-passive product source

```text
productSource = (passiveMeasure.prod weightedBox).prod followingRef.
```

Let the following-patch cylinder in the full source be

```text
S_source = {z | z.2 in s}.
```

Since the full source type is the product of passive theta and the following
matrix, this cylinder is `Set.univ × s`.  Therefore product restriction gives

```text
productSource.restrict S_source
  = (passiveMeasure.prod weightedBox).prod (followingRef.restrict s).
```

by `Measure.restrict_prod_eq_prod_univ` or equivalently
`Measure.prod_restrict` plus `Set.univ` simplification.

Thus the finite-patch product-residual theorem can be restated over the
finite-passive product source restricted to `S_source`.  If this is later
combined with the source-chart theorem, the source-chart theorem's arbitrary
`sourceMeasure` parameter can be instantiated with this restricted source
measure and then shrunk to the returned open set `V`.

## Lean targets

First prove the measure bookkeeping lemma:

```text
case2PassiveThetaWithFollowingFactor_productSourceMeasure_restrict_followingPatch_eq_prod_restrict
```

Expected statement:

```text
((passiveMeasure.prod weightedBox).prod followingRef)
    .restrict {z | z.2 in followingPatch}
 =
  (passiveMeasure.prod weightedBox).prod (followingRef.restrict followingPatch)
```

Mathematically this is pure product restriction bookkeeping.  The Lean proof
uses `Measure.prod_restrict`, whose local API asks for an `SFinite` instance
on the left product; the source-point wrapper supplies this from
`passiveMeasure Set.univ < infinity`.

Then prove the source-point wrapper:

```text
exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_sourceCylinder_of_base_reindexed_det_isUnit
```

It should take a base point `z0` and the separate hypothesis

```text
IsUnit ((z0.2.submatrix id eNext.symm).det)
```

while keeping the existing finite passive-side inputs

```text
passiveMeasure
passiveMeasure Set.univ < infinity.
```

It returns a patch `s`, `K > 0`, `z0.2 in s`, finite
`matrixEntryReferenceMeasure s`, determinant-unit and inverse-square-sum
bounds on `s`, plus a.e. positivity and finite negative-power integrability of
the p.13 product residual over

```text
((passiveMeasure.prod weightedBox).prod followingRef)
  .restrict {z | z.2 in s}.
```

## Boundary

This is still only a source-side finite-patch theorem.  It does not construct
an open source-chart neighborhood, does not prove positive patch mass, and does
not remove the finite passive-side measure hypothesis.  It does not identify
determinant Haar, raw Haar, source density, original prior, or source-image
coverage.  It also does not prove normal crossings, pole order, or RLCT
extraction.
