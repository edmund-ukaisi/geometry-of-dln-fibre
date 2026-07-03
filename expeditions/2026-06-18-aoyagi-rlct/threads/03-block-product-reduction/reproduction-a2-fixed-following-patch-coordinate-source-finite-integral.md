# A2 fixed-following-patch coordinate-source finite integral

Date: 2026-07-03.

## Calculation

The previous open coordinate-source handoff returns an open following patch and
then leaves the local containment

```text
V subset {z | z.2 in followingPatch}
```

as a continuation.  To compose with a source-chart shrink that must use the
same patch, first factor out the supplied-patch calculation.

Fix a following patch `P` and a constant `K`.  Assume:

```text
MeasurableSet P,
matrixEntryReferenceMeasure P < infinity,
forall F in P, det (F.submatrix id eNext.symm) is a unit,
forall F in P, inverse_square_sum(F) <= K.
```

Let `V` be any measurable local source set contained in both cylinders

```text
V subset {z | z.1.1 in passiveLocalSet},
V subset {z | z.2 in P}.
```

If

```text
passiveRef.restrict passiveLocalSet <= Cpassive • passiveMeasure,
passiveMeasure univ < infinity,
Cpassive < infinity, CJ < infinity, CS < infinity,
```

then the reference-source cylinder domination gives

```text
referenceSource.restrict V <= Cpassive • localSourceMeasure,
```

where `localSourceMeasure` is the finite source cylinder over the same patch
`P`, restricted to `V`.  The concrete two-density handoff then gives

```text
coordinateSourceMeasure.restrict V
  <= (CS * (CJ * Cpassive)) • localSourceMeasure
```

from the a.e. Jacobian and source-density upper bounds on
`referenceSource.restrict V` and `baseJ.restrict V`.  The dominated-target
socket transfers p.13 product-residual a.e. positivity and finite
negative-power integrability from `localSourceMeasure` to
`coordinateSourceMeasure.restrict V`.

## Open-patch wrapper

For a base point `z0`, the open wrapper first uses the matrix-entry open patch
constructor on the independent following factor `z0.2`.  It then applies the
with-following source-chart shrink to the ambient open set `G` and the open
following-patch cylinder, producing an open set `V` with

```text
z0 in V,
V subset G,
V subset {z | z.2 in followingPatch}.
```

The passive containment is inherited from the explicit ambient hypothesis

```text
G subset {z | z.1.1 in passiveLocalSet}.
```

The wrapper then calls the fixed-patch theorem above.  The source-domain
opens-measurable, Borel, and Polish hypotheses are explicit and apply to the
canonical source-domain measurable structure; this avoids introducing a fresh
measurable-space instance incompatible with the concrete reference-source
measure.

## Lean targets

The fixed-patch coordinate-source theorem is:

```text
case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_of_followingPatch_passive_restrict_le_smul_and_density_bounds
```

The open-patch/open-source-neighborhood wrapper is:

```text
exists_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
```

Both are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

## Boundary

This proves no passive local comparison measure construction, no passive
local-set existence theorem, no Jacobian-density upper bound, no source-density
upper bound, no determinant-Haar/raw-Haar transport, no original-prior
transport, no normal crossings, pole order, or RLCT extraction.
