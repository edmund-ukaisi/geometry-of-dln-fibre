# Reproduction - A2 Case 2 enlarged following-factor source-to-raw block Jacobian

Date: 2026-07-02.

Status: pen-and-paper reproduction for the next source-moving density theorem.
No Lean theorem is claimed by this note.

## Source Boundary

Aoyagi Lemma 2, PDF pp. 10-11, gives the elementary Schur coordinate change
for a regular top-left block:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2.
```

Theorem 3, PDF pp. 11-13, iterates this coordinate split along a product and
separates the regular variables from the residual product of the `C(s)` blocks.
The differential-product line in the induction statement on PDF p. 15 records
the blow-up source differential as monomial factors in the `u_{s,k}` variables
times the remaining current residual-block differentials and untouched
following-factor block differentials.

In Case 2, PDF pp. 19-21, Aoyagi works on a selected-pivot chart for the
current residual block, introduces the scaling `u_{S,J+1}`, applies the
unitriangular matrix `Q` to the following block, and rewrites the following
factor as the transformed block `C'_J = Q^{-1} C_J`.  These pages justify a
local finite coordinate calculation.  They do not print a raw-map pushforward
identity, do not identify the Lean normalized following factor globally, and do
not cover all pivot charts at once.

## Lean Coordinate Model Being Reproduced

The enlarged source is

```text
Case2PassiveThetaWithFollowingFactor n S J =
  Case2PassiveTheta n S J
    x Matrix (Case2ResidualColIndex n S (J+1)) tau Real.
```

Write a source point as

```text
z = (A1passive, F2, A3passive, Ctop, F3, yNext, F).
```

The retained-data constructor is

```text
case2PassiveThetaWithFollowingFactorEndpointRetainedData z
```

obtained by endpoint-transporting

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor
  A1passive F2 A3passive Ctop F3 yNext F eNext.
```

Before endpoint transport, this constructor copies the passive fields
verbatim and sets the two active `C` factors to

```text
C = case2PostPivotFreeTwoEdgeFactorFamily
      (case2SuccessorSelectedEntrySourceResidual yNext eNext)
      (case2DisplayedPostPivotFreeCprimeOfFollowingFactor F).
```

Thus, in the untransported two-edge domain,

```text
C(0) = case2DisplayedPostPivotFreeFollowingFactor
         (case2DisplayedPostPivotFreeCprimeOfFollowingFactor F),
C(1) = case2DisplayedPostPivotResidualBlock
         (case2SuccessorSelectedEntrySourceResidual yNext eNext).
```

Lean already proves the following-factor inverse:

```text
case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
```

so `C(0)` is exactly the free matrix `F`, up to the displayed endpoint
reindexing convention.

Lean also proves, inside
`case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData`,
that reading `C(1)` entrywise gives

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext.
```

The readback then applies

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
```

under the nonzero-pivot hypothesis.  This is the precise Lean counterpart of
the fixed selected-pivot sector on Aoyagi pp. 19-21.

## Coordinate Ordering And Block Form

Let

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple z
rawMap z = topologyTupleEdgeRawOrder (Y z).
```

Order the source coordinates as

```text
passive fields, yNext, F.
```

Order the target topology-tuple coordinates as

```text
endpoint-transported passive fields, endpoint-transported C(1),
endpoint-transported C(0)
```

or equivalently with `C(0)` and `C(1)` in Lean's tuple order.  Changing between
these two target orders is a finite block permutation, hence changes the
ordinary determinant only by a sign.

With the first target order, the derivative of `Y` has the schematic form

```text
[ endpoint/passive linear equivalence      0                     0 ]
[ 0                                   D chartMap(yNext)          0 ]
[ 0                                        0             endpoint/reindex F ]
```

After Lean's tuple-order permutation of the two active `C` blocks, this becomes
block-permuted diagonal.  In either order the absolute determinant is the
product of:

1. the absolute determinant of the passive endpoint reindexing;
2. the absolute determinant of the selected-entry chart
   `yNext -> C(1)`;
3. the absolute determinant of the free following-factor reindexing
   `F -> C(0)`.

The endpoint transports and finite matrix reindexings are coordinate
permutations after choosing the displayed finite bases.  Their absolute
determinant is `1` in the current normalized coordinate model.  If a future
formalization phrases endpoint transport as an arbitrary linear equivalence
rather than a pure finite reindexing, this factor must be carried explicitly
as a positive constant.

The selected-entry factor is already formalized as

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext yNext
  = |yNext pivotNext| ^ card(center.erase pivotNext).
```

Lean names this in two determinant forms:

```text
sourceDensity_eq_abs_chartMapFDeriv_det
map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
```

Therefore the expected source-to-det-tuple Jacobian is

```text
absDet(DY z)
  = c_endpoint *
    SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext
```

with `c_endpoint = 1` for the current endpoint-reindexing implementation.

## Composition With Raw Order

The map consumed by the latest handoff theorem is not only `Y`; it is

```text
rawMap = topologyTupleEdgeRawOrder o Y.
```

On the determinant sector, Lean already identifies the raw-order absolute
determinant with

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z).
```

Thus the expected forward absolute determinant of `rawMap` is

```text
absDet(D rawMap z)
  = c_endpoint *
    SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext *
    retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z).
```

The last factor is positive and locally bounded above and below on determinant
chart shrinks by the existing retained-passive continuity/positivity lemmas.
The selected-entry factor is locally bounded above on a bounded source box; it
is locally bounded below only after shrinking inside a nonzero-pivot sector.
Across the pivot hyperplane itself the selected-entry chart is not injective,
and the lower bound must not be asserted.

## Correct Measure Convention

For an unweighted product Haar/source measure `sourceHaar` on the enlarged
source coordinates, the forward change-of-variables statement should have the
source-side density:

```text
Measure.map rawMap
  ((sourceHaar.restrict V).withDensity
    (fun z =>
      ENNReal.ofReal
        (c_endpoint *
          SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.yNext *
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))))
  =
rawHaar.restrict (rawMap '' V)
```

up to replacing `rawMap '' V` by the exact measurable local raw chart piece
proved in Lean.

Equivalently, if one defines

```text
thetaReference =
  sourceHaar.withDensity rawMapAbsDet
```

then the latest formal-product handoff's explicit hypothesis

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet
```

is the right COV input, provided `rawSourceSet` is the chosen local raw image.
This is the cleanest way to use the constant-density-`1` handoff already
proved in Lean.  Equivalently, the source-side COV may be stated directly with
`(sourceHaar.restrict V).withDensity rawMapAbsDet`; the Lean handoff just
expects the restriction to appear as `thetaReference.restrict V`.

For a contract relative to the unweighted source image

```text
Measure.map sourceChart (sourceHaar.restrict V),
```

one should instead state

```text
formalProductMeasure.restrict chartPiece =
  ((Measure.map sourceChart (sourceHaar.restrict V)).withDensity targetDensity)
    .restrict chartPiece
```

where `targetDensity` is the forward determinant transported to the image by
the local readback.  This is a target-side `withDensity` only because the base
measure is the unweighted source-image pushforward.  If the base measure is
target Haar/formal-product volume instead, the unweighted source-image measure
has inverse density `1 / rawMapAbsDet(readback E)`.

A one-way domination

```text
formalProductMeasure.restrict chartPiece <=
  D • Measure.map sourceChart (sourceHaar.restrict V)
```

requires only a local upper bound for the forward determinant.  A reverse
domination requires a local positive lower bound and therefore must be confined
to a nonzero-pivot shrink.

## Formalization Plan

The next Lean theorem should not assume the final formal-product/source-image
domination.  A useful upstream theorem would be one of:

1. A source-side weighted raw COV for `rawMap`, with explicit density
   `sourceDensity * retainedPassiveFormalRawOrderJacobianProductAbsDetAt`.
2. A `Y`-only COV into determinant topology-tuple coordinates, proving the
   selected-entry density factor and leaving raw-order composition to the
   existing retained-passive COV.
3. A bounded-domination corollary from (1), proving that the latest
   formal-product/source-reference handoff feeds the existing
   `A2Case2FormalProductSourceImagePieceContract`.

The most bedrock route is (2) first: prove the block-coordinate COV for `Y`
from product identity maps and the existing selected-entry chart COV, then
compose with the already-proved raw-order theorem.

## Kill Conditions

- Do not read Aoyagi pp. 10-22 as printing the Lean raw-map pushforward
  theorem.  They provide the coordinate formulas supporting the elementary
  calculation.
- Do not identify the free `F` with Aoyagi's original untransformed following
  matrix.  It is the normalized retained/raw `C(0)` coordinate after the
  Case 2 following-factor transform.
- Do not claim coverage outside the fixed nonzero selected-pivot chart.
- Do not claim two-sided bounded density across the pivot hyperplane.
- Do not omit the raw-order determinant factor when the target is `rawMap`.
- Do not use the quiver-based paper or quiver Lean results as source evidence.
