# Reproduction - A2 Case 2 enlarged following-factor raw-density frontier

Date: 2026-07-02.

Status: pen-and-paper frontier for the actual formal-product/source-image
density calculation.  No Lean theorem is claimed by this note.

## Source Formulas

Aoyagi Lemma 2, PDF pp. 10-11, performs the elementary Schur elimination for
one block matrix with regular top-left block:

```text
C4 = -A3 A1^{-1} A2 + A4,
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1}.
```

Theorem 3, PDF pp. 11-13, iterates this step along a product.  After regular
left/right transformations, the loss separates into the finite regular
variables

```text
C1 - I,  F2,  F3
```

and the residual product

```text
product_s C(s).
```

The PDF records the coordinate algebra.  It does not state the
formal-product/source-image measure theorem, the raw-Haar pushforward, or the
local bounded-density comparison used by the Lean contract.

The later blow-up pages provide the local differential-product shape but
still not the image-measure theorem.  On PDF pp. 14-15, Aoyagi writes the
source differential product as monomial factors

```text
product u_(s,k)^(M_(s,k)-1) du_(s,k)
```

times the current residual block differentials and untouched following-factor
blocks.  In Case 2, PDF pp. 19-22, the following factor is transformed by an
upper-unitriangular matrix `Q`, so the following-factor coordinate change is
unit determinant after the chosen normalization.  These facts support a local
coordinate-density calculation, but they do not print the pushforward identity
for the Lean source-image measure.

## Enlarged Coordinates

For the two-edge retained-passive window, Lean's p.13 raw topology tuple has
the nonredundant fields

```text
A1passive : Fin 1 -> Matrix rho rho R
F2        : Fin 2 -> Matrix rho (kappa p.castSucc) R
A3passive : Fin 1 -> Matrix (kappa p.castSucc.succ) rho R
C         : Fin 2 -> Matrix (kappa p.succ) (kappa p.castSucc) R
Ctop      : Matrix rho rho R
F3        : Matrix (kappa last) rho R
```

Thus the active residual part contains exactly two raw `C` factors:

```text
C(0) : kappa(1) -> kappa(0)
C(1) : kappa(2) -> kappa(1).
```

The old `Case2PassiveTheta` chart supplies the selected-entry center
coordinates through the successor residual block.  It does not by itself give
an independent `C(0)`.  The enlarged source

```text
Case2PassiveThetaWithFollowingFactor =
  Case2PassiveTheta x Matrix (Case2ResidualColIndex n S (J+1)) tau R
```

adds exactly that missing following-factor matrix.  In the raw two-edge
domain, after endpoint transport back by the equivalences `e`, the retained
data has:

```text
raw C(0) = F
raw C(1) = selected-entry successor matrix built from yNext.
```

This is the formal retained-passive coordinate construction, not a formula
printed verbatim by Aoyagi.  In the PDF Case 2 calculation, the selected pivot
chart is applied to the displayed current block and the following block is
then transformed by the regular/unitriangular `Q` matrix.  The Lean
`yNext`/`C(1)` readout is therefore a fixed-pivot local chart choice in the
normalized retained data.  It must be justified by the existing entrywise
readout lemmas, or carried under an explicit fixed-pivot nonzero/readout
hypothesis; it is not source-image coverage by itself.

The readback theorem already checks this distinction: it recovers `F` from
raw `C(0)` and recovers `yNext` from raw `C(1)`, not from the product
`C(1) * C(0)`.

## Coordinate-Count Check

The enlarged source coordinates are:

```text
passive retained coordinates
+ selected-entry chart coordinates for C(1)
+ free following-factor coordinates for C(0).
```

The target raw topology tuple has:

```text
same passive retained coordinates
+ raw C(1)
+ raw C(0).
```

The selected-entry chart map is a local coordinate map from `yNext` to the
raw `C(1)` block on the nonzero-pivot sector.  The following-factor component
is the identity onto raw `C(0)` only after the same normalization and
endpoint/reindexing conventions used in the retained-data definition.  Thus
`F` should be read as the normalized retained following-factor block, not as
Aoyagi's untransformed full following matrix.  With that convention, the
source coordinate count matches the raw topology-tuple chart piece after the
active `C` factors are split.  The old, non-enlarged theta chart was a
graph/section in this active `C` tuple; the enlarged chart is the first
dimension-matched candidate.

The existing Lean coordinate inventory records this split as

```text
Case2PassiveTheta.cCoordinateIndex_card_eq_cHead_add_center
```

where the head block has cardinality

```text
|Case2ResidualColIndex n S (J+1)| * |tau|.
```

Thus the second component of `Case2PassiveThetaWithFollowingFactor` is exactly
the missing head active `C` block.  The local rank obstruction is not
dimension count; it is the selected-pivot-zero hyperplane, where the
selected-entry chart for the tail `C(1)` block drops rank.

## Expected Density Shape

Let

```text
Y(z)      = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple z
rawMap(z) = topologyTupleEdgeRawOrder (Y(z))
sourceChart(z) =
  case2PassiveThetaWithFollowingFactorEndpointSourceChart z.
```

On the determinant sector, the p.13 raw-order source chart satisfies the
pointwise two-stage identity

```text
rawChart (rawMap z) = sourceChart z.
```

The formal-product measure in the existing Lean socket is already expressed
as

```text
Measure.map (fun u => rawChart (topologyTupleEdgeRawOrder u))
  ((rawHaar.restrict rawDetChart).withDensity
    (formalProductAbsDet u)).
```

The remaining calculation is therefore the finite-dimensional change of
variables for the source-coordinate map `Y` or `rawMap`.

Pen-and-paper expectation:

1. Endpoint transport is a coordinate permutation/reindexing, so its absolute
   determinant is a positive constant.
2. The passive retained fields enter as identity coordinates.
3. The free following factor `F` enters raw `C(0)` as an identity block.
4. The selected-entry chart contributes the usual selected-entry density for
   raw `C(1)`,

   ```text
   SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y
     = |y pivot| ^ |center.erase pivot|
   ```

   with the nonzero-pivot condition giving a local positive bounded unit on a
   small box.  Lean already records the derivative convention as
   `sourceDensity_eq_abs_chartMapFDeriv_det` and the corresponding pushforward
   as `map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero`.
5. The retained-passive raw-order map contributes the already-formalized
   `retainedPassiveFormalRawOrderJacobianProductAbsDetAt` factor.

Thus the desired contract density should be a product of already named
positive local units: endpoint/reindexing constants, the selected-entry
source density, and the retained-passive formal-product raw-order determinant
factor, evaluated through the local inverse/readback.

This bounded-unit statement is only after the monomial exceptional factors
have been separated.  Across the exceptional divisor itself, a full blow-up
Jacobian factor such as `|u|^(N-1)` is not bounded below by a positive unit
when `N > 1`.  A bounded-density theorem must therefore state exactly which
measure already includes the monomial factor and which residual density is
being bounded.

## Lean Target

The next source-moving theorem should not be another original-volume wrapper.
The honest target is a raw/source density theorem for the enlarged chart:

```text
formalProductMeasure.restrict chartPiece =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict chartPiece
```

with a simultaneously proved local a.e. bound

```text
forall^ae E in (Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
  density E <= bound.
```

A useful intermediate statement may replace this by a raw-order formulation:

```text
rawHaar.restrict rawSourceSet =
  (Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity
```

or the corresponding bounded domination/equality restricted to the chosen
source chart piece.  This is closer to the actual Jacobian calculation and
would feed the existing formal-product/source-reference bridge.

## Lean API Checkpoint

Before the density theorem, the smallest bridge is a with-following analogue
of the existing non-following raw-order/two-stage source-chart package.

The non-following theorem is

```text
exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

in `RetainedPassiveCase2PassiveThetaSourceMeasure.lean`.  Its proof ultimately
uses the generic selected-entry source theorem.  For the enlarged source, the
first pointwise raw-order equality should be even more primitive: for any
determinant-chart retained-passive datum, Lean already has

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
```

in `RetainedPassiveLocalSource.lean`.  Applying this to
`case2PassiveThetaWithFollowingFactorEndpointRetainedData` should give

```text
rawChart (rawMap z) = sourceChart z
```

on the local determinant/pivot sector.  It should also give local-source
membership and `sourceReadback = retainedData` through the existing
retained-passive source-chart readback lemmas.  These statements are
coordinate bookkeeping only; they do not assert raw-Haar transport or the
Jacobian density identity.

After this pointwise bridge, the measure-level two-stage equality is the same
measure bookkeeping as in the non-following theorem:

```text
Measure.map (fun z => rawChart (rawMap z)) (thetaMeasure.restrict V)
  = Measure.map sourceChart (thetaMeasure.restrict V)

Measure.map rawChart (Measure.map rawMap (thetaMeasure.restrict V))
  = Measure.map sourceChart (thetaMeasure.restrict V)
```

The actual density comparison still needs an additional finite-dimensional
change-of-variables calculation for the map from enlarged source coordinates
to raw retained-passive topology-tuple coordinates.

## Kill Conditions

- Do not use the old residual product `C(1) * C(0)` to recover `yNext`.
- Do not claim a density identity from Aoyagi pp. 10-13 alone; the pages give
  coordinate algebra, not a measure theorem.
- Do not treat the old `Case2PassiveTheta` source as dimension-matched for
  both raw active `C` factors.
- Do not state `bound < infinity` unless it is explicitly proved or carried
  as a hypothesis.
- Do not assert two-sided bounded density across the exceptional divisor for
  the full blow-up Jacobian.  Only the residual smooth density after factoring
  the monomial can be locally bounded above and below.
- Do not rely verbatim on the ambiguous p.21 product line if it double-counts
  the blow-up scalar after defining `b'_q = u b_q`; use the algebraic
  normalization checked in the retained source definitions.
- Do not treat one fixed selected-entry chart as covering the whole Case 2
  blow-up/source image.  It is a local sector under a fixed-pivot nonzero
  condition unless a finite pivot cover is separately constructed.
- Do not read the formal following-factor variable `F` as Aoyagi's original
  untransformed following matrix.  It is the normalized retained/raw `C(0)`
  coordinate after the `Q`-transformation and endpoint/reindexing choices.
- Do not use Aoyagi's displayed ratios such as `b'_i / b'_{J+1}` across the
  exceptional divisor unless the common monomial factors have already been
  cancelled or the relevant denominator/nonvanishing hypothesis is in force.
- Do not call the result RLCT, pole order, or normal crossings.  The only
  allowed citation boundary remains normal-crossing-to-RLCT extraction.

## Next Check

Before Lean, check the following calculation explicitly:

```text
det D(rawMap)(z)
  = det D(topologyTupleEdgeRawOrder)(Y(z)) *
    det D(Y)(z),
```

where `det D(Y)` splits into endpoint/reindexing constants, passive identity
blocks, selected-entry chart density for `C(1)`, and following-factor identity
for `C(0)`.

The selected-entry factor and retained-passive factor should be checked
against the exact Lean density conventions, since one side may use the
forward density and another the inverse target-side density.

In particular, the source-side selected-entry density is the forward
Jacobian density of `chartMap`.  If a later theorem is stated as a density on
the target image measure instead, the inverse/readback convention must be
used consistently.
