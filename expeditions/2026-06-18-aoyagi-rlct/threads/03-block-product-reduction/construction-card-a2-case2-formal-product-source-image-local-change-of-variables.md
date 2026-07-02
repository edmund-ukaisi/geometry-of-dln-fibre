# Construction Card - A2 Case 2 formal-product/source-image local change of variables

Date: 2026-07-02.

Status: frontier specification; no Lean theorem claimed.

## Source Scope

Allowed source: Aoyagi 2023 preprint only.

Relevant source pages:

- PDF pp. 10-11: Lemma 2, the one-step full-rank block elimination
  `F2=-A1^{-1}A2`, `F3=-A3A1^{-1}`, and
  `C4=A4-A3A1^{-1}A2`.
- PDF pp. 11-13: Theorem 3, the iterated product-reduction chart and the
  final p.13 product-difference display.
- PDF p. 8: the smooth compactly supported prior assumption.  This supplies
  local boundedness only after a valid coordinate transport theorem has been
  proved.

No quiver-paper fact is part of this card.  The normal-crossing-to-RLCT
extraction remains outside this A2 measure-transport bridge.

## Current Lean Socket

The latest useful A2 bridge is:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean`.

It says that on a local Case 2 source-chart shrink, the restricted original
edge-family volume is dominated by the chart-produced source reference once
one supplies the missing comparison

```text
formalProductMeasure.restrict chartPiece
  <= D * Measure.map sourceChart (thetaReference.restrict V).
```

Thus the next A2 source-moving theorem should not be another finite-integral
or original-volume wrapper.  It should prove this formal-product/source-image
local comparison, or a stronger bounded-density statement from which it
follows.

## Target Shape

The target comparison is:

```text
muP13.restrict chartPiece <=
  D • Measure.map sourceChart (thetaReference.restrict V)
```

for every measurable `chartPiece` contained in `sourceChart '' V`, where
`muP13` is the p.13 formal-product chart measure already used by the
formal-product/original-volume bridge.

Stronger acceptable variants:

```text
muP13.restrict chartPiece =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict chartPiece
```

with `density <= D` a.e., or

```text
Measure.map sourceChart (thetaReference.restrict V) =
  (muP13.withDensity sourceDensity).restrict (sourceChart '' V)
```

with `epsilon <= sourceDensity` locally, giving the desired domination after
inverting `epsilon`.

The density must be the Jacobian density of Aoyagi's p.13 source chart, up to
passive unit factors.  It must not be an arbitrary Radon-Nikodym density used
only to restate the conclusion.

## Existing Inputs

The current A2 library already provides the following pieces.

### Local source chart and inverse data

`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`
contains local Case 2 passive-theta source-chart data, including:

```text
case2PassiveThetaEndpointSourceChart
case2PassiveThetaEndpointSourceChartReadback
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_sourceRankStratum
```

These give local continuity, injectivity, measurable image, readback
left-inverse, and one-way source-rank support for produced chart points.  They
do not prove formal-product/source-image measure transport.

### Raw-order and p.13 measure bridges

The raw-order/p.13 files provide raw/formal-product chart-measure identities
and consumers, including:

```text
map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

These are consumers or downstream handoffs.  They do not prove the
formal-product/source-image comparison itself.

### Original volume and prior handoffs

`lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPrior.lean` defines:

```text
originalEdgeFamilyVolume
originalEdgeFamilyPrior
originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
```

The original-volume bridge already converts the formal-product/source-image
comparison into the direction needed by original-volume finite-integral
consumers.  The prior-density wrapper should be used only after the
formal-product/source-image comparison has been proved.

## Missing Mathematical Lemma

The desired theorem is a local finite-dimensional change-of-variables result
for Aoyagi's p.13 source chart:

```text
exists V, IsOpen V /\ z0 in V /\
  MeasurableSet (sourceChart '' V) /\
  ContinuousOn sourceChart V /\
  Set.InjOn sourceChart V /\
  (forall z in V, readback (sourceChart z) = z) /\
  exists D,
    (forall measurable chartPiece,
      chartPiece subset sourceChart '' V ->
      muP13.restrict chartPiece <=
        D • Measure.map sourceChart (thetaReference.restrict V)) /\
    D < infinity.
```

An equality-with-density theorem is preferable if the Jacobian calculation is
available.  The one-way domination form is enough to feed the already-proved
original-volume bridge.

## Pen-And-Paper Obligations

Before Lean implementation, reproduce the following.

1. **Coordinate list and dimension check.**  List every coordinate in the
   Case 2 p.13 source chart and compare it with the coordinate model for
   `muP13`.  If the source chart is a fixed lower-dimensional section of the
   p.13 formal-product chart, it cannot dominate the formal-product measure.
2. **Local inverse.**  Write the readback formulas and prove
   `readback (sourceChart theta)=theta` on the theta-domain shrink.  If a
   source-side right inverse is needed for the measure theorem, state its
   exact image-set hypothesis.
3. **Image set.**  Identify the exact source-side image used by the theorem:
   `sourceChart '' V`, the p.13 source edge-family set, or a smaller chart
   piece.  Prove measurability and containment of chart pieces.
4. **Jacobian density.**  Compute the determinant of the coordinate change
   from `thetaReference` to the p.13 formal-product chart measure.  Separate
   monomial/active factors from passive unit factors and prove the latter are
   locally positive and bounded.
5. **Domination theorem.**  Decide whether the proof gives equality with
   density, two-sided bounded-density equivalence, or one-way domination.
   The result must feed the `muP13 <= D * sourceRef` socket without assuming
   that same comparison.
6. **Original-volume/prior payoff.**  Only after this comparison is proved,
   compose it with the existing original-volume bridge and then with the
   smooth-prior local boundedness wrappers.

## Kill Conditions

- If the source chart is lower-dimensional relative to the p.13
  formal-product chart measure, do not claim domination of `muP13` by its
  image reference.
- Do not define `muP13` or the original/source measure to be
  `Measure.map sourceChart (thetaReference.restrict V)`.
- Do not replace determinant/raw Haar by endpoint image-reference measures
  without a coverage and Jacobian theorem.
- Do not count `sourceChart` continuity, injectivity, or measurable-image
  results as measure transport; they are prerequisites only.
- Do not claim Aoyagi pp. 10-13 prove the measure theorem directly.  They
  provide the Schur/product coordinate algebra; the local measure theorem is
  an additional elementary coordinate-change construction.
- Keep normal-crossing-to-RLCT extraction as the only analytic citation
  boundary.

## Expected Payoff

If this theorem is proved, the existing original-volume bridge immediately
gives:

```text
originalEdgeFamilyVolume.restrict chartPiece <=
  constant • Measure.map sourceChart (thetaReference.restrict V).
```

That is the direction needed by the current readback and finite-integral
sockets.  It moves A2 from chart-produced measure bookkeeping toward an
honest local coordinate-change theorem for the p.13 source chart.

## Nonclaims

No formal-product/source-image comparison, original-volume transport,
original-prior transport, determinant Haar transport, raw-Haar pushforward,
source-image coverage, source-rank coverage, normal-crossing theorem,
pole-order statement, or RLCT extraction is proved here.
