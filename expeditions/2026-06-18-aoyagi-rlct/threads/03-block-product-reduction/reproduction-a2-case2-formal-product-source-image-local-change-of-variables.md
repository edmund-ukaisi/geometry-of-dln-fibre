# Reproduction - A2 Case 2 formal-product/source-image local change of variables

Date: 2026-07-02.

Status: pen-and-paper frontier reproduction; not a Lean implementation target
yet.

## Goal

Identify the exact A2 theorem needed to remove the supplied
formal-product/source-image domination hypothesis:

```text
formalProductMeasure.restrict chartPiece
  <= D • Measure.map sourceChart (thetaReference.restrict V).
```

The downstream theorem waiting for this hypothesis is:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

which already converts formal-product domination into original-volume
domination with the p.13 inverse Haar scalar.

## Source Calculation

Aoyagi Lemma 2 treats a matrix block decomposition

```text
A = [ A1 A2
      A3 A4 ]
```

with `A1` regular.  The coordinate substitution is:

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2.
```

The inverse formulas are:

```text
A2 = -A1 F2,
A3 = -F3 A1,
A4 = C4 + A3 A1^{-1} A2.
```

Theorem 3 iterates this step through the product `A(1) ... A(L)`.  The p.13
display shows that after multiplying by regular left and right factors, the
loss splits into regular variables `C1-Er`, `F2`, `F3` and the reduced product
term:

```text
prod_s C^(s) - F3 F2.
```

This supports the source-chart algebra and the already-formalized p.13 local
source chart.  It does not state a measure pushforward theorem from the
theta-domain reference measure to the p.13 formal-product chart measure.

## Current Lean Translation

The Lean development has already converted the p.13 algebra into:

```text
case2PassiveThetaEndpointSourceChart
case2PassiveThetaEndpointSourceChartReadback
```

and local facts:

```text
readback (sourceChart z) = z
Set.InjOn sourceChart V
ContinuousOn sourceChart V
MeasurableSet (sourceChart '' V)
```

on a suitable shrink `V`.

The p.13 formal-product chart measure is the `muP13` side of the existing
formal-product/original-volume bridge.  The concrete source-image reference is:

```text
Measure.map sourceChart (thetaReference.restrict V).
```

Current consumers can use a domination or bounded-density comparison between
these two measures, but no current theorem constructs it.

## First Gate: Dimension

A domination theorem of the form

```text
muP13.restrict chartPiece <= D • sourceRef
```

can hold only if the source image carries enough local coordinates for the
p.13 formal-product chart piece.  Therefore the first pen-and-paper obligation
is a coordinate count:

```text
dim(Case2PassiveTheta coordinates on V)
  ?= dim(p13 formal-product chart coordinates on chartPiece).
```

If the Case 2 source chart is a lower-dimensional section, then `sourceRef`
cannot dominate the formal-product chart measure on an ambient p.13 chart
piece.  The correct target would then require an enlarged retained-passive
coordinate domain or a submanifold/source-stratum measure.

Update, 2026-07-06: the coordinate-count gate is now reproduced separately in

```text
reproduction-a2-case2-formal-product-source-image-coordinate-count-gate.md
```

The result is that plain `Case2PassiveTheta` is lower-dimensional: it supplies
the selected-entry charted active `C 1` block but has no free active `C 0`
block.  The enlarged `Case2PassiveThetaWithFollowingFactor` adds exactly this
missing matrix and is the only viable full-dimensional source for an ambient
p.13 formal-product/source-image local change-of-variables theorem.

## Second Gate: Inverse And Image

If the dimension check passes, prove that the chart is a genuine local
coordinate change on the intended image:

```text
readback (sourceChart theta) = theta       for theta in V,
sourceChart (readback E) = E              for E in sourceChart '' V.
```

The left inverse is already available locally.  The right-inverse statement is
available on produced image points; any theorem about a larger p.13 chart
piece requires an additional image coverage theorem.

## Third Gate: Jacobian Density

Assuming a full local coordinate chart, the comparison density should be the
absolute Jacobian of the coordinate change from `thetaReference` to the p.13
formal-product chart measure:

```text
d muP13 / d sourceRef (sourceChart theta)
  = |det D(sourceChart)(theta)|^{-1}
```

or the equivalent forward-Jacobian convention.  Passive factors must be shown
to be units on the chosen shrink.  Aoyagi pp. 10-13 provide the coordinate
formulas; they do not compute or state the full local measure theorem for the
Lean source-image reference.

## Fourth Gate: Boundedness

The downstream bridge only needs a finite upper bound on the density.  Once
the Jacobian is a continuous positive unit near the base point, this follows
by shrinking.

Aoyagi's smooth compactly supported prior assumption gives local boundedness
of a prior density after a valid volume/formal-product transport theorem is
known.  It does not identify the transported measure.

## Current Conclusion

Aoyagi pp. 10-13 support the coordinate algebra, not the full
formal-product/source-image measure comparison.  The next source-moving A2
theorem must prove one of:

1. a full local change-of-variables theorem comparing `muP13` with
   `Measure.map sourceChart (thetaReference.restrict V)`;
2. a retained-passive enlarged-coordinate theorem if the current
   passive-theta source chart is lower-dimensional;
3. a one-way domination theorem strong enough to feed the existing
   formal-product/original-volume bridge.

Another wrapper around finite-integral or original-volume consumers would not
move the frontier unless it removes the formal-product/source-image
comparison itself.

## Lean Consumers Once Proved

If the comparison is proved, existing Lean should consume it through:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference

originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
```

and then through the original-volume finite-integral wrappers.

## Kill Conditions

- If the coordinate count shows a lower-dimensional image, do not state
  domination of the ambient p.13 formal-product measure by the source image.
- If image coverage is only proved for produced points, do not claim coverage
  of arbitrary source-rank or p.13 neighborhoods.
- If the density is introduced by Radon-Nikodym abstraction without an
  explicit Jacobian or boundedness theorem, do not claim Aoyagi source
  reproduction.
- If the theorem still assumes the same formal-product/source-image
  domination consumed by the original-volume bridge, it is only a wrapper.
- Do not use endpoint image-reference measures as determinant/raw Haar.

## Nonclaims

No formal-product/source-image comparison, original-volume transport,
original-prior transport, source-image coverage, source-rank coverage,
Jacobian density formula, determinant Haar transport, raw-Haar pushforward,
normal-crossing theorem, pole-order theorem, or RLCT extraction is proved
here.
