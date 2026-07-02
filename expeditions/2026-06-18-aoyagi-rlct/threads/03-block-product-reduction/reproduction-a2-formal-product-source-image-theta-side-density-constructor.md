# Reproduction - A2 formal-product/source-image theta-side density constructor

Date: 2026-07-02.

Status: measure-bookkeeping infrastructure reproduced and formalised.  This is
not the Aoyagi Jacobian calculation and does not prove the
formal-product/source-image comparison by itself.

## Goal

The local formal-product/source-image contract expects an edge-side density
identity:

```text
formalProductMeasure.restrict chartPiece
  =
((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
  .restrict chartPiece.
```

Raw-order and source-chart handoffs more naturally produce a theta-side
weighted pushforward:

```text
formalProductMeasure.restrict chartPiece
  =
(Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => density (sourceChart theta))).restrict V))
  .restrict chartPiece.
```

The present step proves that the second equality implies the first.

## Calculation

Let

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

Assume `V` is measurable, `sourceChart` is a.e. measurable for
`thetaReference.restrict V`, and `density` is a.e. measurable for `sourceRef`.
Since

```text
theta => density (sourceChart theta)
```

factors through `sourceChart`, the generic pushforward-with-density lemma gives

```text
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => density (sourceChart theta))).restrict V)
  =
sourceRef.withDensity density.
```

Restricting both sides to `chartPiece` converts the theta-side equality into
the edge-side equality stored in
`A2Case2FormalProductSourceImagePieceContract`.

## Lean Translation

Lean proves:

```text
A2Case2FormalProductSourceImagePieceContract
  .formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity

A2Case2FormalProductSourceImagePieceContract
  .exists_of_restrict_eq_map_sourceChart_withDensity
```

The first theorem is the equality conversion.  The second theorem constructs
the contract from the same local source-chart fields as before, but with the
theta-side weighted pushforward equality instead of the already-converted
edge-side density equality.

## Boundary

This step does not construct `density`, prove a Jacobian determinant formula,
prove that the density is bounded, identify formal-product measure with raw
Haar, prove source-image coverage, transport the original prior, prove normal
crossings, compute pole order, or extract an RLCT.

It only removes a measure-bookkeeping mismatch between theta-side weighted
pushforwards and the contract's edge-side `withDensity` field.
