# Review - A2 Case 2 formal-product/source-image local change of variables

Reviewer: Pascal, xhigh Lean/source frontier scout.
Date: 2026-07-02.

Verdict: pass for a construction/frontier packet; do not implement Lean yet.

## Findings

No blocking findings against the packet direction.

The reviewer confirmed that the next useful A2 packet should target the
formal-product/source-image comparison:

```text
muP13.restrict chartPiece <=
  D • Measure.map sourceChart (thetaReference.restrict V)
```

for measurable `chartPiece subset sourceChart '' V`, where `muP13` is the
p.13 formal-product chart measure.  A stronger bounded-density equality is
also acceptable if it supplies the same domination.

The reviewer also confirmed that the existing bridge

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

is the correct downstream consumer.  It is sound, but it deliberately keeps
the formal-product/source-image comparison as the missing hypothesis.

## Source Boundary

Aoyagi pp. 10-13 support the Schur elimination formulas, the iterated product
reduction, and the p.13 loss/product split.  They do not by themselves state
the needed measure-transport theorem.  The local change-of-variables theorem
must therefore be constructed explicitly from the coordinate formulas,
including image/coverage and Jacobian-density checks.

## Kill Conditions

The reviewer emphasized the same kill conditions recorded in the card:

- do not treat endpoint image references as unrestricted determinant-chart
  Haar;
- do not claim full determinant-chart coverage from the selected
  passive-theta endpoint image;
- do not normalize Haar scalars away;
- do not define the desired source measure to be the image reference;
- do not ignore dimension mismatch or fixed-section variables such as
  `C1 = I`;
- do not claim source-image/source-rank coverage, normal crossings, pole
  order, or RLCT extraction.

## Nonclaims

This review proves no formal-product/source-image comparison, original-volume
transport, original-prior transport, determinant Haar transport, raw-Haar
pushforward, source coverage, source-rank coverage, normal crossings, pole
order, or RLCT extraction.
