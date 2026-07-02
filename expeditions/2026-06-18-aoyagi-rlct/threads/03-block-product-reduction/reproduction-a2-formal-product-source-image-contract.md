# Reproduction - A2 formal-product/source-image contract

Date: 2026-07-02.

Status: contract slice for Lean; the Jacobian-density calculation remains a
separate pen-and-paper obligation.

## Source Boundary

Aoyagi Lemma 2 and Theorem 3 give the coordinate algebra for the Case 2
product reduction.  In the one-step block calculation, for

```text
A = [ A1 A2
      A3 A4 ],
```

with `A1` regular, the substitution is

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2.
```

The inverse formulas are

```text
A2 = -A1 F2,
A3 = -F3 A1,
A4 = C4 + A3 A1^{-1} A2.
```

Theorem 3 iterates this chart through the product and reaches the p.13
product-difference expression.  This supports the local source-chart formulas,
the local inverse/readback check, and the finite-dimensional Jacobian problem.
It does not by itself state the measure comparison between the p.13
formal-product measure and the source-image reference.

## Contract

For a theta space `Theta`, an edge-family space `E`, a local set `V`, a
source chart

```text
sourceChart : Theta -> E,
```

and a chart piece `chartPiece`, define the source-image reference

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V).
```

The contract records:

```text
formalProductMeasure.restrict chartPiece =
  (sourceRef.withDensity density).restrict chartPiece
```

and

```text
density <= D    sourceRef.restrict chartPiece-a.e.
```

together with the local chart facts already expected in A2: `V` and
`chartPiece` measurable, `chartPiece subset sourceChart '' V`, measurable
image, continuity/injectivity on `V`, and
`readback (sourceChart theta) = theta` on `V`.

The immediate consequence is the exact domination required by the existing
original-volume bridge:

```text
formalProductMeasure.restrict chartPiece <= D • sourceRef.
```

The same contract also feeds the readback domination socket:

```text
Measure.map readback (formalProductMeasure.restrict chartPiece)
  <= D • thetaReference.restrict W
```

for every `W` containing `V`.

## What This Proves

The Lean slice proves only the bounded-density bookkeeping:

1. equality-with-density plus local a.e. upper bound gives source-image
   domination;
2. with the local inverse/continuous-injective chart facts, the same data gives
   readback domination.

This is useful because it names the exact A2 contract that later Jacobian work
must discharge, and it lets downstream bridge statements consume one record
instead of an unstructured list of hypotheses.

## What Remains

The contract still has to be produced from Aoyagi's formulas.  That requires:

- coordinate-count agreement between `Case2PassiveTheta` and the p.13
  formal-product chart piece;
- image coverage for the intended chart pieces;
- the actual Jacobian density formula;
- local positivity and boundedness of the unit factors after shrinking.

## Nonclaims

This contract does not prove the density identity, the density bound,
coordinate-count agreement, source-image coverage, source-rank coverage,
determinant Haar transport, raw-Haar pushforward, original-prior transport,
normal crossings, pole order, or RLCT extraction.
