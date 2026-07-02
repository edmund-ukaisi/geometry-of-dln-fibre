# Review - A2 with-following original-volume domination

Date: 2026-07-02.

Reviewer: Harvey the 2nd, xhigh read-only sidecar audit.

Verdict: PASS after documentation fix.

## Initial Finding

The first review found no mathematical issue in the Lean theorem.  It checked
that the theorem statement keeps the required hypotheses explicit:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

It also checked that the scalar orientation is the p.13 bridge orientation:

```text
(((cHaar^-1 : NNReal) : ENNReal) * 1) • sourceRef.
```

The only finding was documentation drift: the reproduction note still described
the record-constructor eliminator route, while the Lean proof uses the
constant-density formal-product/source-reference theorem directly and feeds its
equality/bound pair into the p.13 bounded-density original-volume bridge.

## Fix

The reproduction note was updated to describe the direct route:

```text
with-following constant-density handoff
  + p.13 bounded-density original-volume bridge.
```

It now mentions the `A2Case2FormalProductSourceImagePieceContract` constructor
only as the record packaging of the same constant-density identity, not as the
Lean proof route for this theorem.

## Boundary Checked

No raw-Haar transport, determinant-chart Haar transport, source-image coverage,
source-prior/original-prior transport, density lower-bound removal, normal
crossings, pole order, or RLCT extraction is claimed.

## Verification

The reviewer replayed focused elaboration of
`RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean`.  The controller
also ran focused elaboration, focused module build, full local
`lake build DLNFibre`, no-sorry audit, whitespace check, targeted marker scan,
and direct axiom probe.  The new theorem reports
`[propext, Classical.choice, Quot.sound]`.
