# Review - A2 Case 2 Passive Theta Source-Chart Readback Left Inverse

Date: 2026-06-30.

## Result

PASS.

## Reviewers

- `Dirac`, xhigh source/scope/math review.
- `Ramanujan`, xhigh Lean/API review.

## Source and Scope Review

Dirac checked the reproduction note against the Lean statements.  The
endpoint-transport cancellation has the correct orientation: endpoint transport
uses the inverse endpoint maps in the forward direction, and the new inverse
lemma cancels fieldwise by `Matrix.submatrix_submatrix`.

The readback theorem assumes exactly the two needed pointwise facts:

```text
sourceReadback E = retainedData theta
case2PassiveThetaEndpointInverseReadout ... X = theta.yNext
```

and concludes only

```text
case2PassiveThetaEndpointSourceChartReadback ... X = theta.
```

The final local theorem returns an open neighborhood with
`readback (sourceChart z) = z`.  It does not assert image measurability,
source-image equality, Haar transport, source-prior comparison, normal
crossings, pole order, or RLCT.

## Lean/API Review

Ramanujan reviewed the current pointwise version, after the proof was changed
away from the earlier dummy-measure wrapper.  The public theorem no longer has
unnecessary measurable-space hypotheses and depends on the determinant-domain
source-readback theorem plus the open nonzero-pivot restriction.

`endpointTransport_symm_endpointTransport` is in the intended namespace and is
safe as a simp theorem because it strictly reduces a double endpoint transport
to the original coordinate datum.

Non-blocking note: the helper
`case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData`
may not need all of its current `τ` typeclass assumptions.  The public local
theorem does need the finite/decidable assumptions through the selected-entry
source theorem, so no required fix was recorded.

## Verification

Before this review note was written, the controller had already checked:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The full build replayed existing modules with pre-existing warnings outside
this slice, but the build completed successfully.

