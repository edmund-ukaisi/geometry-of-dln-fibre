# Review - A2 retained-passive coordinate-data edge-matrix residual-factor bridge

Reviewer: Curie the 3rd, xhigh

## Verdict

No blockers.

## Checks

The pure pointwise bridge
`sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq`
is correctly scoped.  It is pointwise in the source parameter `x`, generic in
the field and fixed-base source setup of `RetainedPassiveLocalSource.lean`, and
uses exactly the required hypotheses: `data.detChart` and the equality between
the fixed-base edge matrices and `data.edgeMatrix`.

The proof is the expected inverse step: rewrite the fixed-base edge family by
the supplied edge equality, then apply
`RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq`.

The selected-entry theorem in `RetainedPassiveLocalMeasure.lean` now consumes
the pure bridge cleanly.  The substantive Aoyagi/Case 2 obligation remains the
data-level residual-factor matrix identity `hdataFactor`; it is not hidden or
proved by this slice.

Focused builds passed for:

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

`git diff --check` was clean in the review pass.

## Nonclaims

The slice does not construct `retainedData`, prove the Case 2 entrywise
product identity, construct a source chart, prove source image equality,
prove a weighted pushforward/Jacobian theorem, compare original loss, prove
normal crossings, compute pole order, or extract an RLCT.
