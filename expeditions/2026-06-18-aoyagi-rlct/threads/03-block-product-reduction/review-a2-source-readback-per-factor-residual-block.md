# Review - A2 source-readback per-factor residual block

Reviewer: xhigh scout `Pascal the 4th`.

## Verdict

No blockers.

## Checks

The reviewed Lean theorem is

```lean
sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge
```

in `RetainedPassiveCoordinates.lean`.  It states exactly that
`(sourceReadback E).C p` is the Schur residual block of
`sourceReadbackTransformedEdge E p`, and the proof is `rfl`.

The theorem is a useful stable rewrite for source-readback factor work.  It
is not a substantive adjacent-window result by itself: adjacent-window Case 2
work still needs endpoint equivalences, product/window transport, and actual
displayed factor identities.

## Warnings

Do not add further wrappers around this helper unless a downstream theorem
directly consumes them.  The next source-moving target should be a
product/window bridge or a source-specific factor-alignment theorem, not
another Schur-block definitional theorem.

## Verification

The controller ran the focused Lean check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

It passed on 2026-06-26.
