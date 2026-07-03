# A2 with-following finite integral on the p.13 readback slice

Status: controller pen-and-paper reproduction before review.

Source: Aoyagi pp. 10-13 retained-passive source chart and pp. 19-22
selected-entry Case 2 coordinates.  This note is independent of the
quiver-based paper.  It uses only the local p.13 image equality and the
already-proved readback-preimage finite-integral wrapper; it does not use the
cited normal-crossing-to-RLCT theorem.

The previous support wrapper gives an open neighborhood `V` such that every
measurable chart piece satisfying

```text
chartPiece subset p13SourceSet,
chartPiece subset readback^{-1}(V)
```

has finite readback product-residual integral.  The same package also returns
the local image equality

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V).
```

## Reproduction

Take the chart piece to be the whole local p.13 readback slice

```text
p13SourceSet inter readback^{-1}(V).
```

It is measurable because the local image equality rewrites it as
`sourceChart '' V`, and the package already returns measurability of
`sourceChart '' V`.

The two support hypotheses are then projections from membership in the
intersection:

```text
E in p13SourceSet inter readback^{-1}(V)
  ==> E in p13SourceSet,

E in p13SourceSet inter readback^{-1}(V)
  ==> readback E in V.
```

Applying the previous readback-preimage finite-integral wrapper to this chart
piece gives finite integrability over the whole local p.13/readback slice.

## Boundary

This is a canonical-piece specialization of the local support wrapper.  It
does not prove that a source-side neighborhood is contained in
`readback^{-1}(V)`, does not prove global p.13 coverage, source-rank-stratum
coverage, finite atlas coverage, Haar/Jacobian transport, normal crossings,
pole order, or RLCT.
