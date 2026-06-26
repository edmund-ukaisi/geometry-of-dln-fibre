# A2 retained-passive source-map factor readout

## Boundary

This slice proves finite factor readout for retained-passive source-map
families.  It does not construct a real Aoyagi source chart, identify
fixed-base endpoint complements with Case 2 row/column intervals, collapse a
full endpoint product to an adjacent window, prove fixed pivot nonzero,
prove source image coverage, prove pushforward/Jacobian transport, compare
the original loss, prove normal crossings, compute pole order, or extract an
RLCT.

The Case 2 specialization in this slice is for the synthetic two-edge
retained-passive datum `case2PostPivotRetainedPassiveData`.  It is not a
fixed-base source-production theorem for a real Aoyagi chart.

## Pen-and-paper reproduction

Let `data` be retained-passive nonredundant coordinate data, and assume
`data.detChart`.  The source map of the retained-passive coordinates is
`data.edgeMatrix`.  The established readback inverse says

```text
sourceReadback(data.edgeMatrix) = data.
```

The per-factor source-readback identity says

```text
(sourceReadback E).C_p
  = schurResidualBlock(sourceReadbackTransformedEdge(E,p)).
```

Apply this with `E = data.edgeMatrix` and rewrite by the readback inverse:

```text
schurResidualBlock(sourceReadbackTransformedEdge(data.edgeMatrix,p))
  = data.C_p.
```

Thus every retained-passive source-map edge has transformed Schur residual
equal to the corresponding stored residual factor.

For the synthetic Case 2 two-edge datum, the stored active factors are
definitionally

```text
data.C_1 = case2DisplayedPostPivotResidualBlock,
data.C_0 = case2DisplayedPostPivotFreeFollowingFactor.
```

Therefore the transformed source edge at edge `1` reads out the displayed
post-pivot residual block, and the transformed source edge at edge `0` reads
out the displayed following factor.

## Kill Conditions

- The synthetic Case 2 datum has endpoint family
  `case2PostPivotTwoEdgeDomain`; this does not produce equivalences from
  fixed-base endpoint complements.
- The theorem reads off individual factors.  It does not identify the full
  fixed-base residual product with the adjacent two-edge product.
- The theorem does not prove selected-entry entrywise readout or pivot
  nonzero.
