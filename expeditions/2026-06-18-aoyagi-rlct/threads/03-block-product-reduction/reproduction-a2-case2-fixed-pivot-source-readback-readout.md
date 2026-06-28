# Reproduction - A2 Case 2 fixed-pivot source-readback readout

## Shape

Let

```text
pivotNext :=
  ((J + 2, J + 2) : case2ResidualBlockPivotEntries n S (J + 1)).
```

For the endpoint-transported explicit Case 2 selected-entry datum, the
already-proved matrix readout is

```text
residualFactorProduct data.C (last 2) 0
  =
    matrix (fun c =>
      chartMap pivotNext yNext
        (residualCoordEquiv c)).
```

Here

```text
residualCoordEquiv :
  AoyagiResidualBlockCoordinateIndex (kappa (last 2)) (kappa 0)
    ~= case2ResidualBlockPivotEntries n S (J + 1)
```

is the product of the endpoint equivalences with the displayed residual-block
pivot-entry equivalence.

The current all-pivot theorem uses nonzeroness of this matrix to obtain some
selected-entry pivot and some coordinates.  That loses the actual pivot
`pivotNext` and the supplied coordinates `yNext`.  The target is pointwise
instead:

```text
value (residualFactorProduct data.C (last 2) 0)
  (residualCoordEquiv.symm pivotNext)
    = yNext pivotNext.
```

Consequently, the product has a nonzero entry under the concrete hypothesis

```text
yNext pivotNext != 0.
```

The fixed-base p.13 source-readback version replaces `data.C` by the `C` field
of the source readback of the fixed-base source edge family built from `data`.
The just-landed source-readback theorem says this readback is exactly `data`,
so the same pointwise readout follows by rewriting.

## Calculation

Start from the endpoint-transported selected-entry matrix identity:

```text
P = matrix (fun c => chartMap pivotNext yNext (residualCoordEquiv c)).
```

Evaluate both sides at

```text
c0 := residualCoordEquiv.symm pivotNext.
```

Using `AoyagiResidualBlockCoordinateIndex.value_matrix`,

```text
value P c0
  = chartMap pivotNext yNext (residualCoordEquiv c0).
```

By the inverse law for `residualCoordEquiv`,

```text
residualCoordEquiv c0 = pivotNext.
```

Then the selected-entry chart's pivot rule gives

```text
chartMap pivotNext yNext pivotNext = yNext pivotNext.
```

Thus the fixed-pivot entry is exactly the supplied pivot coordinate.

For the fixed-base source chart, let

```text
E(yNext) :=
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges ...
    (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData ... data).
```

The source-readback theorem gives

```text
sourceReadback E(yNext) = data.
```

Applying congruence to the residual-factor product and then the pointwise
entry readout gives the fixed-base source-readback version.

## Boundary

This proves a fixed-pivot readout and fixed-pivot nonzeroness for the actual
endpoint-transported Case 2 datum, and for the fixed-base source readback of
the source edge family built from that datum.  It removes the all-pivot
existential ambiguity for this constructed branch.

It still uses supplied endpoint equivalences.  It does not identify those
equivalences as canonical or label preserving.  It does not produce `hyNext`;
it consumes the concrete nonzero pivot-coordinate hypothesis.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The residual-factor product entry indexed by
`residualCoordEquiv.symm pivotNext` is `yNext pivotNext`, hence nonzero under
`hyNext`; the same statement holds after fixed-base source readback for the
constructed p.13 source edge family.

**Assumed.** The endpoint equivalences `eNext` and `e`, determinant-continuity
fixed-base context, and the Case 2 continuation hypotheses `hS`, `hcont`, and
`hnext`.  The nonzero theorem assumes `hyNext`.

**Deferred.** Construction of `tau`/`hTau`, canonical endpoint labelling,
selected-entry label preservation under noncanonical endpoint equivalences,
arbitrary `ofTopologyTuple` alignment, source-prior transport, Jacobian
comparison, normal crossings, pole order, and RLCT.
