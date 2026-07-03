# Reproduction - A2 with-following source-rank readback and local intersection

Status: pen-and-paper reproduction before Lean.

## Claim

For the enlarged Case 2 with-following endpoint source chart, source-rank
membership on the p.13 source side reads back to the two theta-side rank
equations:

```text
r + rank(z.2) = rEdge 0
r + rank(successor selected-entry matrix(z.1.yNext)) = rEdge 1,
```

where `z` is the with-following source-chart readback of the source family.

After shrinking to the existing local p.13 image-equality patch, the local
image cut by the source-rank stratum is exactly the image of the theta-side
rank-equation locus.

## Pointwise Readback Calculation

Let `X` be an endpoint source edge family in the retained-passive p.13 source
set and in the source-rank stratum for `(r, rEdge)`.  Let

```text
E    = edgeMatrixOfReverseEdges(X),
data = sourceReadback(E),
z    = withFollowingSourceChartReadback(X).
```

The p.13 source-set hypothesis says `E` is in the source-recursive determinant
chart, hence `data.detChart`.  The selected-pivot nonzero hypothesis on `z`
gives the already-proved readback identity

```text
endpointRetainedData(z) = data.
```

Since `X` is in the p.13 source set, the p.13 partial inverse also gives

```text
p13SourceEdgeFamilyOfData(data) = X.
```

Transporting the source-rank membership of `X` across this equality and applying
the retained-passive reverse rank lemma gives, for `p = 0, 1`,

```text
rank(data.C p) = rEdge p - r.
```

The source-rank stratum also includes the inequalities `r <= rEdge p`.

For `p = 0`, the with-following readback stores the transported `C 0` block as
the independent following factor.  Endpoint transport preserves matrix rank, so

```text
rank(data.C 0) = rank(z.2).
```

Combining this with `rank(data.C 0) = rEdge 0 - r` and `r <= rEdge 0` gives

```text
r + rank(z.2) = rEdge 0.
```

For `p = 1`, the with-following readback reads `yNext` from the transported
`C 1` block by applying the selected-entry inverse on the pivot-nonzero locus.
The displayed residual-block rank lemma identifies this block's rank with the
rank of the successor selected-entry matrix:

```text
rank(data.C 1) = rank(successorMatrix(z.1.yNext)).
```

Together with `rank(data.C 1) = rEdge 1 - r` and `r <= rEdge 1`, this gives

```text
r + rank(successorMatrix(z.1.yNext)) = rEdge 1.
```

## Local Intersection

On the existing local patch `V`, we already have

```text
sourceChart '' V = p13SourceSet ∩ readback^{-1}(V),
readback(sourceChart z) = z for z in V,
detChart(endpointRetainedData z),
pivotNonzero(z.1).
```

The forward inclusion is the previous checkpoint: if `z in V` satisfies the
two theta-side rank equations, then `sourceChart z` is in the source-rank
stratum.

For the reverse inclusion, take `E in sourceChart '' V ∩ sourceRankStratum`.
Write `E = sourceChart z` with `z in V`.  The local p.13 support gives
`E in p13SourceSet`, the local pivot condition gives `pivotNonzero(z.1)`, and
the local left inverse gives `readback E = z`.  Applying the pointwise readback
calculation to `E` therefore gives the two rank equations for this same `z`.

Thus

```text
sourceChart '' {z | z in V and the two rank equations}
  = sourceChart '' V ∩ sourceRankStratum.
```

Using the p.13 local image equality, the right side can also be rewritten as

```text
(p13SourceSet ∩ readback^{-1}(V)) ∩ sourceRankStratum.
```

## Boundary

This is a local chart-image intersection theorem.  It still does not prove
global source-rank coverage, finite atlas coverage, source-prior transport,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction.  It
does not assert that the full source-rank stratum is covered; only the returned
local p.13 chart image is identified with the theta-side rank-equation locus.
