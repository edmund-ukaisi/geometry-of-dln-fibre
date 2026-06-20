# A4 Case 2 Source-Chart Arbitrary-Suffix Actual-Width Boundary

Status: reproduced the actual-width displayed source-chart terminal boundary
with an arbitrary supplied following matrix `F`.

## Source Anchor

Aoyagi's stopped Case 2 terminal display on PDF pp. 21-22 multiplies the
terminal block by the remaining right product

```text
prod_{s=S+2}^L C^(s).
```

The arbitrary-suffix wrapper shows that this right factor can be kept as a
supplied matrix `F : Matrix τ υ R`, where `τ` is the output-column type of the
terminal `C'` block and `υ` is arbitrary.

## Pen-And-Paper Reproduction

For the displayed source chart, the selected coordinate is

```text
u = chartMap(J+1,J+1),
```

and the concrete post recurrence state is

```text
post = pre.case2Succ(u).
```

The already reproduced displayed source-chart `Q/P` calculation gives a
stopped terminal equality with source old-top rows:

```text
ideal((blockdiag(oldTopWeight, transformed residual block)
        * [old source rows ; source following factor]) * F)
  =
ideal((terminalWeight(post) * Cterm) * F),
```

where `F` is any supplied following matrix.

In the actual-width branch

```text
n(S+1) = J+1,
```

the transported pivot row has no post-pivot column correction.  Thus the
terminal bridge can take

```text
Cterm = original source rows 1..J+1.
```

The actual-width relabel also lets the surviving pivot weight be read from the
relabelled `(S+1,0)` state:

```text
post.stageRelabelSuccZero.weight(J+1) = post.weight(J+1).
```

Therefore the concrete displayed source-chart boundary is

```text
ideal((blockdiag(oldTopWeight, transformed residual block)
        * [old source rows ; source following factor]) * F)
  =
ideal((terminalWeight(post.stageRelabelSuccZero)
        * originalRows(1..J+1)) * F).
```

The level invariant and exponent-domain certificates are the same actual-width
relabelled certificates as in the existing source-suffix boundary.

## Lean Shape

The intended Lean names are:

```text
exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary
```

The existing source-suffix theorem is recovered by specializing
`τ = κ(sourceLayerIndex L (S+2))`, assuming `hSuffix : S+1 <= L`, and taking
`F = sourceSuffixProduct κ Ctail S hSuffix`.

## Boundaries

- `F` is supplied; this does not prove the remaining following product is
  chart-produced or equal to a source suffix.
- The actual-width original-row bridge uses exactly `n(S+1)=J+1`.
- The row-exhausted wide-next branch remains transported-row data, not
  original source rows.
- No chart coverage, source-produced `C'^(S+1)`, chart-produced post-data
  beyond the displayed constructor, Jacobian arithmetic, normal crossings,
  RLCT extraction, termination, transition invariance, or printed-vector
  repair is proved.
