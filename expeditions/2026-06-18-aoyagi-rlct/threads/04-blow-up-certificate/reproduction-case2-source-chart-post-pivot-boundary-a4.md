# Pen-and-paper reproduction - Case 2 source-chart post-pivot boundary

Status: checked supplied-data compatibility bridge for Aoyagi's displayed
Case 2 continuing branch.

This note connects two already isolated pieces:

- the displayed source-chart boundary whose post recurrence state is
  `case2Succ` at the displayed pivot value and whose exponent data are the
  corrected selected-label overrides;
- the post-pivot next-block adapter that reindexes the lower-right block
  after `D''' C'` onto the same-stage successor domains `(S,J+1)`.

It does not prove that the affine source chart produces recurrence data,
exponent data, chart-family regularity, transition invariance, a Jacobian, a
normal-crossing form, or an RLCT.

## Source

Aoyagi PDF pp. 19-22, Case 2:

- the displayed chart selects the top-left residual-block entry
  `d_{J+1,J+1}`;
- the chart writes every residual-block center coordinate as the selected
  coordinate times a chart coordinate;
- the paper performs the `Q/P` operations, writes `C' = Q^-1 C`, and obtains
  the cleared block `D'''`;
- if the process continues, the lower-right part after the displayed pivot is
  the next residual block at the same stage with `J` replaced by `J+1`.

The printed Case 2 exponent vector mismatch is separate.  Here the exponent
post-data are the corrected supplied overrides already isolated in Lean, not
the printed vector.

## Reproduction

Let the displayed source-chart pivot value be

```text
p = sourceChartMap(u,residual)(J+1,J+1).
```

For the source-displayed chart this value equals `u`, but the boundary records
it as the chart-map value so that the recurrence successor is literally

```text
post = pre.case2Succ p.
```

The corrected post-data boundary also records the selected-label updates

```text
t'          = updateSelectedLabelVector(S,J+1, correctedCase2PivotVector),
numerator' = updateSelectedLabelScalar(S,J+1,
                (M(S)-J)(M^(S+1)-J)),
leastValue'= updateSelectedLabelScalar(S,J+1, J).
```

These are supplied corrected data.  They are not derived from the chart in
this checkpoint.

Independently, after the displayed pivot the finite matrix calculation gives

```text
D_chart = [1  y]
          [x  D],

C' = Q^-1 C = [C'_0]
              [C'_tail],

D''' = [1 0]
       [0 D - x y].
```

Therefore

```text
D''' C' = [C'_0]
          [(D - x y) C'_tail].
```

The previous domain handoff identifies the lower row and lower column
complements with the next same-stage residual domains at `(S,J+1)`.  Thus the
lower part of `D''' C'`, after the pivot-complement row reindexing, is

```text
D_next C_next,
```

where `D_next` is the cleared lower-right block `D - x y` reindexed to
`Case2ResidualRowIndex(n,S,J+1)` by
`Case2ResidualColIndex(n,S,J+1)`, and `C_next` is the tail of `C'` reindexed
to `Case2ResidualColIndex(n,S,J+1)`.

The compatibility statement is only that the corrected source-chart boundary
and these supplied post-pivot matrix candidates point to the same successor
slot `(S,J+1)`.  If the stronger branch condition

```text
J+2 <= M(S+1)
```

holds, the next residual-block center at `(S,J+1)` is nonempty.

## Lean target

Add namespace projections:

```text
Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct
Case2DisplayedSuppliedChartFamilyBoundary.postPivotResidualBlock_nonempty_of_next
```

and a concrete source-chart package:

```text
Case2DisplayedSuppliedChartFamilyBoundary
  .sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData
```

The concrete package should combine:

- the lower-row product identity for `D''' * C'`;
- the corrected exponent-domain certificate at `(S,J+1)`;
- the post level/least-value bridge;
- the successor least-value Case 2 gap;
- the successor recurrence Case 2 gap.

## Kill conditions

- Do not say the chart produces recurrence or exponent post-data.
- Do not construct a successor chart-family boundary for `(S,J+1)`.
- Do not assert atlas coverage, transition invariance, coordinate regularity,
  Jacobian arithmetic, normal crossings, RLCT extraction, arbitrary pivot
  coverage, terminal relabeling, or repair of the printed Case 2 vector.
- Do not identify the full product `D''' C'` with the next product; only the
  lower rows are reindexed to the continuing branch.
