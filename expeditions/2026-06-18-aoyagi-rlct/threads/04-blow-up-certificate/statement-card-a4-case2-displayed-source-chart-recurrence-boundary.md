# Statement card - A4 Case 2 displayed source-chart recurrence boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_case2Succ_postData`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_case2Succ_weight_update`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_case2Succ_residualRowWeight_update`

## Statement

Lean now records that the concrete Case 2 recurrence successor
`pre.case2Succ u` uses the displayed source chart's pivot value as its new
recurrence variable.  It also proves the corresponding displayed row-weight
update:

```text
(pre.case2Succ u).weight i
  = case2DisplayedSourceChartMap(...)(J+1,J+1) * pre.weight i
```

for every `i >= J+1`, and in particular for every residual-row index.

## Source Role

This mirrors the recurrence part of Aoyagi's displayed Case 2 calculation on
PDF pp. 19-21: the top-left selected coordinate is `u_(S,J+1)`, and the
successor recurrence weights satisfy `b'_i = u_(S,J+1) b_i` on the displayed
residual rows.

## Proved

- The concrete recurrence successor post-data can be stated using the
  displayed source chart pivot value.
- From the displayed continuation and stage bounds, the new label is a valid
  actual-width label for the recurrence update.
- All recurrence weights from `J+1` onward are multiplied by the displayed
  source chart pivot value.
- The same update holds on every Case 2 residual row.

## Assumed

- A pre-existing recurrence state at `(S,J)`.
- Displayed Case 2 bounds `1 <= S`, `S <= L`, and
  `J+1 <= prefixMinNat n (S+1)`.
- A source residual coordinate function.  The theorem uses only its displayed
  pivot value.

## Not Proved

- No affine chart construction or atlas coverage.
- No chart-produced exponent post-data.
- No Jacobian/volume arithmetic, coordinate regularity, normal crossings,
  RLCT extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-source-chart-recurrence-boundary-a4.md`.
- Review artifact:
  `review-case2-displayed-source-chart-recurrence-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
