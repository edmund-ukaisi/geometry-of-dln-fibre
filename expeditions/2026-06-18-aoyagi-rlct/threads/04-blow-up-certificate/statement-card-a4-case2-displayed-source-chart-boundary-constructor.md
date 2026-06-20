# Statement card - A4 Case 2 displayed source-chart boundary constructor

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`

Supporting name:

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_case2Succ_postData`

## Statement

Lean now provides a displayed-source-chart version of the concrete displayed
Case 2 supplied-boundary constructor.  The boundary scalar is syntactically
exposed as the displayed source chart value

```text
case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1).
```

The post recurrence state is correspondingly

```text
pre.case2Succ
  (case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1)).
```

The exponent post-data remain the corrected selected-label update used in the
existing displayed concrete-update boundary.

## Source Role

This mirrors only the displayed top-left Case 2 naming on Aoyagi PDF
pp. 19-21: the selected chart coordinate is the new variable
`u_(S,J+1)`.  The theorem ties the supplied boundary's scalar and recurrence
successor to that displayed source-coordinate name.

## Proved

- The displayed supplied boundary can be constructed with scalar equal to the
  displayed source chart pivot value.
- The post recurrence state is the concrete successor for that same displayed
  pivot value.
- The corrected selected-label exponent post-data can be reused unchanged.
- The supplied chart-family predicates are carried through unchanged.

## Assumed

- A pre-state recurrence object at `(S,J)`.
- Displayed Case 2 bounds `1 <= S`, `S <= L`, and
  `J+1 <= prefixMinNat n (S+1)`.
- Pre-state exponent certificates, level/least-value bridge, and Case 2
  least-value gap.
- A source residual coordinate function.
- Supplied chart and transition regularity through
  `Case2ResidualBlockChartFamilyBoundary`.

## Not Proved

- No affine chart construction or chart production of all post-data.
- No chart-produced exponent post-data.
- No non-top-left displayed chart formulas or atlas coverage.
- No coordinate regularity from coordinates.
- No Jacobian/volume arithmetic, normal crossings, RLCT extraction,
  termination, full transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-source-chart-boundary-constructor-a4.md`.
- Review artifact:
  `review-case2-displayed-source-chart-boundary-constructor-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
