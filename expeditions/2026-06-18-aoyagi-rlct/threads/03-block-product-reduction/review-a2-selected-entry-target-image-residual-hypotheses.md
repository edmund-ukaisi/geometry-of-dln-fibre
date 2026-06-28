# Review - A2 selected-entry target-image residual hypotheses

Date: 2026-06-28.

Reviewer: xhigh `Lagrange the 3rd`.

Verdict: PASS after statement-card typo fix.

## Findings

One low-severity documentation issue was found: the statement card wrote the
critical cast as `: R` instead of `: ℝ`.  The Lean theorem statement was
correct, and the statement card has been corrected.

No scoped Lean or mathematical correctness issues were found.

The theorem is honestly scoped to Lebesgue measure restricted to the selected-
entry target chart image,

```text
volume.restrict (chartMap pivot '' signedBoxSet R),
```

and the docstring/boundary text excludes retained-passive source production.

The proof composition is sound: it uses the selected-entry weighted source-box
theorem, the selected-entry chart pushforward theorem, the residual identity
`residual pivot y = aoyagiCoordinateSquareSum (chartMap pivot y)`, `ae_map_iff`
for positivity, and `lintegral_map_le` for finite lower-integral transport.

The hypotheses are correctly scoped: `0 <= t`, positive radii, and
`2 * t < ((center.erase pivot.1).card : ℝ) + 1`; `pivot : center` supplies the
only needed nonempty witness.

## Residual Risk

This remains finite selected-entry target-image measure bookkeeping.  It is
not retained-passive source production and does not identify a determinant-
chart measure with a selected-entry signed-box measure.
