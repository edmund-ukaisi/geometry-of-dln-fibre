# Audit - A2 original loss to p.13 boundary

Date: 2026-06-25.

Auditor: xhigh `Lagrange the 5th`, read-only.

## Verdict

The original DLN/statistical loss to p. 13 coordinate bridge is not proved in
the current Lean development.

The safe next theorem boundary is conditional: assume explicitly that,
eventually on the fixed-base source-rank `nhdsWithin` filter,

```text
c0 * adaptedProductDifferenceSquareSum(x) <= originalLoss(x)
```

for some `c0 > 0`.  Under that hypothesis, the existing p. 13 finite machinery
can transfer the positive lower bound from `adaptedProductDifferenceSquareSum`
to `originalLoss` and then to the cleaned
`regularSquareSum + residualSquareSum`.

## Already In Lean

- `lossDLN` is the Frobenius square loss and has nonnegativity/zero-locus facts
  only.  It is not connected to the p. 13 fixed-base coordinates.
- The fixed-base endpoint coordinate and determinant-chart persistence
  machinery is formalised, but it does not prove source-rank openness or a
  global Aoyagi chart theorem.
- The literal and cleaned p. 13 square-sums are locally compared by factor `2`,
  including the half lower-bound form.
- The current self-base comparison lands only in
  `paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`, not in
  `lossDLN`.

## Elementary But Still Unformalised

- A named wrapper extracting `exists c > 0, c * literalSquareSum <=
  adaptedProductDifferenceSquareSum` from the self-base adapted theorem.
- Finite-dimensional norm/basis comparison between fixed-base adapted
  product-difference coordinates and the original Frobenius loss, up to a
  positive local constant.
- If the target is statistical KL/prediction loss rather than Frobenius square
  loss, an input covariance/noise lower-bound comparison.

## Boundary

Do not state `c * literal <= lossDLN` or `c * cleaned <= lossDLN` as
source-backed by Aoyagi p. 13.  Such a theorem must either prove or explicitly
assume the metric/covariance/basis bridge.
