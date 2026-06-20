# Statement card - A4 Case 2 source terminal product form

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul`

## Statement

Lean now proves that the source-row terminal product candidate is the product
of the separately named source-row terminal weight and source-row terminal
next-factor candidate, followed by the supplied suffix:

```text
case2DisplayedSourceTerminalProductReindexedCandidate Wold ... F
  =
(case2DisplayedSourceTerminalWeight Wold b0 *
  case2DisplayedSourceTerminalCprimeCandidate ... C) * F.
```

## Proved

- Source-row reindexing commutes with the terminal weight times terminal
  next-factor product.
- Source-row reindexing also commutes with the final right multiplication by
  the supplied suffix.
- The candidate product can now be used computationally in its factorized
  source-row form.

## Assumed

- Only the data needed to define the candidate matrices: source old-top weight,
  residual/following-factor data, continuation bound, and suffix `F`.

## Not Proved

- No chart-produced `C'^(S+1)`.
- No proof that the supplied source terminal next-factor candidate is the full
  transformed source matrix from Aoyagi's chart.
- No chart coverage, coordinate regularity, Jacobian arithmetic, normal
  crossings, RLCT extraction, termination, transition invariant, automatic
  Case 2 gap/tail transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-terminal-product-form-a4.md`.
- Review artifact:
  `review-case2-source-terminal-product-form-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
