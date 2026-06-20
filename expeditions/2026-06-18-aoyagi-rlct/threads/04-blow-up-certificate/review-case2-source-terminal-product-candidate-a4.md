# Review - A4 Case 2 Source Terminal Product Candidate

Status: passed xhigh source/math and Lean/API review after API-name
hardening.

## Source/Math Review

No blocking source/math fidelity issues were found.

- Product orientation is correct: the terminal candidate remains
  `(blockdiag(Wold,[b0]) * [Cold; C0]) * F`, matching Aoyagi's left
  row-weight diagonal and right suffix product.
- Row indexing is coherent: old top rows are `1..J`, terminal rows are
  `1..J+1`, and `case2SourceTerminalRowEquiv` maps old rows to themselves and
  the surviving pivot row to `J+1`.
- Entry-ideal reindexing is legitimate: `matrixEntryIdeal_submatrix_equiv` is
  equivalence reindexing invariance and is used with the terminal-row
  equivalence and identity column equivalence.
- The docs and theorem comments do not claim chart-produced source data.

## Lean/API Review

No blocking Lean/API issues were found.

The API reviewer noted a low clarity risk: the source-row terminal product was
defined as a row reindexing of the stacked candidate, not by separately
multiplying the source-row weight and source-row `C'` definitions.  The Lean
name was therefore hardened to

```text
case2DisplayedSourceTerminalProductReindexedCandidate
```

The final source old-top/source suffix wrapper keeps the compiled name
`exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`,
while its right hand side is the reindexed candidate above.

## Residual Risk

The follow-up checkpoint

```text
case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul
```

now proves the product-form equality

```text
(source terminal weight * source terminal Cprime candidate) * F
```

for the existing reindexed candidate.  The remaining risk is source
production: this does not prove that the separately named source-row factors
are produced by Aoyagi's chart.
