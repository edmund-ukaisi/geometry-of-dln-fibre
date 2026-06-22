# Statement card - A6 supplied final assembly boundary

## Lean Names

File: `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`.

- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_apply_eq_reducedWidthInt`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_eq_natCast_sub`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidths_nonneg`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidthNat_nonneg`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.poleOrder_eq_theorem2OrderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_and_poleOrder_eq_expanded_and_orderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_average_selectedReducedWidths`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedFinalBoundary.lambda_eq_theorem2Lambda_expanded_selectedReducedWidths`

## Claim

A supplied final boundary packages selected-width provenance, the A0 extraction
hypothesis, and the finite exponent formula hypothesis.  From that supplied
boundary, Lean projects Aoyagi Theorem 2's displayed `lambda` formulas and
the displayed pole-order formula.

## Proved

Lean proves:

- selected widths agree with the integer reduced widths at the selected
  cutpoints;
- under separately supplied selected rank-width bounds, selected widths are Nat
  subtractions coerced to integers and are nonnegative;
- a separately supplied source selected-width inequality gives
  `m i <= data.ceilWidth - 1`;
- the A0 extraction hypothesis plus the supplied finite exponent formula
  equalities imply the ceiling-data, average, and expanded displayed
  `lambda` formulas and the displayed order formula.

## Assumed

The selected cutpoints, equality
`m = aoyagiSelectedReducedWidths H r C`, `AoyagiDefinition3CeilData`,
`AoyagiNormalCrossingExtractionHypothesis`, and
`AoyagiTheorem2FiniteExponentFormulaHypothesis` are supplied by the final
boundary.  Selected rank-width hypotheses and the source selected-width
inequality are supplied separately for the auxiliary width lemmas that use
them.

## Deferred

Selected cutpoint existence, Definition 3 source-selection proof,
rank-width inequalities from the matrix problem, normal-crossing chart
production, finite exponent formula equalities, chart coverage, unit factors,
Jacobian/prior exponent correctness, Lemma 5 no-extra coverage, Lemma 5 order
count, pole order without A0, and the analytic extraction theorem.

## Cited

A0 only, via the explicit `AoyagiNormalCrossingExtractionHypothesis`.

## Verification

Focused, module, and full-library checks pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed in
`review-theorem2-final-assembly-a6.md`.
