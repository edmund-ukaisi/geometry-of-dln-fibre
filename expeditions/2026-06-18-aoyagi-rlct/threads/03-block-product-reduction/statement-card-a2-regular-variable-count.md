# Statement Card - A2 Regular-Variable Count

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`
- `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`

## Claim

The three regular block families isolated after Aoyagi Theorem 3 have finite
entry count

```text
r^2 + r(H^(L+1)-r) + (H^(1)-r)r.
```

Under endpoint rank-width bounds, half of this count equals the regular term
already appearing in Aoyagi Theorem 2's displayed lambda formula:

```text
(-r^2 + r(H^(1)+H^(L+1))) / 2.
```

## Lean Names

```text
aoyagiTheorem2RegularVariableCount
aoyagiTheorem2RegularTerm_eq_half_regularVariableCount
AoyagiNormalCrossingExponentData
  .exponentMinimum_jacobianPriorLossShift_regularVariableCount
AoyagiNormalCrossingExponentData
  .exponentOrder_jacobianPriorLossShift_regularVariableCount
AoyagiNormalCrossingChartCertificate
  .exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount
AoyagiNormalCrossingChartCertificate
  .exponentData_exponentOrder_jacobianPriorLossShift_regularVariableCount
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_regularVariableCountShift
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_chart_regularVariableCountShift
```

## Inputs Kept Explicit

- `r <= H 1`;
- `r <= H (L+1)`.
- reduced finite minimum plus the regular term equals the displayed Theorem 2
  lambda formula;
- reduced finite order equals the displayed Theorem 2 order formula.

## Not Proved

No regular-suspension chart construction, no analytic generator transport, no
Aoyagi Lemma 1, no regular-coordinate RLCT additivity, no normal-crossing
certificate production, no pole-order theorem, and no RLCT theorem.

## Verification

Run:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.FinalFormula
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.RegularVariableShift
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```
