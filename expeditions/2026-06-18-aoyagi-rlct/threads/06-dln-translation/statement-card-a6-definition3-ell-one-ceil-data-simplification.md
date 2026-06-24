# Statement card - A6 Definition 3 `ell=1` ceiling-data simplification

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-definition3-ell-one-ceil-data-simplification-a6.md`.

Review:
`review-definition3-ell-one-ceil-data-simplification-a6.md`.

## Target

Prove finite simplification lemmas for an arbitrary
`AoyagiDefinition3CeilData 1 m`, independent of how the datum was constructed.

## Lean Artifacts

Declarations in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3CeilData.aParam_eq_one_of_ell_eq_one
AoyagiDefinition3CeilData.selectedSum_eq_ceilWidth_of_ell_eq_one
AoyagiDefinition3CeilData.ceilWidth_eq_selectedSum_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2OrderFormula_eq_one_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one
AoyagiDefinition3CeilData.theorem2Lambda_fromCeilData_eq_regularTerm_add_selectedPair_half_of_ell_eq_one
```

These prove that for any `data : AoyagiDefinition3CeilData 1 m`:

```text
data.aParam = 1
sum_j m_j = data.ceilWidth
data.ceilWidth = sum_j m_j
data.theorem2OrderFormula = 1
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
  aoyagiTheorem2RegularTerm L H r
    + aoyagiSelectedWidthPairSum 1 m / 2
```

and, when `m 0 = u`, `m 1 = v`:

```text
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
  aoyagiTheorem2RegularTerm L H r + u*v/2.
```

## Boundaries

- This is finite arithmetic for already supplied `ell=1` ceiling data.
- It does not construct selected cutpoints or source data.
- It does not choose a branch or assert branch independence.
- It does not build Eq5 payloads, charts, normal crossings, pole order, or
  RLCT.

## Verification

Controller focused elaboration passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Independent xhigh review passed with no findings.
