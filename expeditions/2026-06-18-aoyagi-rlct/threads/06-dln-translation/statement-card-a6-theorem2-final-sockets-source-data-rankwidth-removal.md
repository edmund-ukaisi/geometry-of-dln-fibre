# Statement Card - A6 Theorem 2 Final Sockets Source-Data Rank-Width Removal

Date: 2026-07-02.

## Claim

For `ell=1` source data and for arbitrary `L=2` source data, the downstream
Theorem 2 supplied final-boundary sockets no longer need a separate
source-range rank-width hypothesis.  The needed rank-width proof is derived
from Definition 3 source data and then fed into the existing rank-width
wrappers.

## Source Status

This uses Aoyagi Definition 3 on PDF pp. 8-9 only through already-formalized
finite consequences:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_ell_eq_one
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_L_eq_two_sourceData
```

The normal-crossing extraction step remains supplied/cited.

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
lean/DLNFibre/DLN/Aoyagi/Theorem2RankWidthRegularShiftBridge.lean
```

Theorems:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_regularVariableCountShift
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData_regularVariableCountShift
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_regularVariableCountShift
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData_regularVariableCountShift
```

Review:
`review-theorem2-final-sockets-source-data-rankwidth-removal-a6.md`.

## Nonclaims

No branch-independent formula, no branch choice, no finite minimum/order
construction, no Eq5 or chart construction, and no analytic RLCT extraction.
