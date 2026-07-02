# Statement Card - A6 Theorem 2 Terminal And Regular Sockets Source-Data Rank-Width Removal

Date: 2026-07-02.

## Claim

For selected downstream terminal-order, Eq5 terminal-order, and supplied
regular-suspension handoffs, Definition 3 source data supplies the source-range
rank-width hypothesis in the natural `L=2` and `ell=1` cases.

## Source Status

This uses Aoyagi Definition 3 on PDF pp. 8-9 only through already-formalized
rank-width consequences:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_L_eq_two_sourceData
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_ell_eq_one
```

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean
lean/DLNFibre/DLN/Aoyagi/Theorem2RegularSuspensionFinalBridge.lean
```

Lean names:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_terminalMinimumCountDatumClassifier
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_terminalMinimumCountDatumClassifier
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_suppliedRegularSuspension
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData_suppliedRegularSuspension
```

Review:
`review-theorem2-terminal-regular-sockets-source-data-rankwidth-removal-a6.md`.

## Nonclaims

No terminal classifier construction, no Eq5 payload construction, no
regular-suspension certificate construction, no branch selection, no
branch-independent formula, no normal-crossing construction, and no RLCT
extraction.
