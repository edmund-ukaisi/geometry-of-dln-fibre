# Review - A4 Case 2 all-pivot and row-index source bridges

Date: 2026-06-24.

Reviewer: Helmholtz, xhigh read-only review.

Status: pass, no blocking findings.

## Scope

Reviewed the current checkpoint:

- `Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_eq_sourceSelectedChartMapOfMem`;
- `exists_case2DisplayedQP_mul_sourceSubstitution_of_rowIndex_monomialRec`;
- `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_rowIndex_monomialRec`;
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`;
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem`;
- the reproduction notes, statement cards, and ledger updates for the two A4
  bridge clusters.

## Findings

No blocking findings.

The Lean additions are correctly scoped.  The selected-entry chart-family
adapter is definitional over `case2SourceSelectedChartMapOfMem`.  The
row-index source-substitution theorem rewrites by
`case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst` and reuses the
existing row-index `Q/P` theorem.  The all-pivot source-point adapter delegates
to the generic selected-entry family and proves only chart-map equality at
that point.

The source boundary is appropriate after wording cleanup.  The all-pivot
adapter should be described as a supplied-pivot source-selected finite map,
not as an arbitrary-pivot paper formula.  The normal-crossing disclaimers
should distinguish the existing finite formal selected-entry certificate from
any analytic/global normal-crossing theorem.

## Review Caveat

The reviewer did not run builds or edit files.  Local PDF extraction tools were
unavailable, so source-fidelity review used the existing A4 page-image/source
artifacts quoting Aoyagi pp. 19-21.  Mechanical verification is recorded in
the statement cards.
