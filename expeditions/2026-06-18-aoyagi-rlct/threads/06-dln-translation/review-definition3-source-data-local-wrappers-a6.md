# Review - A6 Definition 3 source-data local wrappers

Date: 2026-06-23.

Reviewer: xhigh read-only reviewer `Bacon`.

## Verdict

Pass; no required fixes.

The reviewed Lean slice stays within the intended boundary.  The new
`AoyagiDefinition3SourceData` wrappers only project the strict selected-width
inequality already stored in the supplied source-data package into existing
finite arithmetic APIs.  They do not construct selected cutpoints or derive
new source hypotheses.

## Lean/API Review

Reviewed artifact:

```text
lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Reviewed names:

```text
AoyagiDefinition3SourceData.selected_strict_selectedReducedWidths
AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData
AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData
AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth
```

The reviewer confirmed that the final aggregator keeps the source-range
rank-width hypothesis explicit, applies it only at the supplied selected
cutpoints using `C.pos` and `S.cut_le`, and returns only selected reduced
widths, ceiling data, natural-width rewrites, nonnegativity, the strict
selected inequality, and selected upper bounds.

## Boundary

This review does not certify selected-cutpoint existence, nonselected
Definition 3 consequences, rank-width hypotheses from concrete dimensions,
Lemma 5 coverage/no-extra exactness, chart production, pole order, or RLCT
extraction.

## Verification

The reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

The focused check passed.
