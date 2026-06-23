# Statement card - A6 Definition 3 source-data local wrappers

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

Names:

- `AoyagiDefinition3SourceData.selected_strict_selectedReducedWidths`
- `AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData`
- `AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData`
- `AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData`
- `AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData`
- `AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack`
- `AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`

## Claim

For the selected reduced-width family

```text
m = aoyagiSelectedReducedWidths H r C,
```

the strict selected inequality already stored in
`AoyagiDefinition3SourceData L ell H r C` supplies the `hsource` input needed
by the existing Definition 3/Lemma 5 local arithmetic wrappers.

## Inputs Kept Explicit

- supplied selected cutpoints `C`;
- supplied source data `S : AoyagiDefinition3SourceData L ell H r C`;
- supplied or previously constructed ceiling datum
  `data : AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C)`;
- the same local index/slack guards already required by the existing
  wrappers.

## Proved

The wrappers project:

```text
forall i, ell * m_i < sum_j m_j
```

from `S.selected_strict`, then reuse existing Lean arithmetic to prove the
selected-width upper bound and local Eq3/Eq4/Eq5 label-bound packages.

The aggregator theorem additionally packages:

```text
exists m data,
  m = aoyagiSelectedReducedWidths H r C
```

together with natural-width rewrites, selected-width nonnegativity, strict
selected inequality, the selected upper bound `m_i <= data.ceilWidth - 1`, and
Nat-indexed selected-width nonnegativity, all under an explicit source-range
rank-width hypothesis.

## Not Proved

No selected-cutpoint construction, no nonselected inequality construction, no
rank-width theorem from the matrix problem, no Lemma 5 chart coverage or
no-extra exactness, no pole order, and no RLCT extraction.

## Review

Xhigh review passed.  Review artifact:
`review-definition3-source-data-local-wrappers-a6.md`.
