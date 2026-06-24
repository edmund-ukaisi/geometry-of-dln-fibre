# Review - Definition 3 selected/nonselected redundancy

Date: 2026-06-24.

Reviewer: Mendel the 2nd, xhigh read-only scout.

Verdict: PASS for the narrow target.

## Findings

Full selected-cutpoint or `AoyagiDefinition3SourceData` existence is not a
viable next target.  Aoyagi Definition 3 is currently formalised as supplied
selected cutpoints satisfying displayed conditions, not as an existence
algorithm.

The narrow elementary target is valid: derive the
`selected_lt_nonselected` field from strict selected inequalities,
nonselected upper inequalities, and rank-width nonnegativity for selected
widths.

## Recommended Lean Shape

Pure arithmetic theorem:

```text
aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe
```

Constructor:

```text
AoyagiDefinition3SourceData.of_selectedStrict_nonselectedLe_rankWidth
```

The constructor should keep selected cutpoints, cutpoint bounds, rank-width,
strict selected inequalities, and nonselected upper inequalities explicit.

## Risks

The selected-width nonnegativity input is necessary.  Without a rank-width
hypothesis giving `0 <= M^(S_i)`, the integer implication can fail.

Downstream value is modest: this removes one redundant source-data field, but
does not yet create selected cutpoints or construct Lemma 5 families.

## Nonclaims

No selected-cutpoint construction, no `AoyagiDefinition3SourceData` existence
from arbitrary dimensions, no matrix-rank source theorem, no Eq5 branch
construction, no Lemma 5 exactness, no chart production, no normal crossings,
no pole order, and no RLCT.
