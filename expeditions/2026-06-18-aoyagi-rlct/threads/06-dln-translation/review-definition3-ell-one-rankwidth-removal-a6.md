# Review - Definition 3 `ell=1` Source-Data Rank-Width Removal

Date: 2026-07-02.

Reviewer: xhigh independent reviewer `Linnaeus`.

## Verdict

PASS.  No required corrections.

## Source And Math Check

The reviewer confirmed that

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_ell_eq_one
```

is mathematically valid.  For `ell=1`, the two selected strict inequalities
give positivity of the two selected reduced widths.  The existing
value-cover lemma then says every source-range reduced width is one of those
two selected values, hence nonnegative, hence `r <= H s`.

The proof uses only Definition 3 source-data clauses, through the existing
`reducedWidth_mem_selectedValueSet_of_ell_eq_one` lemma.  It does not use
quiver material or RLCT extraction.

## Lean/API Check

The reviewer checked that

```text
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_general
```

is exactly the old rank-width theorem with
`S.sourceRangeRankWidth_of_ell_eq_one` supplied.  It remains branch-specific
to supplied `ell=1` source data and the supplied selected cutpoints `C`.

Reviewer verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

passed from the `lean/` project root.

## Scope Check

No overclaim found.  The result does not infer `ell=1`, choose a canonical
selected pair from arbitrary data, assert branch-independent formula payloads,
construct Eq5 payloads or charts, prove normal crossings, or extract RLCT.

The finite displayed arithmetic `theorem2OrderFormula = 1` is part of the
returned finite formula package.  The nonclaim is only that no analytic
pole-order/RLCT extraction is proved.
