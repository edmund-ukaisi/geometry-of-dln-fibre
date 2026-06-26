# Statement card - A6 Definition 3 `L=2` branch formula rank-width removal

Date: 2026-06-26.

## Lean declarations

File:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

New rank-width helper theorems:

```text
AoyagiDefinition3SourceData.rank_le_of_aoyagiReducedWidthInt_eq_natCast
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_three_reducedWidthInt_eq_natCast
AoyagiDefinition3SourceData.allSourceStrict_of_L_eq_two_triangle_widths
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_L_eq_two_triangle_widths
```

New branch-specific formula wrappers:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
```

## Statement

The existing `L=2` repeated-positive and triangle parity formula packages
required an explicit source-range rank-width hypothesis:

```text
forall s, 1 <= s -> s <= 3 -> r <= H s
```

The new wrappers discharge that hypothesis from the concrete width data already
present in each branch.

For the repeated-positive branch, natural-width identities

```text
aoyagiReducedWidthInt H r s = (w : Int)
```

imply `0 <= aoyagiReducedWidthInt H r s`, hence `r <= H s` after unfolding the
integer reduced width.  Applying this at `s=1,2,3` supplies the source-range
rank-width input to the existing repeated-positive `_rankWidth` formula
theorem.

For the all-source triangle branch, the three inequalities

```text
2*w_i < w1+w2+w3
```

together with the three width identities give the all-source strict selected
inequality.  The existing theorem
`sourceRangeRankWidth_of_all_selected_strict` then derives source-range
rank-width before the odd/even parity wrappers delegate to the existing
triangle parity `_rankWidth` formula theorems.

## Source reproduction

`threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`

This uses only the finite Definition 3/Theorem 2 branch data from Aoyagi
PDF pp. 8-9 and the already recorded branch-selection audit:
`threads/06-dln-translation/source-audit-definition3-branch-selection-a6.md`.

## Review

`threads/06-dln-translation/review-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`

## Verification

Whitespace and forbidden-marker checks passed:

```text
git diff --check
cd lean
scripts/sorries
```

Focused module build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

## Nonclaims

This is finite Definition 3/Theorem 2 branch-specific arithmetic.  It does not
choose a canonical branch, prove branch independence, add a final socket,
construct Eq5 payloads or charts, prove normal crossings, identify pole order,
or extract RLCT.
