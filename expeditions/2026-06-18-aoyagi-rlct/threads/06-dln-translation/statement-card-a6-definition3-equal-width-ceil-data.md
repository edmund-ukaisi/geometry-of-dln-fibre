# Statement card - A6 Definition 3 equal-width ceiling data

Date: 2026-06-24.

## Claim

The positive constant reduced-width hypothesis implies the source-range
rank-width bound `r <= H s`.  Combining this with the equal-width consecutive
source-data constructor produces the standard selected reduced-width ceiling
data package without separately supplying source data or rank-width.

## Source Status

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9 support the
equal-width lane.  The rank-width step is elementary arithmetic from Lean's
integer reduced-width definition:

```text
aoyagiReducedWidthInt H r s = (H s : Int) - (r : Int).
```

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-equal-width-ceil-data-a6.md`.

Review:
`review-definition3-equal-width-ceil-data-a6.md`.

Verdict: pass as a small arithmetic helper plus narrow packaging theorem.  The
slice is mostly a wrapper; its new arithmetic content is extracting `r <= H s`
from the constant Nat-valued reduced-width equality.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos
```

The package theorem returns consecutive cutpoints, equal-width Definition 3
source data, selected reduced widths, a Definition 3 ceiling datum, Nat-width
rewrites, nonnegativity, strict selected inequalities, selected-width upper
bounds, and the pointwise equal-width identity `m j = w`.

## Nonclaims

No arbitrary Definition 3 selected-cutpoint existence, no closed form or
uniqueness for `ceilWidth` or `aParam`, no Eq5 payload, no finite exponent
formula, no chart production, no normal crossings, no pole order, and no RLCT
extraction.
