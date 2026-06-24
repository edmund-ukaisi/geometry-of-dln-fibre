# Review - Definition 3 equal-width ceiling data

Date: 2026-06-24.

Reviewer: xhigh independent scout `Russell the 2nd`.

## Verdict

PASS for a small arithmetic helper plus a narrow equal-width packaging theorem.

The reviewer classified the slice as mostly a wrapper, with one genuine
arithmetic extraction: the constant integer reduced-width equality implies the
source-range rank-width bound `r <= H s`.

## Checked Calculation

Lean defines

```text
aoyagiReducedWidthInt H r s = (H s : Int) - (r : Int).
```

If this equals `(w : Int)` for a natural number `w`, then it is nonnegative.
Therefore `(H s : Int) - (r : Int) >= 0`, hence `(r : Int) <= H s`, and so
`r <= H s` as a natural-number inequality.

This rank-width consequence can be fed to the existing
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`
after constructing consecutive equal-width source data.

## Required Hypotheses

- The helper rank-width theorem needs only the constant reduced-width
  hypothesis.
- The packaged equal-width theorem also needs `0 < L` and `0 < w`, as in the
  previous equal-width source-data constructor.

## Caveats

This theorem is not new source content beyond the rank-width arithmetic
consequence of the already-strong equal-width hypothesis.  It is useful
because it removes a repeated supplied source-data/rank-width bundle in the
equal-width lane.

## Nonclaims

No arbitrary Definition 3 selected-cutpoint existence, no closed form or
uniqueness for `ceilWidth` or `aParam`, no Lemma 5/Eq5 payload, no finite
exponent formula, no chart production, no normal crossings, no pole order, and
no RLCT extraction.
