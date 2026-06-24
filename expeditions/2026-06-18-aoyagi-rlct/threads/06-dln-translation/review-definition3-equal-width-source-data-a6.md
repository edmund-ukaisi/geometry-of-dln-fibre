# Review - Definition 3 equal-width source data

Date: 2026-06-24.

Reviewer: xhigh independent scout `Carson the 2nd`.

## Verdict

PASS for the narrow equal-width source-data constructor.

The scout checked Aoyagi PDF pp. 8-9 and reported that the equal-width example
supports the choice `ell = L` independently of the quiver-based paper.  The
source-backed Lean construction is to choose all source layers as selected
cutpoints, zero-based as `C.cut j = j.val + 1`.

## Checked Calculation

Under the hypothesis

```text
M^(s) = w > 0       for all 1 <= s <= L+1,
```

the consecutive selected cutpoints give selected sum `(L+1)w`.  For every
selected width,

```text
Lw < (L+1)w
```

because `w > 0`, proving the strict selected inequality.

The nonselected hypotheses are impossible in the current Lean model because
`AoyagiDefinition3SourceData` uses value-level membership in the selected
width set.  Every source-range width value is `w`, and `w` is selected.

## Required Hypotheses

- `0 < L`, because the structure requires `ell_pos`.
- `0 < w`, because otherwise the strict selected inequality becomes
  `0 < 0`.
- Constancy over the full source range `1 <= s <= L+1`, not only at selected
  cutpoints, so that the nonselected clauses are vacuous.

## Caveats

This is genuinely source-moving for Aoyagi's equal-width example, but it is
not a general Definition 3 source-data existence theorem.  Because the Lean
source-data structure treats nonselectedness by width value, equal-width
profiles also make the nonselected clauses vacuous for smaller selected value
sets; to match Aoyagi's printed equal-width example, the theorem must
explicitly choose `ell = L` and all consecutive cutpoints.

## Lean Readiness

Recommended target:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos
```

in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

The proof should construct `C.cut j = j.val + 1`, prove the selected sum by
rewriting every reduced width to `w`, and discharge nonselected fields by
contradicting the `notin selected value set` hypothesis using the selected
index `0 : Fin (L+1)`.
