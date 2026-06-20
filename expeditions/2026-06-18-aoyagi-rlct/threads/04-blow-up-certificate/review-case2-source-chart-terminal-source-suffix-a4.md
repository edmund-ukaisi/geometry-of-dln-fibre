# Review - A4 Case 2 source-chart terminal source-suffix

Reviewed objects:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`

Verdict: no blocking source/math issue found at this scope.

The wrappers have the expected constructor-level shape.  They instantiate

```text
of_sourceChartMap_case2Succ_updateSelected
```

with the displayed source-chart selected value

```text
case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1),
```

then apply the already proved terminal source-suffix theorem in the appropriate
stopped branch.

The actual-width wrapper correctly uses the relabelled terminal pivot weight

```text
(pre.case2Succ chartValue).stageRelabelSuccZero.weight (J+1).
```

The row-exhausted wrapper correctly keeps the raw successor weight

```text
(pre.case2Succ chartValue).weight (J+1)
```

and keeps the pivot row as the top row of `Q^-1 C`, not as the original source
row.

## Caveats

- `chartFamily`, the exponent pre-data, level invariants, `C`, and `Ctail`
  remain supplied.
- The source suffix is source-shaped, but it is not derived from a global
  chart-produced matrix chain.
- These wrappers do not prove chart coverage, chart-produced post-data,
  Jacobian arithmetic, normal crossings, RLCT extraction, termination,
  transition invariance, or a full `C'^(S+1)` construction.
- The row-exhausted branch must not import original-row equality or the
  `(S+1,0)` relabel unless actual-width exhaustion is separately available.

## Lean Check

The file-level command

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

passed from the `lean/` project root after these wrappers were added.
