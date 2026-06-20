# A4 Case 2 Source-Chart Terminal Source-Suffix

Status: reproduced the constructor-level source-chart terminal source-suffix
wrappers.  These are compositions of already proved supplied-boundary
theorems; they are not chart coverage or global source-production theorems.

## Source Anchor

On Aoyagi PDF pp. 20-22, the displayed Case 2 chart selects the pivot
coordinate `(J+1,J+1)`, rewrites the residual block by the source chart
coordinate, applies the `Q/P` calculation, and then handles the stopped
terminal branch.

The Lean source-chart constructor fixes the selected variable to be

```text
v = case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1).
```

It packages the displayed boundary with post recurrence state

```text
pre.case2Succ v
```

and with the corrected selected-label exponent overrides.

## Pen-And-Paper Reproduction

The supplied terminal source-suffix theorems already have the source-shaped
left side:

```text
blockdiag(diag(pre.weight 1..J), P/Q tail) *
[old source rows 1..J ; source following rows J+1..] *
prod_{s=S+2}^L C^(s).
```

The constructor

```text
of_sourceChartMap_case2Succ_updateSelected
```

specializes the abstract displayed boundary to the source chart value `v`.
Therefore the old displayed post-state is no longer arbitrary: it is
`pre.case2Succ v`, and the selected exponent data are the corrected Case 2
updates.

There are two terminal stopped sides.

In the actual-width side,

```text
n(S+1)=J+1,
```

the post-pivot column correction in the top row of `Q^-1 C` is empty.  The
terminal matrix can be the original source rows:

```text
Cterm(i,-) = C(i,-),       i=1,...,J+1.
```

The terminal scalar is read from the relabelled actual-width post-state:

```text
(pre.case2Succ v).stageRelabelSuccZero.weight(J+1).
```

In the current-prefix row-exhausted side,

```text
prefixMinNat n S = J+1,
```

the next continuation bound fails, but the actual next width need not be
exhausted.  The terminal prefix rows are `1..J+1`, and the last row remains
the transported top row:

```text
Cterm(J+1,-) = (Q^-1 C)_top.
```

It is not generally the original row `C(J+1,-)`.

## Lean Shape

The proved source-chart wrappers are:

```text
exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
```

Both are direct compositions:

```text
let data :=
  of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
    exponentPre levelInv leastValueGap chartFamily
simpa [data] using data.<terminal theorem> ...
```

## Boundaries

- The chart-family predicates remain supplied.
- The old following matrix `C` and suffix matrices `Ctail` remain supplied.
- The source suffix is source-shaped, but not derived from a global
  chart-produced matrix chain.
- The source-chart map is not an atlas or coverage theorem.
- The exponent/post data are selected by the constructor; they are not proved
  from a full chart-production or transition invariant.
- No Jacobian, normal-crossing, RLCT, termination, or full
  source-produced `C'^(S+1)` conclusion is proved.
- The row-exhausted theorem does not use the `(S+1,0)` relabelled post-state.

## Kill Conditions

- Do not replace the transported row `J+1` by the original row in the
  row-exhausted branch without `n(S+1)=J+1`.
- Do not treat `case2DisplayedSourceChartMap` as proving chart coverage.
- Do not drop the supplied status of `chartFamily`, `C`, or `Ctail`.
