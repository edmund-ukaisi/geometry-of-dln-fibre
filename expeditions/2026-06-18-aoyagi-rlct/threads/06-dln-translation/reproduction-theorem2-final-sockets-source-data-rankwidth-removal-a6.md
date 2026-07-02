# Reproduction - Theorem 2 Final Sockets Source-Data Rank-Width Removal

Date: 2026-07-02.

Status: controller reproduction; implemented and reviewed.

## Question

Several downstream A6 sockets already consume Definition 3 source data, but
still ask separately for source-range rank-width:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

For two source-backed cases this is now redundant:

- `ell=1`, by `sourceRangeRankWidth_of_ell_eq_one`;
- `L=2`, by `sourceRangeRankWidth_of_L_eq_two_sourceData`.

This slice removes that explicit rank-width input from the supplied final
boundary and regular-variable shifted final boundary in those two cases.

## Pen-and-paper Derivation

The existing final-boundary theorem has the form:

```text
S : AoyagiDefinition3SourceData L ell H r C
hr : forall s in source range, r <= H s
finite formula/extraction hypotheses
------------------------------------------------
exists m data, supplied final boundary plus selected-width side data
```

If `ell=1`, Definition 3 source data forces source-range rank-width.  The
proof is finite: every source-range reduced width lies in the two selected
values, and the two selected strict inequalities force both selected values
positive.  Hence all source reduced widths are nonnegative, so `r <= H s`.

If `L=2`, the already-formalized finite classification says source-data
existence is either:

- repeated-positive, where all three source reduced widths are positive; or
- triangle, where the three strict triangle inequalities imply positivity of
  each reduced width by adding the other two inequalities.

Again every source reduced width is nonnegative, so `r <= H s`.

Therefore in both cases the downstream socket is obtained by applying the
existing rank-width theorem with the derived `hr`.

## Lean Shape

In `Theorem2FinalAssembly.lean`, add final-boundary and chart-boundary wrappers
for:

```text
exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData
exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData
exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData
exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData
```

In `Theorem2RankWidthRegularShiftBridge.lean`, add the analogous
regular-variable shifted wrappers:

```text
exists_theorem2SuppliedFinalBoundary_of_L_eq_two_sourceData_regularVariableCountShift
exists_theorem2SuppliedFinalBoundary_of_ell_eq_one_sourceData_regularVariableCountShift
exists_theorem2SuppliedChartFinalBoundary_of_L_eq_two_sourceData_regularVariableCountShift
exists_theorem2SuppliedChartFinalBoundary_of_ell_eq_one_sourceData_regularVariableCountShift
```

Each proof is just delegation to the existing rank-width theorem with the
source-derived rank-width proof.

## Nonclaims

- No final Theorem 2 proof.
- No branch-independent formula or branch selection for arbitrary Definition 3
  data.
- No construction of finite minimum/order obligations.
- No construction of normal-crossing charts or Eq5 payloads.
- No pole-order/RLCT extraction beyond the supplied A0 extraction hypothesis.
