# Reproduction - A4 Case 1/Case 2 selected-entry finite coverage

Date: 2026-06-23.

Status: reproduced; Lean formalisation landed and focused build passed.

## Source Anchor

Aoyagi's Case 1 and Case 2 blow-up steps on PDF pp. 16-21 use
selected-entry substitutions of the form

```text
x_p = u,
x_i = u y_i  for i != p.
```

The generic finite selected-entry coverage calculation is recorded in
`reproduction-selected-entry-finite-chart-coverage-a4.md`.  This slice only
specializes that finite calculation to the two finite centers already used by
the all-pivot certificates:

```text
case2ResidualBlockPivotEntries n S J
case1CenterGenerators n S J J1
```

## Case 2 Specialization

In the displayed continuing Case 2 range, the hypotheses

```text
1 <= S,
J + 1 <= prefixMinNat n (S + 1)
```

give nonemptiness of `case2ResidualBlockPivotEntries n S J`.  The all-pivot
finite selected-entry certificate is definitionally the generic all-pivot
certificate for that finite center, with the canonical finite-subtype chart
enumeration.

Therefore, for every finite residual-block value

```text
value : {p // p in case2ResidualBlockPivotEntries n S J} -> K,
```

the generic coverage theorem gives a chart index and chart point mapping to
`value`.  If `value` is not zero, the chosen chart is a nonzero residual-block
coordinate; if `value` is zero, any residual-block pivot chart works.

## Case 1 Specialization

The Case 1 finite center

```text
case1CenterGenerators n S J J1
```

is always nonempty because it contains the old exceptional generator token.
The all-pivot finite selected-entry certificate is again the generic
all-pivot certificate for that finite center, with the canonical finite-subtype
chart enumeration.

Thus every finite Case 1 center value

```text
value : {g // g in case1CenterGenerators n S J J1} -> K
```

has a preimage in some selected-entry chart.

## Boundary

This is finite chart-map coverage only.

- no analytic atlas domains or neighbourhood coverage;
- no transition regularity;
- no source production for arbitrary Case 2 residual-block pivots;
- no source production for the hidden Case 1 selected-old label or arbitrary
  row-strip pivots;
- no analytic Jacobian or volume-form theorem;
- no normal-crossing certificate for the full DLN loss;
- no pole order or RLCT extraction.

## Kill Conditions

- Do not use these wrappers as source-coordinate formulas for arbitrary
  non-displayed Aoyagi pivots.
- Do not use finite chart-map coverage as analytic blow-up atlas coverage.
- Do not use these wrappers to discharge transition regularity, unit control,
  or source production obligations.
