# Reproduction - A2 Case 2 source chart-point coverage

Date: 2026-06-29.

Status: pen-and-paper reproduction before Lean.

## Question

The generic all-pivot selected-entry finite certificate covers every finite
center value by a chart point.  For Case 2, can we record the same fact in the
source-coordinate presentation already used by the residual-block selected
entry algebra?

## Source anchor

Aoyagi's Case 2 selected-entry calculation on PDF pp. 19-22 uses the displayed
top-left residual-block entry as the selected coordinate and writes the block
coordinates in the form

```text
x_p = u,
x_i = u r_i     for i != p.
```

The theorem below is not a new source claim that Aoyagi prints an all-pivot
atlas.  It is expedition-built finite coordinate bookkeeping for the
all-pivot residual-block certificate, obtained by varying the displayed
selected-entry formula over possible residual-block pivots.

## Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S J
```

be the finite residual-block pivot set.  Under `hS : 1 <= S` and
`hcont : J + 1 <= prefixMinNat n (S + 1)`, this center is nonempty.  The
Case 2 all-pivot finite certificate is the generic selected-entry chart family
for this center.

Given a finite residual-block center value

```text
value : center -> K,
```

the generic selected-entry inverse gives:

```text
exists c, exists u, exists residual : (Nat x Nat) -> K,
  chartMap_c(sourceChartPoint_c(u,residual)) = value.
```

Concretely:

1. If `value` is zero, choose any residual-block pivot `p`, take `u = 0`, and
   take every residual coordinate to be zero.
2. Otherwise choose a residual-block pivot `p` with `value_p != 0`, take
   `u = value_p`, and take

```text
residual_i = value_i / value_p
```

for residual-block entries `i != p`.  Outside the finite residual block the
ambient residual function may be arbitrary; the existing Lean adapter
`sourceChartPoint` erases everything except the non-pivot center entries.

Then the chart map sends this source chart point to `value`, and the unique
certificate coordinate is

```text
coord_0(sourceChartPoint_c(u,residual)) = u.
```

## Lean target

Add to namespace
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`:

```text
exists_sourceChartPoint_chartMap_eq_value
exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq_sourceSelected
```

The first theorem should specialize the generic theorem

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
  .exists_sourceChartPoint_chartMap_eq_value
```

to the Case 2 residual-block certificate.  The second theorem should combine
the first theorem with the existing coordinate readout

```text
coord_sourceChartPoint_eq_sourceSelected
```

## Kill conditions

- The theorem claims analytic atlas coverage, source production of successor
  matrices/suffixes, normal crossings, pole order, or RLCT.
- The theorem claims Aoyagi prints all residual-block pivots rather than a
  displayed selected-entry chart.
- The theorem changes or weakens the existing Case 2 residual-block source
  coordinate convention.
- The proof uses the quiver paper or quiver Lean branch as evidence.
