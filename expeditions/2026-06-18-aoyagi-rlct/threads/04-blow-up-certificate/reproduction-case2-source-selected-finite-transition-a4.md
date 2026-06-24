# Reproduction - A4 Case 2 source-selected finite transition

Date: 2026-06-24.

Status: Lean formalised; focused/full build, sorry audit, and independent
xhigh review passed.  Independent xhigh source and strategy scouts passed the
target choice and denominator condition.

## Source Anchor

Aoyagi PDF pp. 19-21, Case 2:

- p. 19 starts Case 2 with the residual block `D_J = (d_ij)` and the
  displayed selected chart `d_(J+1,J+1) = u_(S,J+1)`;
- p. 20 introduces the normalized entries `d'_ij`, updates
  `b'_i = u_(S,J+1) b_i`, and uses the column-operation matrix `Q`;
- p. 21 introduces `C' = Q^(-1) C`, the row-operation matrix `P`, and the
  reduced block identity.

The Lean all-pivot selected-entry family extends the displayed top-left
selected-entry chart to arbitrary finite pivots in the residual-block center.
This extension is finite selected-entry algebra only.  Aoyagi displays the
top-left pivot chart; this note does not claim that the PDF writes every
non-top-left chart.

## Reproduction

Let `E` be the finite residual-block center.  In a selected-entry chart with
pivot `p in E`, write the normalized coordinate function as

```text
x_i = 1              if i = p,
x_i = residual_i     if i != p.
```

The finite center value represented by this chart is

```text
d_i = u * x_i.
```

Now choose another pivot `q in E`.  The correct chart-overlap denominator is
the normalized target coordinate:

```text
x_q != 0.
```

It is not enough to name the denominator as the center value `d_q = u*x_q`:
requiring `d_q != 0` would wrongly exclude exceptional-divisor points with
`u = 0` and `x_q != 0`.  On the actual overlap, define the target chart data

```text
u_q = u * x_q,
y_i = x_i / x_q.
```

Then the target chart has normalized target pivot

```text
y_q = x_q / x_q = 1,
```

and it represents the same finite center value.  At the target pivot,

```text
u_q = u * x_q = d_q.
```

For `i != q`,

```text
u_q * y_i
  = (u * x_q) * (x_i / x_q)
  = u * x_i
  = d_i,
```

using `x_q != 0`.

Thus the selected-entry finite chart maps agree on the normalized overlap.
The Case 2 source-selected wrapper is the same identity with

```text
x_i = case2SourceSelectedNormalizedMapOfMem hp residual i,
d_i = case2SourceSelectedChartMapOfMem hp u residual i.
```

The chart-index wrapper takes `p` and `q` from

```text
finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)
```

for the two chart indices.

## Not The Q/P Reduced-Block Transition

Aoyagi's pp. 20-21 `Q/P` calculation does more than change selected-entry
coordinates: it computes a reduced residual block after pivoting.  For an
arbitrary target pivot `q = (a,b)`, the reduced entries satisfy the
Schur-complement-style relation

```text
x_ab^2 * z_ij^(q) = x_ab * x_ij - x_ib * x_aj
```

for the appropriate off-pivot rows and columns.  The present Lean slice does
not formalise that reduced-block transition.  It proves only equality of the
finite selected-entry center value under the source and target selected-entry
presentations.

## Lean Targets

```text
selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero
case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero
```

## Boundary

- This is a finite selected-entry chart-map equality on the normalized
  target-coordinate overlap.
- It proves no analytic transition regularity, no chart coverage, no open
  neighbourhood statement, no source production of successor matrices or
  suffixes, no Q/P reduced-block transition, no analytic Jacobian/volume
  theorem, no global normal crossings, no pole order, and no RLCT extraction.
- It does not claim that Aoyagi displays non-top-left selected-entry source
  charts.

## Kill Conditions

- Do not replace the denominator condition `x_q != 0` by `u*x_q != 0`.
- Do not use this as `TransitionRegular`; the current transition-regularity
  API remains a supplied predicate.
- Do not identify equality of selected-entry center values with equality of
  reduced Q/P residual coordinates.
