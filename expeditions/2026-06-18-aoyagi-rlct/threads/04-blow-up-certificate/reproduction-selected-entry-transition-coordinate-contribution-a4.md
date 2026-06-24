# Reproduction - Selected-entry transition coordinate contribution

Date: 2026-06-24.

Status: parked after xhigh review; do not formalise as a new Lean wrapper.

## Question

The selected-entry coordinate postdata records the unique chart coordinate at a
transition-generated target point:

```text
coord_target = u * denom.
```

The displayed-overlap microcertificate contribution theorem already records the
same transition point's chart-map equality, loss monomial identity, formal
Jacobian/prior monomial identity, and local finite ratio/count/order facts.  This
slice asks whether we should package the coordinate equality together with that
existing contribution summary.

## Source Anchors

Aoyagi PDF pp. 19-22 supports the displayed Case 2 selected-entry blow-up
calculation around the pivot `(J+1,J+1)`: the pivot entry is the exceptional
coordinate `u`, the other selected center entries are written as `u` times
normalized coordinates, and the displayed chart transition is considered on the
overlap where the displayed normalized coordinate is nonzero.

The Lean all-pivot selected-entry family is a finite generalization of this
selected-entry algebra.  For this slice we only use it to move from an arbitrary
source pivot chart to Aoyagi's displayed target chart under the explicit
nonzero displayed denominator hypothesis.

## Pen-and-paper Calculation

Let `I` be the Case 2 residual-block center and let `p,q in I`, where `q` is
the displayed pivot.  In the source selected-entry chart at pivot `p`,

```text
z_p = u,
z_i = u y_i.
```

Let

```text
denom = y_q = normalized_p(q).
```

On the overlap `denom != 0`, the target chart at pivot `q` is obtained by

```text
u_q = u * denom,
y'_i = normalized_p(i) / denom.
```

Therefore the target chart's unique certificate coordinate is

```text
coord_q = u_q = u * denom.
```

The nonzero denominator is not needed to evaluate this coordinate, but it is
needed for the chart-map equality

```text
chartMap_q(target point) = chartMap_p(source point).
```

At the same target point the existing finite selected-entry certificate gives:

```text
loss = lossUnit * coord_q^(2*k),
jacobianPrior = jacobianPriorUnit * coord_q^h,
```

with `k=1` and `h=|I|-1`.  For the Case 2 residual-block center,

```text
|I| = (prefixMinNat n S - J) * (n(S+1) - J).
```

Thus the local finite ratio, finite minimum, displayed-chart count at that
ratio, displayed-chart minimum count, and finite order remain the already-banked
values:

```text
ratio = |I| / 2,
minimum = |I| / 2,
countInDisplayedChartAtRatio = 1,
minCountInDisplayedChart = 1,
order = 1.
```

## Lean Shape Considered

The initially considered theorem was a wrapper in
`SelectedEntryNormalCrossing.lean`, next to the existing displayed-overlap
summary:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_coordinateContribution_summary_of_displayed_normalized_ne_zero
```

It should reuse
`sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero`
and add the conjunct

```text
Cnc.coord displayedChart
  (sourceChartTransitionPoint ... sourceChart displayedChart u residual)
  (0 : Fin 1)
= targetU.
```

The displayed nonzero-normalized-coordinate hypothesis would have remained
explicit because the summary includes the chart-map equality.

## Xhigh Review Decision

Independent xhigh scout `Turing the 3rd` rejected this as redundant finite
plumbing.  The proposed theorem would only conjoin two existing facts:

```text
coord_sourceChartTransitionPoint_eq_sourceSelected
sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero
```

It produces no successor chart/source data, no suffix data, no analytic
transition regularity, no coverage, no coordinate-derived recurrence or
exponent postdata beyond the already landed coordinate value, and no A0/A6
final-socket discharge.  Under the current A4 kill condition, it should not be
formalised unless a downstream theorem directly consumes exactly this
conjunction.

## Nonclaims

- No analytic chart domains.
- No analytic atlas coverage.
- No transition regularity beyond finite chart-map equality on the displayed
  nonzero overlap.
- No source production of successor matrices, suffixes, recurrence post-data,
  or exponent post-data.
- No analytic Jacobian/volume-form theorem.
- No normal-crossing chart production.
- No pole order or RLCT extraction.
