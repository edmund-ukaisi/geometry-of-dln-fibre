# A4 Case 1(2) Selected-Old Supplied Chart-Family Boundary

Status: reproduced the supplied chart-family boundary combining the
selected-old pullback package with Case 1 finite chart-family regularity data.

## Source Situation

Aoyagi first chooses an old exceptional variable `u_(s,k)` at first-jump level
`J+J1` and then blows up the Case 1 center

```text
u_(s,k) = 0,
d_ij = 0,    J+1 <= i <= J+J1,    J+1 <= j <= M^(S+1).
```

In the displayed Case 1(2) chart, the row-strip pivot is `(J+1,J+1)` and the
old variable is rewritten as

```text
u_(s,k) = u_(S,J+1) * u'_(s,k).
```

The relevant source pages are Aoyagi PDF pp. 15-19: first-jump choice and
recurrence on p. 15, Case 1 center and displayed Case 1(2) chart on pp. 16-17,
the displayed `Q/P` calculation on p. 18, and the continuation/advance split
on p. 19.

## Pen-And-Paper Compatibility Check

The selected old source label data does not come from the finite center token
alone. In Lean, the `Unit` branch of

```text
Case1CenterGenerator = Unit + (Nat x Nat)
```

records only the old-generator chart token. The actual label `(s0,k0)`, its
introduced-label proof, and its level `J+J1` are supplied by the selected-old
pullback boundary.

The displayed row-strip pivot membership is finite bookkeeping:

```text
1 <= J1,
J+1 <= n(S+1)
```

give

```text
Sum.inr (J+1,J+1) ∈ case1CenterGenerators n S J J1.
```

The chart-family regularity facts are therefore projections from a supplied
boundary:

```text
Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular.
```

They do not construct regular charts. The source-order and exponent-domain
projections are reused from the selected-old pullback boundary.

## Lean Boundary

Lean now proves

```text
Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary
```

with projection theorems:

```text
sourcePullback_selectedIntroduced
selectedLevel
selectedOld_mem_center
displayedPivot_mem_center
chart_regular_selectedOld
chart_regular_displayedPivot
transition_regular_selectedOld_displayedPivot
transition_regular_displayedPivot_selectedOld
source_step_eq_mulStepAt
sourceOrder_identity
extendExponentDomain
```

## Caveats

- Chart regularity and transition regularity are supplied fields.
- This does not construct a blow-up atlas or prove chart coverage.
- This does not derive the source label `(s0,k0)` from the `Unit` token.
- This does not construct the raw-coordinate-to-`source` pullback.
- This does not prove Jacobian accounting, normal crossings, or RLCT
  extraction.
