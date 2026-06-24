# Reproduction - selected-entry affine transition regularity

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The selected-entry all-pivot microcertificate already has finite chart maps,
source chart points, transition chart points, and chart-map equality on a
normalised target-coordinate overlap.  The A4 atlas boundary, however, still
stores transition regularity as an arbitrary supplied predicate.  Can we record
the concrete selected-entry affine overlap formulas as a nontrivial transition
regularity certificate?

## Source Anchor

Aoyagi's Case 1/Case 2 blow-up charts use a selected entry as the exceptional
coordinate and divide all other center entries by that selected entry.  On an
overlap where the target pivot's normalised source coordinate is nonzero, the
target selected entry is the old selected entry times that old normalised
target coordinate, and the new normalised residual coordinates are obtained by
division by that coordinate.  This is the elementary affine-chart transition
for the selected-entry blow-up used throughout Aoyagi's displayed Case 1/Case
2 chart substitutions.  The overlap hypothesis is the nonvanishing of the
normalised coordinate `d`, not the nonvanishing of the ambient center value
`u * d`; exceptional-divisor points with `u = 0` are still allowed.

## Generic Selected-Entry Transition

Let `center` be the finite set of center entries and let chart `p` be the chart
where the center entry `p` is selected.  Coordinates in chart `p` are

```text
x_p = u,
x_i = u * y_i        for i != p.
```

Equivalently, with Lean's total normalised map

```text
N_p(y)_p = 1,
N_p(y)_i = y_i       for i != p,
```

the chart map is

```text
x_i = u * N_p(y)_i.
```

Now fix another pivot `q`.  On the overlap where

```text
d = N_p(y)_q != 0,
```

the target chart coordinates are

```text
u_q = u * d,
z_i = N_p(y)_i / d.
```

Then the target chart map is

```text
u_q * N_q(z)_i = u * N_p(y)_i
```

for every center entry `i`.  Indeed:

- if `i=q`, then `N_q(z)_q=1`, so the left side is `u*d`;
- if `i!=q`, then `N_q(z)_i=z_i=N_p(y)_i/d`, so the left side is
  `(u*d)*(N_p(y)_i/d)=u*N_p(y)_i`.

Thus the two charts give the same finite center value on the overlap.

## Inverse

Starting from the target coordinates above, the normalised source coordinate in
the target chart is

```text
N_q(z)_p = 1/d.
```

Applying the reverse transition gives selected coordinate

```text
u_p' = (u*d) * (1/d) = u
```

and residual coordinates

```text
N_q(z)_i / N_q(z)_p
  = (N_p(y)_i/d) / (1/d)
  = N_p(y)_i.
```

For non-source-pivot residual entries this is exactly the original residual
coordinate; at the source pivot it is the total normalised value `1`, which is
erased from the source residual subtype.  Hence the reverse transition recovers
the original source chart point.

## Cocycle

Let `r` be a third pivot.  Suppose

```text
d_q = N_p(y)_q != 0,
d_r = N_p(y)_r != 0.
```

After first moving from `p` to `q`, the target denominator for moving from `q`
to `r` is

```text
N_q(z)_r = N_p(y)_r / d_q.
```

The selected coordinate after the two-step transition is

```text
(u*d_q) * (N_p(y)_r/d_q) = u*N_p(y)_r,
```

which is the selected coordinate of the direct `p -> r` transition.  The
normalised residuals also agree:

```text
(N_q(z)_i)/(N_q(z)_r)
  = (N_p(y)_i/d_q)/(N_p(y)_r/d_q)
  = N_p(y)_i/N_p(y)_r.
```

Thus the finite chart transition is route-independent on the normalised triple
overlap.

## Lean Shape

Add concrete predicates, not `True` placeholders:

```text
SelectedEntryFiniteAffineTransitionRegularFamily hcenter chartEquiv
SelectedEntryFiniteAffineTransitionRegularPair hcenter chartEquiv sourceChart targetChart
```

The family predicate has fields for:

1. the full transition-point formula, including residuals
   `N_source(i) / denom`;
2. target coordinate:
   `coord target (transition source target u residual) 0 = u * N_source(target)`;
3. chart-map equality on `N_source(target) != 0`;
4. inverse transition on the same nonzero overlap;
5. self-transition;
6. cocycle on normalised triple overlaps.

Then prove:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
  .finiteAffineTransitionRegular
```

for arbitrary selected-entry centers, and a Case 2 residual-block
specialisation:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteAffineTransitionRegular
```

Finally provide the displayed-target pair extraction theorem where
`targetChart = displayedChartIndex`:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteAffineTransitionRegular_displayedPair
```

## Why This Is Source-Moving

The predicate is tied to the actual selected-entry chart formulas and cannot be
inhabited from `SelectedEntryChartFamilyBoundary.exists_trivial` or from
`SourceProductionObligation`.  It proves concrete overlap algebra that can
instantiate a finite selected-entry `TransitionRegular` predicate when that
predicate is explicitly chosen to mean these algebraic overlap identities.

## Nonclaims

This is still finite affine overlap algebra.  It does not prove analytic
domains, analytic regular maps, open-neighbourhood coverage, unit regularity,
analytic Jacobian compatibility, source production of successor matrices,
branch termination, normal crossings, pole order, or RLCT extraction.

It also does not repair Aoyagi's printed Case 2 vector mismatch or construct a
full A4 transition invariant.
