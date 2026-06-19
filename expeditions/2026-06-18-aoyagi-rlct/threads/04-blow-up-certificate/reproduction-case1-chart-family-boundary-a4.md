# A4 Case 1 Chart-Family Boundary

Status: reproduced a named assumption boundary for the Case 1 finite center.

## Source Data

In Case 1, after an old exceptional variable has been chosen, Aoyagi's center
has two kinds of generators:

```text
u_(s,k) = 0,
d_ij = 0,    J+1 <= i <= J+J1,    J+1 <= j <= n_(S+1).
```

The current Lean encoding is

```text
Case1CenterGenerator = Unit + (Nat x Nat),
case1CenterGenerators =
  {old exceptional generator} union {row-strip entries}.
```

The `Unit` branch represents the already chosen old exceptional generator. It
does not itself remember the source label `(s,k)`, its introduced-label
validity, level `J+J1`, minimality, or comparability data. Those remain in
the `Case1FirstJumpHypotheses` and later invariant packages.

Aoyagi displays two selected charts in Case 1:

- the old-exceptional-variable chart, corresponding to the `Unit` branch;
- the top-left row-strip pivot chart `d_(J+1,J+1) = u`, corresponding to
  `Sum.inr (J+1,J+1)`.

Arbitrary row-strip selected-entry charts are finite-center candidates. The
source text does not spell out chart coverage, regularity, or source-order
transition formulas for each non-displayed row-strip pivot.

## Elementary Finite Facts

The finite Case 1 center is always nonempty, witnessed by the old exceptional
generator. Under `1 <= J1` and `J+1 <= n_(S+1)`, the row-strip part is also
nonempty, witnessed by `(J+1,J+1)`.

For a right-branch generator, membership in the Case 1 center is exactly
membership of the underlying pair in the row-strip entry set.

These are finite-set statements. They do not establish the source validity of
the hidden old label, row-strip containment in the residual block, chart
coverage, or transition formulas.

## Boundary

The boundary records supplied predicates

```text
ChartRegular(g)
TransitionRegular(g,h)
```

for generators `g,h` in `case1CenterGenerators n S J J1`. A boundary package
says:

```text
if g is in the center, then ChartRegular(g);
if g and h are in the center, then TransitionRegular(g,h).
```

It deliberately does not define these predicates. Later source-order chart
work must instantiate them with an explicit chart model.

## Scope

This checkpoint proves:

- finite nonemptiness of the Case 1 center;
- finite nonemptiness of the Case 1 row strip under displayed entry bounds;
- right-branch center membership iff row-strip membership;
- a Case 1 specialization of the generic selected-entry chart-family boundary;
- convenience projections for all center members, the old exceptional chart,
  and the displayed top-left row-strip pivot.

It does not prove:

- chart regularity;
- transition regularity;
- affine blow-up atlas construction or chart coverage;
- source validity of the hidden old label represented by `Unit`;
- source-order transition formulas for non-displayed row-strip pivots;
- chart-produced recurrence or exponent post-data;
- polynomial-coordinate Jacobians or analytic germ invariance;
- source comparability, normal crossings, or RLCT extraction.
