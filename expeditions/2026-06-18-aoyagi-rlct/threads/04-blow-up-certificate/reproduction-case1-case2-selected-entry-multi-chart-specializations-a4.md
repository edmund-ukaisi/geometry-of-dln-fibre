# Reproduction - A4 Case 1/Case 2 selected-entry multi-chart specializations

Date: 2026-06-23.

Status: reproduced, formalised, and xhigh-reviewed.

Review:
`review-case1-case2-selected-entry-multi-chart-specializations-a4.md`.

## Source Anchor

Aoyagi PDF pp. 16-17 gives the Case 1 center: one old exceptional
coordinate together with the row strip

```text
d_ij = 0,    J+1 <= i <= J+J1,    J+1 <= j <= M^(S+1).
```

Aoyagi PDF pp. 19-21 gives the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and displays the top-left selected-entry chart.  This slice does not use the
quiver paper.  It packages the elementary selected-entry calculation for all
finite pivots in those two centers; it does not assert that Aoyagi wrote
source-coordinate formulas for every pivot.

## Finite Calculation

Let `E` be a nonempty finite center and choose a pivot `p in E`.  The
selected-entry chart has coordinates

```text
x_p = u,
x_e = u y_e    for e in E \ {p}.
```

Then the center square-sum pulls back to

```text
sum_{e in E} x_e^2
  = u^2 + sum_{e != p} u^2 y_e^2
  = u^2 * (1 + sum_{e in E \ {p}} y_e^2).
```

In the finite normal-crossing certificate convention, the unique coordinate
therefore has loss exponent `1`.  The formal pivot-first Jacobian matrix has
the block form

```text
[ 1   0 ]
[ y   u I ],
```

so its formal determinant is `u^(|E|-1)`.  The unique active ratio in every
pivot chart is

```text
((|E|-1) + 1) / (2 * 1) = |E| / 2.
```

Since each chart has only this one coordinate, every pivot chart contributes
count `1` at the ratio `|E|/2`; the finite exponent minimum is `|E|/2`, and
the finite exponent order of the all-pivot chart family is `1`.

## Case 2 Specialization

For Case 2 set

```text
E = case2ResidualBlockPivotEntries n S J.
```

Under the displayed continuation hypotheses

```text
1 <= S,
J + 1 <= prefixMinNat n (S + 1),
```

the displayed pivot `(J+1,J+1)` witnesses `E.Nonempty`, so the all-pivot
finite certificate can be formed.  The existing cardinality lemma gives

```text
|E| = (prefixMinNat n S - J) * (n (S+1) - J).
```

Therefore the all-pivot finite Case 2 selected-entry family has finite
minimum

```text
((prefixMinNat n S - J) * (n (S+1) - J)) / 2
```

and finite order `1`.

## Case 1 Specialization

For Case 1 set

```text
E = case1CenterGenerators n S J J1.
```

The old exceptional generator witnesses `E.Nonempty` without further bounds.
The existing center cardinality lemma gives

```text
|E| = 1 + |case1StripEntries n S J J1|
    = 1 + J1 * (n (S+1) - J).
```

Therefore the all-pivot finite Case 1 selected-entry family has finite
minimum

```text
(1 + J1 * (n (S+1) - J)) / 2
```

and finite order `1`.

## Boundary

This is finite certificate bookkeeping only.

- no analytic chart coverage;
- no transition regularity;
- no source-coordinate formulas for arbitrary non-displayed pivots;
- no `Q/P` source production;
- no chart-produced recurrence or exponent post-data;
- no global A0 active-ratio lower bound or chart count theorem;
- no analytic Jacobian or volume-form theorem;
- no pole order or RLCT extraction.

## Kill Conditions

- If a downstream statement treats the all-pivot finite family as Aoyagi's
  analytic blow-up atlas, it overclaims this slice.
- If a downstream statement uses arbitrary-pivot Case 1 or Case 2 charts as
  source-produced transition formulas, it must supply separate source
  production and regularity proofs.
- If the finite count `1` in each pivot chart is promoted to a global pole
  order without proving the complete normal-crossing chart family and the
  lower-bound hypotheses, it crosses the cited extraction boundary.
