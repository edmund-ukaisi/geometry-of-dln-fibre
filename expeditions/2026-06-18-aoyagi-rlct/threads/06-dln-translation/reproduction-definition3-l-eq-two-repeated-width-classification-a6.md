# Reproduction - Definition 3 `L=2` repeated-width classification

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The landed `L=2` pairwise-distinct theorem classifies Definition 3 source-data
existence under pairwise distinct source-range reduced widths.  It leaves open
the repeated-width branch.  For `L=2`, can we classify all source-data
existence in terms of the three reduced-width values?

## Source Anchors

Aoyagi Definition 3, PDF pp. 8-9, supplies selected source indices and imposes
the selected strict inequality

```text
ell * M^(S_j) < sum_k M^(S_k)
```

for selected indices.  It also imposes conditions only on source-range widths
whose **value** is not in the selected value set.  Lean formalises this
value-level condition as membership in the image

```text
{ aoyagiReducedWidthInt H r (C.cut j) | j : Fin (ell+1) }.
```

Thus an unselected source position whose reduced-width value equals a selected
value is not nonselected for the purpose of Definition 3.

## Setup

For `L=2`, write

```text
w1 = M^(1),  w2 = M^(2),  w3 = M^(3).
```

Any Definition 3 source-data witness has `0 < ell` and `ell+1` strictly
increasing cutpoints in the source range `{1,2,3}`.  Hence

```text
ell = 1 or ell = 2.
```

The case `ell=2` selects all three source layers.  The case `ell=1` selects
two source layers.

## The `ell=2` Branch

If `ell=2`, the three cutpoints must be exactly `1,2,3`.  The nonselected
conditions are vacuous because every source-range value is selected.  The
Definition 3 selected strict inequalities are exactly

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

Call this the triangle branch.

Conversely, if the three triangle inequalities hold, selecting all source
layers with consecutive cutpoints gives Definition 3 source data by the
all-source selected constructor.

## The `ell=1` Branch

Suppose `ell=1` and the selected cutpoints carry values `a` and `b`.  The
selected strict inequalities are

```text
a < a+b,
b < a+b.
```

Therefore

```text
a > 0,  b > 0.
```

Now let `c` be the value of any source-range width whose value is not in the
selected value set `{a,b}`.  Definition 3's nonselected upper inequality has
coefficient `ell-1 = 0`, so it gives

```text
a+b <= 0*c = 0.
```

This contradicts `a>0` and `b>0`.  Hence, for `ell=1`, every source-range
reduced-width value must lie in `{a,b}`.  Because the two selected values are
positive, all three source-range reduced widths are positive.  Because three
values are covered by at most two selected values, at least two of
`w1,w2,w3` are equal.

Conversely, assume

```text
0 < w1, 0 < w2, 0 < w3
```

and at least two of the three values are equal.  Then the set of the three
values has cardinality at most two.  Choose two source positions whose values
cover all distinct values:

- if all three values are equal, choose cutpoints `1,2`;
- if `w1=w2`, choose cutpoints `1,3`;
- if `w1=w3`, choose cutpoints `1,2`;
- if `w2=w3`, choose cutpoints `1,2`.

The two selected values are positive, so the selected strict inequalities for
`ell=1` hold:

```text
a < a+b    because b>0,
b < a+b    because a>0.
```

Every source-range value belongs to the selected value set by construction, so
the nonselected clauses are vacuous.  This gives Definition 3 source data with
`ell=1`.

## Classification

For `L=2`, Definition 3 source data exists if and only if either:

1. all three reduced widths are positive and at least two are equal; or
2. the three triangle inequalities hold:

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

The first branch is realised with `ell=1`.  The second branch is realised with
`ell=2`.

## Lean Shape

First strengthen the existing `ell=1` necessary-condition lemma by removing
the rank-width hypothesis:

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one
```

For `ell=1`, selected strict inequalities alone make the selected sum
positive.  A genuine nonselected value would force the same sum to be
nonpositive.

Then add an `ell=1` constructor for positive repeated profiles, followed by
the full classification theorem:

```text
AoyagiDefinition3SourceData.exists_ell_one_of_L_eq_two_positive_repeated

AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
```

The final theorem should state the repeated-positive branch and triangle
branch directly in terms of

```text
aoyagiReducedWidthInt H r 1,
aoyagiReducedWidthInt H r 2,
aoyagiReducedWidthInt H r 3.
```

No source-range rank-width hypothesis is needed for this finite Definition 3
classification, because the `ell=1` proof of positivity comes from the
selected strict inequalities, not from rank nonnegativity.

## Nonclaims

- No classification for `L>2`.
- No proof that Aoyagi's source data is produced by concrete matrix data.
- No ceiling-data package, Eq5 payload, Lemma 5 exactness, chart production,
  normal crossings, pole order, or RLCT extraction.
