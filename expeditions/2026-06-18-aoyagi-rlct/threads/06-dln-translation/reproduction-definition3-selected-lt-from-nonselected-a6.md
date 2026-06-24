# Reproduction - Definition 3 selected/nonselected redundancy

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

Independent scout:
Mendel the 2nd, xhigh read-only scout.

## Question

Full selected-cutpoint existence is not currently source-supported: Aoyagi
Definition 3 is treated as a choice of selected cutpoints satisfying displayed
conditions, not as an algorithm proving such cutpoints exist from arbitrary
layer widths.

There is, however, a small elementary redundancy inside the current
`AoyagiDefinition3SourceData` package.  The field

```text
selected_lt_nonselected
```

should follow from:

- the strict selected inequality;
- the nonselected upper inequality;
- nonnegativity of selected reduced widths, supplied through the rank-width
  hypothesis.

This removes one separately supplied field from a constructor for Definition 3
source data.  It does not construct cutpoints or prove that Definition 3 is
inhabited.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, separates selected widths from nonselected
widths.  The Lean source-data structure records both the strict selected
condition and the nonselected upper condition:

```text
ell * M^(S_i) < sum_j M^(S_j)
sum_j M^(S_j) <= (ell - 1) * M^(s)
```

for `M^(s)` outside the selected value set.  Since the reduced widths in the
paper are nonnegative in the source range `r <= H^(s)`, these two inequalities
force each selected width to be strictly smaller than the nonselected width.

## Pen-and-paper Calculation

Let

```text
e = ell,       x = M^(S_i),       y = M^(s),
T = sum_j M^(S_j).
```

Assume

```text
0 < e,
0 <= x,
e*x < T,
T <= (e-1)*y.
```

Then

```text
e*x < (e-1)*y.
```

If `y <= x`, then because `e-1 >= 0`,

```text
(e-1)*y <= (e-1)*x.
```

Thus

```text
e*x < (e-1)*x.
```

But `e*x = (e-1)*x + x`, so this implies `x < 0`, contradicting `0 <= x`.
Therefore `x < y`.

In Lean, `x` is

```text
aoyagiReducedWidthInt H r (C.cut i)
```

and the nonnegativity `0 <= x` is derived from the rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s
```

at the selected cutpoint, using `C.pos i` and `cut_le i`.

## Lean Shape

Add to `Definition3Bridge.lean`:

```text
aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe
```

with integer variables `selected`, `width`, and `total`.

Then add a constructor:

```text
AoyagiDefinition3SourceData.of_selectedStrict_nonselectedLe_rankWidth
```

Inputs:

```text
hell : 0 < ell
hcut_le : forall j, C.cut j <= L+1
hr : forall s, 1 <= s -> s <= L+1 -> r <= H s
hselected_strict : strict selected inequalities
hnonselected_le : nonselected upper inequalities
```

Output:

```text
AoyagiDefinition3SourceData L ell H r C.
```

The constructor fills `selected_lt_nonselected` using the arithmetic theorem.

## Nonclaims

This does not construct selected cutpoints.

It does not prove `exists C, AoyagiDefinition3SourceData L ell H r C`.

It does not prove rank-width hypotheses from matrices; those remain supplied
here and are handled separately by the source-rank bridge.

It does not prove Lemma 5 displayed-family realisation, Eq5 branch
construction, active-ratio/chart-count facts, chart production, normal
crossings, pole order, or RLCT.
