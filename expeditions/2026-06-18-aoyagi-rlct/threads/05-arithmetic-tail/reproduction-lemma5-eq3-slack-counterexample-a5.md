# Pen-and-paper reproduction - Lemma 5 equation (3) slack counterexample

Status: checked finite Definition 3-shaped counterexample.

This note records a concrete selected-width tuple showing that Definition 3's
selected-width hypotheses do not force equation `(3)`'s extra one-unit slack
`W_1+2<=M`, and therefore do not force the selected-label upper bound for
`k=Htilde'_1+1`.

## Data

Take

```text
ell = 3,
a = 2,
M = 3,
W_1 = W_2 = W_3 = W_4 = 2.
```

In Lean's zero-based selected-width notation this is `m i = 2` for
`i : Fin (ell+1)`.

## Definition 3-shaped Checks

The range and equation `(3)` interior guards hold:

```text
1 <= ell,
a <= ell,
1 <= a,
a < ell,
ell-a+2 <= ell+1.
```

The selected widths are positive.  Their sum is

```text
sum_i W_i = 2+2+2+2 = 8.
```

Definition 3's selected-sum right side is

```text
ell*(M-1)+a = 3*(3-1)+2 = 8.
```

The strict selected-width inequalities hold for every selected width:

```text
ell*W_i = 3*2 = 6 < 8 = sum_i W_i.
```

Definition 3 also gives the lower width guard used in the equation `(3)` label
calculation:

```text
M-1 = 2 <= W_1+W_2 = 4.
```

## Failed Slack and Label Bound

The extra one-unit slack is

```text
W_1+2 <= M.
```

In this example,

```text
W_1+2 = 4,
M = 3,
```

so the slack fails.

The displayed equation `(3)` label is

```text
k = Htilde'_1+1.
```

Here

```text
Htilde'_1+1 = 3,
W_2 = 2,
```

so the selected-label upper bound `k<=W_2` also fails.

## Lean Target

```text
aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example
```

## Nonclaims

- No supplied equation `(3)` branch certificate is constructed.
- No actual source-width compatibility is asserted.
- No displayed vector, introduced-label status, terminal `tilde t=0`, chart
  sequence, Lemma 5 order count, pole order, normal crossings, or RLCT
  extraction is proved.
