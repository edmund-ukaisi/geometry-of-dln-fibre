# Pen-and-paper reproduction - Lemma 5 equation (4) terminal compatibility counterexample

Status: checked finite Definition 3-shaped counterexample.

This note records a concrete selected-width tuple showing that Definition 3's
selected-width hypotheses do not force equation `(4)`'s terminal-collision
last-width compatibility.

## Data

Take

```text
ell = 3,
a = 2,
p = 1,
M = 3,
W_1 = W_2 = W_3 = W_4 = 2.
```

In Lean's zero-based selected-width notation this is `m i = 2` for
`i : Fin (ell+1)`.

## Definition 3-shaped Checks

The range and terminal-collision guards hold:

```text
1 <= ell,
a <= ell,
1 <= p,
p <= ell-a,
p+1 = a.
```

The equation `(4)` source cutoff is also in range and terminal:

```text
p+(ell-a)+2 = 4 = ell+1,
p+(ell-a)+1 = 3 = ell.
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

## Failed Terminal Compatibility

The equation `(4)` terminal-extension compatibility from the terminal-collision
obstruction is

```text
W_(ell+1) = M-p+1.
```

In this example,

```text
W_(ell+1) = W_4 = 2,
M-p+1 = 3-1+1 = 3.
```

So the compatibility fails even though the selected-sum and strict
selected-width inequalities hold.

## Lean Target

```text
aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example
```

## Nonclaims

- No supplied equation `(4)` branch certificate is constructed.
- No terminal extension is constructed.
- No displayed vector, terminal `tilde t=0`, chart sequence, Lemma 5 order
  count, pole order, normal crossings, or RLCT extraction is proved.
