# Pen-and-paper reproduction - Lemma 5 equation (4) terminal collision

Status: checked finite endpoint arithmetic.

This note records what happens when Aoyagi Lemma 5 equation `(4)`'s special
boundary reaches the terminal selected endpoint.  It is an obstruction note,
not a terminal-variable construction.

## Source

Aoyagi PDF p. 27, equation `(4)`, has special boundary

```text
S_(p+ell-a+2)-1
```

with value

```text
Htilde'_(p+ell-a) - p + 1.
```

In Lean's zero-based notation this is

```text
C.point (p + (ell-a) + 1) - 1
```

with value

```text
aoyagiHtildeUpperNat ell a M m (p + (ell-a)) - p + 1.
```

## Terminal Collision

The special boundary is the terminal selected endpoint exactly when

```text
p + (ell-a) + 1 = ell,
```

equivalently

```text
p + 1 = a.
```

This is the equality case of the repaired selected-index guard `p+1<=a`.
The supplied equation `(4)` certificate now carries both `a<=ell` and
`p+1<=a`, so the boundary index is source-valid before this terminal
specialisation is applied.

Under this equality,

```text
p + (ell-a) = ell-1,
```

so the displayed terminal-collision value is

```text
Htilde'_(ell-1) - p + 1.
```

## Penultimate Upper Chain

Definition 3's selected-sum identity gives

```text
sum_i W_i = ell*(M-1)+a.
```

For the upper displayed chain,

```text
Htilde'_(ell-1) = sum_{i=1}^{ell} W_i
                 - ((ell-1)*(M-1) + (a-1)).
```

Since `sum_{i=1}^{ell} W_i = sum_i W_i - W_(ell+1)`, this becomes

```text
Htilde'_(ell-1)
  = ell*(M-1)+a - W_(ell+1) - (ell-1)*(M-1) - (a-1)
  = M - W_(ell+1).
```

Thus the displayed terminal-collision value is

```text
M - W_(ell+1) - p + 1.
```

Using `p+1=a`, this is also

```text
M - W_(ell+1) - a + 2.
```

## Zero Condition and Counterexample

The value is zero exactly when

```text
W_(ell+1) = M - p + 1.
```

Definition 3 does not force this condition.

For example, take

```text
ell = 3,
a = 2,
p = 1,
M = 3,
W_1 = W_2 = W_3 = W_4 = 2.
```

Then

```text
sum_i W_i = 8 = 3*(3-1)+2,
3*W_i = 6 < 8
```

for every selected width, so the selected-sum and strict selected-width
inequalities hold.  The boundary is terminal because `p+1=a`.  But the
displayed boundary value is

```text
M - W_4 - p + 1 = 3 - 2 - 1 + 1 = 1.
```

So equation `(4)`'s printed terminal-collision branch is not terminal-zero
from Definition 3 alone.

## Lean Targets

```text
aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum
aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary
aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary
```

## Nonclaims

- No construction or existence proof for equation `(4)`'s displayed vector.
- No proof of terminal `tilde t=0`.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction.
