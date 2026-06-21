# Pen-and-paper reproduction - Lemma 5 equation (4) no terminal upper extension example

Status: checked finite supplied-data incompatibility.

This note combines the terminal-collision obstruction with the closed
Definition 3-shaped counterexample.  It does not construct equation `(4)`'s
piecewise certificate or a terminal extension.

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

The selected-width sum is

```text
sum_i W_i = 2+2+2+2 = 8.
```

The right side of the selected-sum identity is

```text
ell*(M-1)+a = 3*(3-1)+2 = 8.
```

For each selected width,

```text
ell*W_i = 3*2 = 6 < 8 = sum_i W_i.
```

The equation `(4)` terminal-collision guards also hold:

```text
p+1 = 2 = a,
p+(ell-a)+1 = 1+(3-2)+1 = 3 = ell,
p+(ell-a)+2 = 4 = ell+1.
```

Thus the special boundary is the terminal selected endpoint
`S_(ell+1)-1`, written in Lean as `C.point 3 - 1`.

## Endpoint Values

The equation `(4)` singleton branch assigns the terminal endpoint

```text
Htilde'_(ell-1) - p + 1.
```

Here this is `Htilde'_2 - 1 + 1 = Htilde'_2`.  Directly from the displayed
upper chain,

```text
Htilde'_2 = (W_1+W_2+W_3) - (ell-a)(M-1) - (2-(ell-a))M
          = 6 - 2 - 3
          = 1.
```

The terminal upper-chain endpoint is

```text
Htilde'_3 = (W_1+W_2+W_3+W_4) - (ell-a)(M-1) - (3-(ell-a))M
          = 8 - 2 - 6
          = 0.
```

Equivalently, the terminal-extension compatibility condition from the
terminal-collision obstruction would be

```text
W_(ell+1) = M-p+1.
```

But in this tuple

```text
W_4 = 2,
M-p+1 = 3-1+1 = 3.
```

So any supplied equation `(4)` piecewise certificate for this tuple is
incompatible with the supplied terminal upper-chain extension

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

## Lean Target

```text
aoyagiLemma5Eq4_terminalEndpoint_values_ell3_a2_p1_allWidthsTwo
aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo
```

## Nonclaims

- No supplied equation `(4)` branch certificate is constructed.
- No terminal extension is constructed.
- No terminal `tilde t=0` theorem is proved.
- The terminal endpoint is outside the half-open selected block coverage.
- This is not a proof or disproof of Aoyagi Lemma 5.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction is proved.
- No compatibility between `layerWidth` and the selected widths is asserted.
