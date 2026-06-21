# Pen-and-paper reproduction - Lemma 5 equation (4) terminal extension forces p

Status: checked finite source-selected obstruction.

This note records the general necessary condition behind the `p=1` terminal
extension obstruction.  It does not construct equation `(4)`'s piecewise
certificate or a terminal extension.

## Source Normalisation

In equation `(4)`, the terminal-collision case is

```text
p+1 = a.
```

Then the equation `(4)` special boundary is the terminal selected endpoint
`S_(ell+1)-1`, and the supplied terminal-collision branch value is

```text
M - W_(ell+1) - p + 1.
```

## Terminal Extension Consequence

A supplied terminal upper-chain extension gives

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

The selected-sum identity plus `a<=ell` gives

```text
Htilde'_ell = 0.
```

Together with the terminal-collision branch value, this forces

```text
W_(ell+1) = M - p + 1.
```

## Definition 3 Obstruction

Definition 3's selected-sum identity and strict selected-width inequalities
give the selected-width upper bound

```text
W_i <= M-1
```

for every selected width.  In particular,

```text
W_(ell+1) <= M-1.
```

Combining with the terminal-extension compatibility gives

```text
M - p + 1 <= W_(ell+1) <= M - 1.
```

Hence

```text
2 <= p.
```

Equivalently, under the same supplied-certificate and source-selected
hypotheses, if `p<2`, then the supplied terminal upper-chain extension is
impossible.

## `p=0` Caveat

The Lean theorem is stated for the totalized supplied-certificate API, which
allows any natural `p` satisfying the record fields.  Aoyagi's printed equation
`(4)` uses `Htilde_{j0}` with displayed chains indexed from `1`, so the
`p=0` edge should be read as a Lean-totalized supplied-certificate consequence,
not as an additional printed source case.

## Lean Targets

```text
aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected
aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two
```

## Nonclaims

- No supplied equation `(4)` branch certificate is constructed.
- No terminal extension is constructed.
- No terminal `tilde t=0` theorem is proved.
- This is not a proof or disproof of Aoyagi Lemma 5.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction is proved.
