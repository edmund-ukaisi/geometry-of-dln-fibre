# Pen-and-paper reproduction - Lemma 5 equation (4) p=1 terminal extension obstruction

Status: checked finite source-selected obstruction.

This note records a uniform `p=1` consequence of the terminal-collision
obstruction.  It does not construct equation `(4)`'s piecewise certificate or
a terminal extension.

## Source Normalisation

In equation `(4)`, the terminal-collision case is

```text
p+1 = a.
```

If `p=1`, then `a=2`.  The equation `(4)` boundary index becomes

```text
p+(ell-a)+1 = 1+(ell-2)+1 = ell,
```

so the special boundary is the terminal selected endpoint `S_(ell+1)-1`.

The supplied terminal-collision branch value is

```text
M - W_(ell+1) - p + 1.
```

With `p=1`, this is

```text
M - W_(ell+1).
```

## Terminal Extension Consequence

A supplied terminal upper-chain extension gives

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

The selected-sum identity gives

```text
Htilde'_ell = 0.
```

Together with the terminal-collision branch value, this forces

```text
W_(ell+1) = M.
```

Equivalently, this is the general compatibility condition
`W_(ell+1)=M-p+1` specialized to `p=1`.

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

This contradicts the terminal-extension compatibility `W_(ell+1)=M`.

Therefore, in the `p=1` terminal-collision equation `(4)` case, a supplied
piecewise certificate satisfying Definition 3's selected-width hypotheses
cannot also satisfy the supplied terminal upper-chain extension.

## Lean Target

```text
aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality
```

## Nonclaims

- No supplied equation `(4)` branch certificate is constructed.
- No terminal extension is constructed.
- No terminal `tilde t=0` theorem is proved.
- This is not a proof or disproof of Aoyagi Lemma 5.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction is proved.
