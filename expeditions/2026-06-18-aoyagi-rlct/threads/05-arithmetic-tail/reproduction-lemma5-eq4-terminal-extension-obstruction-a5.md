# Pen-and-paper reproduction - Lemma 5 equation (4) terminal extension obstruction

Status: checked finite endpoint compatibility.

This note combines two already-isolated supplied-data facts for Aoyagi Lemma 5
equation `(4)`.  It does not construct the displayed vector or prove the
terminal convention.

## Source Normalisation

In the terminal-collision case

```text
p+1 = a,
```

the equation `(4)` special boundary

```text
S_(p+ell-a+2)-1
```

is the terminal selected endpoint `S_(ell+1)-1`.

The printed equation `(4)` singleton branch assigns this endpoint the value

```text
Htilde'_(ell-1) - p + 1.
```

Using Definition 3's selected-sum identity, the penultimate upper-chain value
is

```text
Htilde'_(ell-1) = M - W_(ell+1).
```

Therefore the supplied equation `(4)` boundary value is

```text
M - W_(ell+1) - p + 1.
```

## Terminal Extension Consequence

A separate supplied terminal extension would assign

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

Definition 3's selected-sum identity gives

```text
Htilde'_ell = 0.
```

Thus, if the supplied equation `(4)` branch certificate and this supplied
terminal extension are both imposed in the terminal-collision case, then

```text
M - W_(ell+1) - p + 1 = 0.
```

Equivalently,

```text
W_(ell+1) = M - p + 1.
```

If this last-width condition fails, then the supplied equation `(4)` branch
certificate cannot also satisfy the terminal extension to `Htilde'_ell`.

## Lean Targets

```text
aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary
aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary
```

## Nonclaims

- No construction or existence proof for equation `(4)`'s displayed vector.
- No proof that Aoyagi's terminal convention is supplied by the printed
  branch certificate.
- No terminal `tilde t=0` theorem without the supplied extension.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction.
