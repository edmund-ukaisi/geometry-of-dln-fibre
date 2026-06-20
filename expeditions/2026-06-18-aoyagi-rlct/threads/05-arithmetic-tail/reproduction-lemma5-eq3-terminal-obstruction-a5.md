# Pen-and-paper reproduction - Lemma 5 equation (3) terminal obstruction

Status: checked finite obstruction.

This note records the boundary case `a=1` for Aoyagi Lemma 5 equation `(3)`.
It is an obstruction to reading equation `(3)` as a terminal-zero theorem.

## Source

Aoyagi PDF p. 27, equation `(3)`, has the special boundary assignment

```text
T(S_(ell-a+2)-1) = Htilde'_(ell-a+1)+1.
```

If `a=1`, then

```text
ell-a+1 = ell,
ell-a+2 = ell+1.
```

So the special boundary is the terminal selected endpoint:

```text
S_(ell+1)-1.
```

The displayed value is

```text
Htilde'_ell + 1.
```

Definition 3's selected-sum identity gives

```text
Htilde'_ell = 0.
```

Therefore a supplied equation `(3)` branch certificate gives

```text
T(S_(ell+1)-1) = 1
```

in the boundary case `a=1`.

## Lean Target

```text
aoyagiLemma5Eq3_terminalEndpoint_one_of_one
```

## Nonclaims

- This does not construct equation `(3)`'s displayed vector.
- This does not prove any terminal variable theorem.
- This does not prove `tilde t=0`; it records why that cannot follow from the
  printed equation `(3)` branch assignment when `a=1`.
- No chart-family, order-count, normal-crossing, or RLCT claim is made.
