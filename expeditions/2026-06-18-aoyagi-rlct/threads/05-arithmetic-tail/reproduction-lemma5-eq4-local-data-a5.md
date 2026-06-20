# Pen-and-paper reproduction - Lemma 5 equation (4) local data

Status: checked conditional source arithmetic.

This note packages the local arithmetic already isolated for Aoyagi Lemma 5
equation `(4)`.  It does not construct the displayed source vector; it only
records the corrected guards under which the displayed formula has a legal
label and the right own-coordinate value.

## Source

Aoyagi PDF p. 27, equation `(4)`, has

```text
s = S_(j0+1)-1,
k = Htilde_j0 + 1,
j0 <= a.
```

Write `p=j0` and `c=ell-a`.  The displayed formula also contains the tail
cutoff

```text
S_(p+c+2).
```

Definition 3 supplies selected indices only through `S_(ell+1)`.

## Corrected Selected-Index Guard

The tail cutoff is selected exactly when

```text
p+c+2 <= ell+1.
```

Substituting `c=ell-a`, and assuming `a<=ell`, this is equivalent to

```text
p+1 <= a.
```

Thus the local-data package uses `p+1<=a`, not only the printed `p<=a`.

## Own Coordinate

The own-coordinate value in the displayed equation `(4)` branch is

```text
Htilde'_p - p.
```

The already-proved interval-excess calculation gives

```text
Htilde'_p - Htilde_p = p
```

when

```text
p <= a,
p <= ell-a.
```

Since `p+1<=a` implies `p<=a`, the corrected local package assumes
`p<=ell-a` and obtains

```text
Htilde'_p - p = Htilde_p.
```

Therefore at the own coordinate `s=S_(p+1)-1`, the displayed value matches
`k-1`.

## Label Legality

The previous Definition 3 label-bound slice proves

```text
1 <= Htilde_p+1 <= W_(p+1)
```

under `1<=p`, `p<=a`, and the selected-width hypotheses.  Again,
`p+1<=a` supplies `p<=a`.

Thus the corrected local package has a legal label

```text
k = Htilde_p+1.
```

## Lean Target

```text
aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
```

It packages:

```text
p + (ell-a) + 2 <= ell+1,
Htilde'_p - p = Htilde_p,
1 <= Htilde_p+1 <= W_(p+1).
```

## Nonclaims

- This does not construct the equation `(4)` displayed source vector.
- This does not prove terminal `tilde t=0`.
- This does not prove vector admissibility or the source vector-to-chain
  correspondence.
- This does not prove chart-family coverage, Lemma 5 order count, pole order,
  normal crossings, or RLCT extraction.
