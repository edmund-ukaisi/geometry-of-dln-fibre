# A6 Definition 3 source-data ceiling reproduction

Date: 2026-06-23.

Source used: Aoyagi 2023 preprint, Definition 3 and Theorem 2 setup
(PDF/printed pp. 8-9).

## Question

The existing A6 formula layer treats `AoyagiDefinition3CeilData` as supplied:
it already contains the integer `M` of Definition 3, renamed `ceilWidth`, and
the residue `a`.  The source, however, defines these numbers after the selected
cutpoints and selected-width inequalities have been chosen.

This slice removes only the supplied ceiling/residue datum.  It does not
construct the selected cutpoints.

## Source Data

Definition 3 starts with reduced widths

```text
M^(s) = H^(s) - r,        s = 1,...,L+1.
```

It selects cutpoints `S_j`, `j=1,...,ell+1`, and forms the selected value set
`M = {M^(S_j)}`.  The source conditions are value-level: selected reduced
widths are smaller than widths whose value is not in `M`, and the selected
widths satisfy the strict selected inequality

```text
sum_k M^(S_k) > ell * M^(S_j)
```

for selected indices, plus the displayed nonselected inequality

```text
sum_k M^(S_k) <= (ell-1) * M^(s)
```

for widths whose value is not in the selected value set.  Lean packages these
as source data attached to an already supplied `AoyagiSelectedCutpoints ell`.
The cutpoints themselves remain supplied; the paper passage does not give an
existence algorithm here.

## Ceiling Calculation

Let

```text
T = sum_j m_j
e = ell.
```

Assume `0 < e`.  Euclidean division of the integer `T` by the positive integer
`e` gives

```text
T = (T % e) + e * (T / e),
0 <= T % e < e.
```

Definition 3 wants a residue `a` in the range

```text
0 < a <= ell
```

and an integer `ceilWidth` such that

```text
T = ell * (ceilWidth - 1) + a.
```

There are two cases.

If `T % e = 0`, set

```text
ceilWidth = T / e,
a = ell.
```

Then

```text
T = e * (T / e)
  = e * ((T / e) - 1) + e,
```

and `0 < a <= ell` follows from `0 < ell`.

If `T % e != 0`, set

```text
ceilWidth = T / e + 1,
a = (T % e).toNat.
```

Since `0 <= T % e < e` and the remainder is nonzero, we have

```text
0 < T % e <= e,
```

so `0 < a <= ell` after converting the nonnegative integer remainder to a
natural number.  Also

```text
T = (T % e) + e * (T / e)
  = e * ((T / e + 1) - 1) + a.
```

This is exactly the integral form already stored in
`AoyagiDefinition3CeilData`.

## Lean Target

Add to `Definition3Bridge.lean`:

- `AoyagiDefinition3CeilData.nonempty_of_ell_pos`, a generic Euclidean-division
  constructor for any integer selected-width family;
- `AoyagiDefinition3SourceData`, a source-shaped package for supplied
  Definition 3 cutpoints, value-level selected dominance, selected strict
  inequalities, and value-level nonselected inequalities;
- `AoyagiDefinition3SourceData.exists_ceilData`, which turns source data into
  an existential `AoyagiDefinition3CeilData` and carries forward the strict
  selected inequality.

## Nonclaims

- No construction or uniqueness of selected cutpoints.
- No proof that Aoyagi's displayed selected set exists for arbitrary widths.
- No proof that selected cutpoints are the only possible selected set.
- No use of nonselected inequalities in later arithmetic yet.
- No normal-crossing chart production.
- No pole order or RLCT extraction.
