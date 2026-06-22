# Reproduction - dimension and rank convention map

Date: 2026-06-22.

Status: A6 convention-map slice.  This is notation and finite arithmetic only.

## Source Anchor

Aoyagi's main setup on PDF p. 8 uses matrices

```text
A^(s) : H^(s) x H^(s+1),      s = 1,...,L.
```

The true product has rank `r`.  Definition 3 on PDF pp. 8-9 defines the
reduced layer widths

```text
M^(s) = H^(s) - r,             s = 1,...,L+1.
```

Theorem 3 and the reduced problem on PDF pp. 11-14 explain why these are the
dimensions of the reduced matrices after rank-`r` block reduction.  This Lean
slice does not formalise that deduction here; it records the rank-width bound
needed to read the integer expression as a natural width.

## Convention Map

Lean uses a source-indexed width function

```text
H : Nat -> Nat
```

with Aoyagi's source layers read at `H 1, ..., H (L+1)`.  The rank is

```text
r : Nat.
```

The explicit pointwise rank-width hypothesis is

```text
r <= H s.
```

For selected cutpoints, Lean index `j : Fin (ell+1)` represents source index
`j+1`, and the selected source layer is `C.cut j`.  The selected rank-width
hypothesis is therefore

```text
forall j : Fin (ell+1), r <= H (C.cut j).
```

The source layer range is finite, so the Lean API keeps hypotheses pointwise
or selected-pointwise rather than introducing a global `forall s : Nat`
assumption.  This slice does not prove the matrix-rank fact from a concrete
product.

The source also has an input/output wording hazard on PDF p. 8: the matrix
dimensions orient the product by the displayed sizes `H^(s) x H^(s+1)`.  This
convention map records the matrix/product orientation and does not try to
normalise the prose about input and output units.

## Pen-and-paper Check

Without the bound `r <= H^(s)`, Nat subtraction would truncate:

```text
H^(s) - r = 0     if r > H^(s)
```

whereas Aoyagi's displayed `M^(s)=H^(s)-r` is meant as the actual reduced
dimension.  Therefore the Lean definition keeps

```text
aoyagiReducedWidthInt H r s = (H s : Int) - (r : Int).
```

If `r <= H s`, then ordinary integer subtraction agrees with Nat subtraction
coerced to integers:

```text
(H s : Int) - (r : Int) = ((H s - r : Nat) : Int).
```

The same inequality also gives

```text
0 <= (H s : Int) - (r : Int).
```

For selected cutpoints `C`, the selected reduced widths are pointwise

```text
aoyagiSelectedReducedWidths H r C j
  = aoyagiReducedWidthInt H r (C.cut j).
```

Thus a pointwise selected hypothesis

```text
forall j, r <= H (C.cut j)
```

gives the Nat-subtraction form and nonnegativity of every selected reduced
width.

The Nat-indexed helper used by the Lemma 5 arithmetic is
`aoyagiSelectedWidthNat`.  On selected-range indices it agrees with the finite
family, and outside the selected range it is the zero extension.  Hence the
same selected rank-width hypothesis proves

```text
0 <= aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) i
```

for every Nat index `i`.

## Lean Translation

The Lean file is `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`.

It adds:

- `aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le`;
- `aoyagiReducedWidthInt_nonneg_of_rank_le`;
- `aoyagiSelectedReducedWidths_apply`;
- `aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le`;
- `aoyagiSelectedReducedWidths_nonneg_of_rank_le`;
- `aoyagiSelectedWidthNat_selectedReducedWidths_of_lt`;
- `aoyagiSelectedWidthNat_selectedReducedWidths_fin`;
- `aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le`.

## Kill Conditions

- Do not replace `aoyagiReducedWidthInt` by Nat subtraction unless the relevant
  `r <= H s` hypothesis is present.
- Do not replace the selected pointwise rank-width hypothesis by an untracked
  global width hypothesis.
- Do not use this convention map as a proof of the product reduction,
  normal-crossing certificate, pole order, or RLCT extraction.
