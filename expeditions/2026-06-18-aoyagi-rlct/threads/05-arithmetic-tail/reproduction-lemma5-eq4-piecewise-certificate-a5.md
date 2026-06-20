# Pen-and-paper reproduction - Lemma 5 equation (4) piecewise certificate

Status: checked conditional source-vector-facing slice.

This note records the first source-layer vocabulary for Aoyagi Lemma 5
equation `(4)`: selected cutpoints and a supplied piecewise branch certificate.
It does not construct the displayed vector.  It says that if a function has the
displayed branch values on selected blocks, then its own-coordinate value and
label legality follow from the already-proved local arithmetic.

## Source

Aoyagi Definition 3 selects indices

```text
S_1 < ... < S_(ell+1)
```

and selected widths `M(S_i)`.  Lemma 5 equation `(4)` on PDF p. 27 gives a
piecewise formula for `t^(S)_{s,k}` with

```text
s = S_(p+1)-1,
k = Htilde_p+1,
c = ell-a.
```

The relevant selected blocks are

```text
B_b = { S | S_(b+1)-1 <= S < S_(b+2)-1 },
```

in zero-based notation.

## Supplied Cutpoints

The Lean structure `AoyagiSelectedCutpoints ell` supplies the selected
cutpoints as data:

```text
cut : Fin (ell+1) -> Nat,
cut i >= 1,
cut i < cut (i+1).
```

The accessor `point C i` is total; in range it is the source selected index
`S_(i+1)`.  The block predicate is

```text
block C b S  iff  b < ell and point C b - 1 <= S < point C (b+1) - 1.
```

The basic endpoint lemma proves

```text
block C b (point C b - 1)
```

for `b<ell`.

## Supplied Equation (4) Branch Certificate

The Lean structure `AoyagiLemma5Eq4PiecewiseSourceVector` records a function
`T : Nat -> Int` with the displayed branch values from equation `(4)`:

```text
S < S_2-1:
  T(S) = layerWidth(S+1),

1 <= b <= p and S in B_b:
  T(S) = Htilde'_b - b,

p < b <= p+c and S in B_b:
  T(S) = Htilde'_b - p,

S = S_(p+c+2)-1:
  T(S) = Htilde'_(p+c) - p + 1,

tail selected blocks after S_(p+c+2)-1:
  T(S) = Htilde'_b.
```

This is a certificate shape, not an existence theorem.

## Own Coordinate

At the own source layer,

```text
S = s = S_(p+1)-1 = point C p - 1.
```

Since `p<ell`, this lies in block `B_p`.  The prefix branch applies because
`1<=p` and `p<=p`, hence

```text
T(point C p - 1) = Htilde'_p - p.
```

The already-proved local equation `(4)` arithmetic, under `p+1<=a` and
`p<=ell-a`, gives

```text
Htilde'_p - p = Htilde_p.
```

Therefore

```text
T(point C p - 1) = Htilde_p = k-1.
```

## Label Legality

The same local arithmetic theorem gives

```text
1 <= Htilde_p+1 <= W_(p+1),
```

under Definition 3's selected-width hypotheses and `1<=p`, `p+1<=a`.

## Lean Targets

```text
AoyagiSelectedCutpoints
AoyagiSelectedCutpoints.point
AoyagiSelectedCutpoints.block
AoyagiSelectedCutpoints.leftEndpoint_mem_block
AoyagiLemma5Eq4PiecewiseSourceVector
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
```

## Nonclaims

- No construction or existence proof for the equation `(4)` displayed vector.
- No total source-layer coverage beyond the supplied branch certificate.
- No terminal `tilde t=0`.
- No vector admissibility or source vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 chart-family coverage/order count, pole order, normal crossings,
  or RLCT extraction.
