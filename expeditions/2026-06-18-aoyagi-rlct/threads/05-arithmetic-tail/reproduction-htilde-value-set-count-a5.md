# Pen-and-paper reproduction - Htilde value-set count

This note isolates a small finite-count wrapper around the `Htilde` interval
value sets already formalised from Aoyagi's Lemma 4/Lemma 5 discussion.  It
does not prove Lemma 5's chart-family construction, vector admissibility,
coverage, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi PDF pp. 25-27:

- the displayed lower and upper chains `Htilde_j` and `Htilde'_j`;
- Lemma 5 counts the interval sizes between these two chains at
  `j=1,...,ell-1`;
- the arithmetic target is

```text
1 + sum_{j=1}^{ell-1} (|I_j| - 1) = a(ell-a)+1,
```

where `I_j = {H : Htilde_j <= H <= Htilde'_j}`.

The source then uses additional displayed vector constructions to claim the
pole-order count.  This note only covers the displayed interval value-set
count.

## Reproduction

Fix `ell`, `a`, `M`, and selected widths `m`, with the source bounds
`1 <= ell` and `a <= ell`.

Let

```text
L_j = Htilde_j,
U_j = Htilde'_j.
```

The existing `Htilde` arithmetic proves

```text
U_j - L_j = e_j,
e_j = min(j, ell-j, a, ell-a).
```

For each coordinate `j`, define

```text
I_j = { L_j + r : r = 0,...,e_j }.
```

The map `r |-> L_j + r` is injective because integer addition by the fixed
integer `L_j` is injective.  Therefore

```text
|I_j| = e_j + 1.
```

Thus for interior coordinates `1 <= j <= ell-1`,

```text
|I_j| - 1 = e_j.
```

The previously reproduced Lemma 5 interval-excess arithmetic gives

```text
sum_{j=1}^{ell-1} e_j = a(ell-a).
```

Combining these equalities yields the finite value-set count

```text
1 + sum_{j=1}^{ell-1} (|I_j| - 1) = a(ell-a)+1.
```

The leading `1` is the common baseline contribution in Aoyagi's displayed
count.  This reproduction does not identify this baseline with a unique source
chart, nor does it prove that every counted interval value is realised by an
admissible exponent vector.

## Lean target

Add a Nat-indexed wrapper for the existing finite value sets:

```text
aoyagiHtildeIntervalValueSetNat ell a M m j
```

which is the finite value set at coordinate `j` when `j < ell+1`, and `empty`
otherwise.

Then prove:

```text
aoyagiHtildeIntervalValueSetNat_card_of_lt
aoyagiHtildeIntervalValueSetNat_card
aoyagiHtildeIntervalValueSetNat_excess_sum_Icc
```

The first cardinality theorem must assume `j < ell+1`.  The unconditional
cardinality theorem should return `0` outside the source coordinate range.

The second theorem should state:

```text
1 + sum_{j in Icc 1 (ell-1)}
      (card(aoyagiHtildeIntervalValueSetNat ell a M m j) - 1)
  = a*(ell-a)+1.
```

## Kill conditions

- Do not call this theorem Aoyagi Lemma 5.
- Do not claim chart-family admissibility, coverage, or exact pole order.
- Do not use the quiver paper or quiver Lean.
- Keep the proof purely finite arithmetic.
