# Pen-and-paper reproduction - Htilde interval bounds

Status: checked source-gap slice.  This is a finite same-coordinate
`H`-chain consequence of the displayed `Htilde`/`Htilde'` chains on Aoyagi
PDF pp. 24-26, plus the source-coordinate obstruction from PDF pp. 14 and
22-26.  It does not prove a source-defined map `T -> (H_j),(S_j)`, Lemma 4,
Lemma 5, pole order, normal crossings, or RLCT extraction.

## Source Gap

Aoyagi Definition 4 on PDF p. 14 defines only componentwise vector order:

```text
T <= T' iff t_1 <= t'_1, ..., t_L <= t'_L.
```

On PDF p. 22, Aoyagi says every vector `T_{s,k}` has corresponding sequences
`(H_j),(S_j)` with

```text
H_j in {t^(1)_{s,k}, ..., t^(L)_{s,k}},
S_j < S_(j+1),
H_j <= H_(j-1),
H_j <= M(S_(j+1)),
H_ell = 0.
```

This is existential bookkeeping, not a unique projection from a vector to
chain coordinates.  The nearest explicit coordinate relation appears in the
Lemma 5 discussion on PDF p. 26:

```text
t_{s,k}^{(S_(j+1)-1)} = H_j.
```

Thus the source step

```text
Ttilde <= T <= Ttilde' and Htilde_ell=Htilde'_ell=0 imply H_ell=0
```

is not derivable from Definition 4 alone.  It is valid only when the endpoint
or chain values are read from common coordinates.

## Chain-Level Replacement

Let `L_j` be the lower displayed chain `Htilde_j` and `U_j` be the upper
displayed chain `Htilde'_j`.  The previous chain arithmetic proves

```text
U_j - L_j = e_j
```

where

```text
e_j = min(j, ell-j, a, ell-a) >= 0.
```

Therefore

```text
L_j <= U_j
```

for every same chain coordinate `j`.

Define the finite offset interval

```text
O_j = {0,1,...,e_j}.
```

Then

```text
|O_j| = e_j + 1,
```

which is exactly Aoyagi's displayed interval size in Lemma 5.

Define the same-coordinate value set

```text
V_j = {L_j + r | r in O_j}.
```

Because `r` ranges over all integers from `0` to `e_j`,

```text
H_j in V_j
  iff L_j <= H_j <= L_j + e_j
  iff L_j <= H_j <= U_j.
```

The map `r |-> L_j+r` is injective, so

```text
|V_j| = |O_j| = e_j+1.
```

## Endpoint Consequence

At the terminal coordinate, the previous endpoint arithmetic gives

```text
L_ell = U_ell = 0
```

under Definition 3's selected-width sum

```text
sum_j M(S_j) = ell*(M-1)+a.
```

Thus a same-coordinate chain squeeze

```text
L <= H <= U
```

implies

```text
0 = L_ell <= H_ell <= U_ell = 0,
```

so

```text
H_ell = 0.
```

This is the honest replacement for the source sentence until a source-defined
vector-to-chain correspondence is available.

## Displayed Chain Counts

The previous increment calculation gives:

```text
F_j(L) in {M-1,M},
F_j(U) in {M-1,M}.
```

Together with terminal zero and the selected-width sum, the existing Lemma 4
finite count theorem applies to each displayed chain.  Therefore each
displayed chain has exactly `a` high increments and `ell-a` low increments.

This remains finite arithmetic.  It does not prove that an arbitrary
intermediate chain satisfying `L <= H <= U` has two-valued increments.  That
two-value property remains a separate hypothesis in the Lemma 4 wrappers.

## Same-Coordinate Vector API

If a coordinate map is supplied,

```text
coord : {0,...,ell} -> vector coordinates,
Tlo(coord j) = L_j,
T(coord j) = H_j,
Thi(coord j) = U_j,
```

then componentwise vector inequalities `Tlo <= T <= Thi` imply

```text
H_j in V_j
```

for every `j`.  This is not a theorem that Aoyagi's source construction
provides such a `coord`; the coordinate map is an explicit hypothesis.

## Deferred

- Source-defined unique `T -> (H_j),(S_j)` correspondence.
- Proof that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the same
  chain coordinates.
- Derivation of the two-value increment hypothesis for arbitrary intermediate
  chains or vectors.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Independent Checks

Xhigh source checker `Nietzsche the 5th` confirmed that Definition 4 supplies
only componentwise vector order and that the endpoint step is invalid without
a common coordinate.  Xhigh Lean/API scout `McClintock the 5th` recommended
the finite interval-offset/value-set API and warned not to derive binary
increments from chain bounds alone.
