# Pen-and-paper reproduction - Lemma 5 equation (3) local data and label bridge

Status: checked conditional arithmetic and source-label bridge.

This note records the source-facing arithmetic around Aoyagi Lemma 5 equation
`(3)`. It does not prove that equation `(3)` constructs a displayed source
vector, a terminal variable, a chart-family member, or a pole-order witness.

## Source

Aoyagi PDF p. 27, equation `(3)`, has the exceptional pair

```text
s = S_2-1,
k = Htilde'_1+1.
```

The special cutoff in the displayed vector is

```text
S_(ell-a+2).
```

Write zero-based selected widths as

```text
W_1 = M(S_1),
W_2 = M(S_2).
```

In Lean these are

```text
aoyagiSelectedWidthNat ell m 0,
aoyagiSelectedWidthNat ell m 1.
```

## Selected Index and Own Coordinate

The selected cutoff is defined from the selected list
`S_1,...,S_(ell+1)` exactly when

```text
ell-a+2 <= ell+1.
```

Under `a<=ell`, this is equivalent to `1<=a`.

For the own coordinate, equation `(3)` must put `S=S_2-1` into the upper-chain
branch with value `Htilde'_1`. This requires the interior guard `a<ell`; then

```text
Htilde'_1 - Htilde_1 = 1,
```

so the label `k=Htilde'_1+1` is one above the lower endpoint.

## Label Bounds

When `a<ell`,

```text
Htilde'_1 = W_1 + W_2 - (M-1),
k = Htilde'_1+1 = W_1+W_2-M+2.
```

Thus

```text
1 <= k <= W_2
```

is equivalent to

```text
M-1 <= W_1+W_2,
W_1+2 <= M.
```

Definition 3's selected-width inequalities and selected-sum identity prove the
first inequality. The second inequality is an extra one-unit slack condition.
It must not be inferred from Definition 3 alone.

## Counterexample to Definition 3 Label Legality

Take

```text
ell = 3,
a = 2,
M = 3,
W_1 = W_2 = W_3 = W_4 = 2.
```

Then the selected sum is `8 = 3*(3-1)+2`, and the strict selected-width
inequality holds because `8 > 3*2` for every selected width. The guards
`1<=a` and `a<ell` both hold.

But

```text
Htilde'_1 = W_1+W_2-(M-1) = 2,
k = Htilde'_1+1 = 3,
W_2 = 2.
```

So `k<=W_2` fails. This is why the Lean source-shaped theorem keeps
`W_1+2<=M` as an explicit hypothesis.

## Actual Source Label

The selected-width label bounds become the blow-up bookkeeping predicate

```text
actualWidthLabel L n (S_2-1) k
```

only after the following additional compatibility data are supplied:

```text
S_2-1 <= L,
n(S_2) = W_2,
(k : Int) = Htilde'_1+1.
```

The lower source-layer bound `1<=S_2-1` follows from `S_1>=1` and the strict
cutpoint inequality `S_1<S_2`.

## Lean Targets

```text
aoyagiLemma5Eq3_localData_of_widthGuards
aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack
```

## Nonclaims

- No construction or existence proof for equation `(3)`'s displayed vector.
- No proof that Definition 3 alone gives `Htilde'_1+1<=M(S_2)`.
- No introduced-label theorem.
- No terminal `tilde t=0` theorem.
- No vector admissibility, chart-family coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction.
