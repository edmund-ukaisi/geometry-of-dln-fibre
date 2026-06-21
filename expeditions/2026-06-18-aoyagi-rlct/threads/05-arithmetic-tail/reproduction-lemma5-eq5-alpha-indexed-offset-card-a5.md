# Reproduction - Lemma 5 Eq5 alpha-indexed offset cardinality

Status: reproduced; Lean checked; xhigh review passed.

This note packages a supplied alpha-domain coverage hypothesis as a finite
cardinality bridge.  It does not construct the branch family and does not
claim equality between Sigma-valued branch labels and integer offset values.

## Source

Aoyagi PDF p. 27, equation `(5)`, uses strict offsets `alpha` and branch labels

```text
k = Htilde'_p + 1 - alpha.
```

The strict Eq5 offset-value set in Lean records the corresponding source-vector
values

```text
Htilde'_p - alpha.
```

These are not the same type as branch labels: branch labels are source-label
pairs `(S,k)`, while offset values are integers.  The theorem below compares
only cardinalities, by counting both sides through the same supplied alpha
domain.

## Reproduction

Let `branches : Finset beta` be a supplied finite family with maps

```text
alphaOf : beta -> Nat
branchLabel : beta -> Sigma (fun _ : Nat => Nat).
```

Assume:

```text
branches.image alphaOf = aoyagiLemma5Eq5AlphaDomain ell a p,
Set.InjOn alphaOf branches,
(branchLabel b).snd = Htilde'_p + 1 - alphaOf b
```

for every supplied branch `b`.

The supplied alpha injectivity gives

```text
(branches.image alphaOf).card = branches.card.
```

The displayed label formula plus the previous branch-label injectivity theorem
gives

```text
(branches.image branchLabel).card = branches.card.
```

The alpha-image hypothesis rewrites `branches.image alphaOf` to the strict
alpha domain.  Finally, the map

```text
alpha |-> Htilde'_p - alpha
```

is injective, and its image on the strict alpha domain is exactly
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  Hence the offset-value set has
the same cardinality as the strict alpha domain.  Chaining these equalities
gives

```text
(branches.image branchLabel).card =
  (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card.
```

## Lean target

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card
```

## Nonclaims

- No construction of `branches`, `alphaOf`, or `branchLabel`.
- No source-label legality or width compatibility.
- No equality or explicit bijection between Sigma-valued branch labels and
  integer offset values.
- No coverage of actual-width labels, terminal-minimum labels, or Aoyagi's
  full displayed family.
- No pole order, normal crossings, or RLCT extraction.
