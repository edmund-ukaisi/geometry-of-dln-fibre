# Reproduction - Lemma 5 Eq5 alpha-indexed branch-label image

Status: reproduced; Lean checked; xhigh review pending.

This note packages the previous Eq5 alpha-indexed source-label slice at the
finite-image level.  It does not construct the branch family or prove any
coverage theorem.

## Source

Aoyagi PDF p. 27, equation `(5)`, assigns a strict-offset branch label

```text
k = Htilde'_p + 1 - alpha.
```

The previous checkpoint proved branchwise label legality under explicit
source-range and actual-width hypotheses, and branch-label injectivity under
supplied alpha injectivity.

## Reproduction

Let `branches : Finset beta` be a supplied finite family of Eq5 branch
records, with supplied maps

```text
alphaOf : beta -> Nat
branchLabel : beta -> Sigma (fun _ : Nat => Nat).
```

For every `b in branches`, assume:

```text
alphaOf b in aoyagiLemma5Eq5AlphaDomain ell a p,
1 <= (branchLabel b).fst <= L,
W_p <= n((branchLabel b).fst + 1),
(branchLabel b).snd = Htilde'_p + 1 - alphaOf b.
```

The branchwise source-label theorem gives

```text
branchLabel b in actualWidthLabelFinset L n
```

for each supplied branch.  Therefore every element of the finite image

```text
branches.image branchLabel
```

is in `actualWidthLabelFinset L n`.  This proves only a subset relation for
the supplied image.

If `alphaOf` is injective on `branches`, then the earlier injectivity theorem
gives `branchLabel` injective on `branches`.  The finite image cardinality is
therefore

```text
(branches.image branchLabel).card = branches.card.
```

This cardinality is a count of supplied branch labels, not a count of all Eq5
labels, all actual-width labels, or terminal-minimum labels.

## Lean targets

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj
```

## Nonclaims

- No construction of Eq5 branch records.
- No proof that branch alphas cover the strict Eq5 alpha domain.
- No selected-span coverage or displayed-vector construction.
- No terminal exactness, classifier, back-to-label map, or Lemma 5 order
  count.
- No pole order, normal crossings, or RLCT extraction.
