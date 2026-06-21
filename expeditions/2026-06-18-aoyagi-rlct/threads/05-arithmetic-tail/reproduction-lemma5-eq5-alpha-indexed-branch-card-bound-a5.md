# Reproduction - Lemma 5 Eq5 alpha-indexed branch cardinal bound

Status: reproduced; Lean checked; xhigh review pending.

This note packages the previous Eq5 alpha-indexed branch-label image slice as
finite cardinal upper bounds.  It does not construct the branch family or prove
coverage of any target label set.

## Source

Aoyagi PDF p. 27, equation `(5)`, assigns strict-offset branch labels of the
form

```text
k = Htilde'_p + 1 - alpha.
```

The previous checkpoint proved two supplied-boundary facts for a finite family
of such labels:

```text
branches.image branchLabel <= actualWidthLabelFinset L n,
(branches.image branchLabel).card = branches.card.
```

The second equality requires the supplied alpha projection to be injective on
`branches`.

## Reproduction

Let `branches : Finset beta` be a supplied finite family of Eq5 branch records.
Let

```text
alphaOf : beta -> Nat
branchLabel : beta -> Sigma (fun _ : Nat => Nat)
```

be supplied maps.  Assume the same branchwise hypotheses as in the image slice:

```text
alphaOf b in aoyagiLemma5Eq5AlphaDomain ell a p,
1 <= (branchLabel b).fst <= L,
W_p <= n((branchLabel b).fst + 1),
(branchLabel b).snd = Htilde'_p + 1 - alphaOf b.
```

Also assume `alphaOf` is injective on `branches`.  The previous image-card
theorem gives

```text
branches.card = (branches.image branchLabel).card.
```

The previous image-subset theorem gives

```text
branches.image branchLabel <= actualWidthLabelFinset L n.
```

Finite-set monotonicity of cardinality then gives

```text
(branches.image branchLabel).card
  <= (actualWidthLabelFinset L n).card.
```

If `alphaOf` is injective on `branches`, then the image-cardinality theorem
also gives

```text
branches.card
  = (branches.image branchLabel).card
  <= (actualWidthLabelFinset L n).card.
```

The first inequality counts distinct supplied alpha-indexed Eq5 branch labels.
The second counts the supplied branches themselves under supplied injectivity.
Neither theorem is a source construction of the branch family, and neither is
an upper bound for terminal-minimum labels unless an additional classifier or
no-extra theorem is supplied.

## Lean targets

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card
aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card
```

## Nonclaims

- No construction of Eq5 branch records.
- No proof that branch alphas cover the strict Eq5 alpha domain.
- No selected-span coverage or displayed-vector construction.
- No terminal exactness, classifier, back-to-label map, or Lemma 5 order
  count.
- No pole order, normal crossings, or RLCT extraction.
