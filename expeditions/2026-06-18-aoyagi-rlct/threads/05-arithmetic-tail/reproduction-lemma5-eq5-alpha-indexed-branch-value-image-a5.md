# Pen-and-paper reproduction - Lemma 5 equation (5) alpha-indexed branch value image

Status: reproduced; Lean checked; xhigh review pending.

## Source

Aoyagi PDF p. 27, equation `(5)`, gives a strict alpha-indexed own-coordinate
value of the form

```text
Htilde'_p - alpha
```

for each strict offset parameter in the Eq5 alpha domain

```text
1 <= alpha <= min(excess(ell,a,p), p-1).
```

The source passage does not by itself construct an abstract branch-record type
or prove that a supplied finite branch family has exactly this alpha image.
Those are kept as explicit hypotheses.

## Reproduction

Let `branches` be any finite family of records, with an alpha projection

```text
alphaOf : beta -> Nat
```

and a value projection

```text
value : beta -> Int.
```

Assume the alpha projection has image exactly the strict Eq5 domain:

```text
branches.image alphaOf = aoyagiLemma5Eq5AlphaDomain ell a p.
```

Assume also that every branch value is the Eq5 own-coordinate expression:

```text
value b = Htilde'_p - alphaOf b
```

for all `b` in `branches`.  Then the branch-value image is exactly the
alpha-family image

```text
image (alpha |-> Htilde'_p - alpha) (aoyagiLemma5Eq5AlphaDomain ell a p).
```

The previous value-image theorem identifies this image with
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.

The calculation is only finite-set extensionality:

- If `z=value b`, use `alpha=alphaOf b`; the alpha-image hypothesis puts this
  alpha in the strict domain, and the value hypothesis rewrites `z`.
- If `z=Htilde'_p-alpha` for an alpha in the strict domain, the alpha-image
  hypothesis supplies a branch `b` with `alphaOf b=alpha`; the value
  hypothesis rewrites `value b=z`.

No injectivity is required, because the conclusion is equality of images, not
equality or cardinality of branch records.

## Lean Target

```text
aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet
```

## Nonclaims

- No construction of the branch records.
- No construction of equation `(5)`'s displayed vector.
- No source-label legality, cutoff guard, selected-span coverage, or terminal
  `tilde t=0`.
- No branch injectivity, classifier, back-to-label coverage, or exact
  terminal-minimum label count.
- No Lemma 5 pole-order count, normal crossings, or RLCT extraction.

The theorem becomes misleading if `halpha_image` is weakened to inclusion, if
the value formula is not branchwise, or if an image equality is read as a
cardinality statement.
