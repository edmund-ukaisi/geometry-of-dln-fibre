# Statement card - A5 Lemma 5 equation (5) alpha-indexed branch value image

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet`

## Claim

For any finite branch set `branches`, if

```text
branches.image alphaOf = aoyagiLemma5Eq5AlphaDomain ell a p
```

and every branch satisfies

```text
value b = aoyagiHtildeUpperNat ell a M m p - alphaOf b,
```

then

```text
branches.image value = aoyagiLemma5Eq5OffsetValueSet ell a p M m.
```

## Proved

Lean proves this by finite-set extensionality, using the alpha-image equality
in both directions and then applying
`aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet`.

## Assumed

The branch family, alpha projection, value projection, exact alpha-image
coverage, and branchwise value formula are all supplied.

## Cited

None in Lean.  Source fidelity is only to the finite alpha/value shape of
Aoyagi PDF p. 27 equation `(5)`.

## Deferred

Branch construction, equation `(5)` displayed vectors, source labels,
cutoff/selected-span coverage, terminal `tilde t=0`, injection, classifier,
back-to-label coverage, Lemma 5 count, normal crossings, pole order, and RLCT
extraction.

## Review

- Controller pen-and-paper reproduction completed.
- Focused Lean checks passed for `Lemma5DisplayedVector.lean` and
  `Lemma5SourceLabel.lean`.
- Independent xhigh reviewer `Anscombe` returned `survived` with no findings.
