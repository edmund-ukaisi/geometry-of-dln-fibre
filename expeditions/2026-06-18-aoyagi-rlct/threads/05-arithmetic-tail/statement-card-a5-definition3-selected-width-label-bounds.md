# Statement card - A5 Definition 3 selected-width label bounds

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_mul_le_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`

## Statement

Lean now proves that Definition 3's selected-width arithmetic gives both
label bounds for Aoyagi Lemma 5 equation `(4)`'s label

```text
k = Htilde_p + 1.
```

Under the source selected-width hypotheses, `a<=ell`, `1<=p`, and `p<=a`,

```text
1 <= Htilde_p+1 <= W_(p+1).
```

## Proved

- The tail estimate
  `sum_{i=p+2}^{ell+1} W_i <= (ell-p)(M-1)`.
- The lower prefix inequality `pM <= P_(p+1)`.
- The lower label bound `1<=Htilde_p+1`.
- The full equation `(4)` label bound after combining with the previous
  upper-label theorem.

## Assumed

- `1<=ell` and `a<=ell`.
- The selected-width sum `sum W = ell*(M-1)+a`.
- The strict source selected inequality `ell*W_i < sum W` for every selected
  width.
- For the full label-bound theorem: `1<=p` and `p<=a`.

## Cited

- None in Lean.  This is finite arithmetic from Aoyagi Definition 3.

## Deferred

- The displayed cutoff in equation `(4)` still needs the selected-index guard
  `p+1<=a`, unless a separate terminal selected-index convention is supplied.
- The own-coordinate calculation still needs `p<=ell-a`.
- Equation `(3)`'s one-unit slack guard `W_1+2<=M`.
- Full equations `(3)` and `(4)` displayed-family realisation.
- `tilde t=0`, vector admissibility, Lemma 5 order count, pole order, normal
  crossings, and RLCT extraction.

## Review

- Source scout: xhigh `Bacon`.
- Lean/definition scout: xhigh `Sartre`.
- Pen-and-paper checker: xhigh `Noether`.
- Landed-patch review passed by xhigh `Franklin`:
  `review-definition3-selected-width-label-bounds-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
