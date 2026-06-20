# Statement card - A5 Definition 3 selected-width upper label bound

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality`

## Statement

Lean now proves that Definition 3's strict selected-width inequality implies
each selected width is at most `M-1`.  Consequently, for equation `(4)`, the
upper label bound

```text
Htilde_p + 1 <= W_(p+1)
```

holds under `1<=p`, `p<=a`, and the Definition 3 selected-width hypotheses.

## Proved

- Selected widths satisfy `W_i <= M-1` from the source strict inequality.
- The previous selected-width prefix satisfies `P_p+1 <= pM` for `1<=p`.
- The upper label bound for `k=Htilde_p+1` follows.

## Assumed

- `1<=ell` and `a<=ell`.
- The selected-width sum `sum W = ell*(M-1)+a`.
- The strict source selected inequality `ell*W_i < sum W` for every selected
  width.
- For the equation `(4)` consequence: `1<=p` and `p<=a`.

## Cited

- None in Lean.  This is finite arithmetic from Aoyagi Definition 3.

## Deferred

- The lower label bound `1<=Htilde_p+1`, equivalently `pM<=P_(p+1)`.
- Equation `(3)`'s one-unit slack guard `W_1+2<=M`.
- Full equations `(3)` and `(4)` displayed-family realisation.
- `tilde t=0`, vector admissibility, Lemma 5 order count, pole order, normal
  crossings, and RLCT extraction.

## Review

- Source/Lean scout: xhigh `Linnaeus`.
- Landed-patch review passed by xhigh `Bohr`:
  `review-definition3-selected-width-upper-label-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
