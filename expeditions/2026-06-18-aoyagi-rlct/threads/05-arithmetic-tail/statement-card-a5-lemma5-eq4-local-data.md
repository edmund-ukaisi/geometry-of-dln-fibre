# Statement card - A5 Lemma 5 equation (4) local data

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_localData_of_sourceSelectedInequality`

## Statement

Lean now packages the corrected local arithmetic data for Aoyagi Lemma 5
equation `(4)`.  Under the selected-width hypotheses from Definition 3 and
the guards

```text
1<=p,     p+1<=a,     p<=ell-a,     a<=ell,
```

the theorem proves:

```text
p + (ell-a) + 2 <= ell+1,
Htilde'_p - p = Htilde_p,
1 <= Htilde_p+1 <= W_(p+1).
```

## Proved

- The displayed tail cutoff `S_(p+ell-a+2)` lies in the selected list.
- The own-coordinate displayed value equals `k-1` for
  `k=Htilde_p+1`.
- The source label `k=Htilde_p+1` is legal.

## Assumed

- `1<=ell` and `a<=ell`.
- The selected-width sum `sum W = ell*(M-1)+a`.
- The strict source selected inequality `ell*W_i < sum W` for every selected
  width.
- The corrected equation `(4)` guards `1<=p`, `p+1<=a`, and `p<=ell-a`.

## Cited

- None in Lean.  This is finite arithmetic from Aoyagi Definition 3 and Lemma
  5's displayed equation `(4)`.

## Deferred

- Full equation `(4)` displayed-vector construction.
- Terminal `tilde t=0`.
- Vector admissibility and source vector-to-chain correspondence.
- Lemma 5 chart-family coverage/order count, pole order, normal crossings,
  and RLCT extraction.

## Review

- Lean/API scout: xhigh `Mendel`.
- Pen-and-paper/source checker: xhigh `Feynman`.
- Review artifact:
  `review-lemma5-eq4-local-data-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
