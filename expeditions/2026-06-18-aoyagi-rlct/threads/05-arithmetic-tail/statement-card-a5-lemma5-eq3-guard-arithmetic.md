# Statement card - A5 Lemma 5 equation (3) guard arithmetic

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_selectedIndexGuard_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards`

## Statement

Lean now records three guard facts for Aoyagi Lemma 5 equation `(3)`.

First, the displayed special cutoff `S_(ell-a+2)` lies inside the selected
source list `S_1,...,S_(ell+1)` exactly when

```text
1 <= a.
```

Second, in the interior case `1<=a` and `a<ell`,

```text
Htilde'_1 - Htilde_1 = 1.
```

Third, when `a<ell`, the label bounds for `k=Htilde'_1+1` are equivalent to

```text
M-1 <= W_1+W_2,
W_1+2 <= M.
```

## Proved

- The exact selected-index guard for the equation `(3)` special cutoff.
- The first upper/lower Htilde gap in the interior case.
- The exact arithmetic reformulation of `1 <= Htilde'_1+1 <= W_2`.

## Assumed

- For the selected-index guard: `a<=ell`.
- For the first-gap theorem: `1<=a` and `a<ell`.
- For the label-bounds equivalence: `a<ell`.

## Cited

- None in Lean.  These are finite arithmetic consequences of the displayed
  Htilde definitions and Definition 3's selected-index range.

## Deferred

- Full equations `(3)` and `(4)` displayed-family realisation.
- Legal-label bounds from Definition 3 alone.
- `tilde t=0`.
- Source vector-to-chain correspondence and vector admissibility.
- Lemma 5 chart-family coverage/order count, pole order, normal crossings, and
  RLCT extraction.

## Review

- Arithmetic scout: xhigh `Planck`.
- Landed-patch review passed by xhigh `Turing`:
  `review-lemma5-eq3-guard-arithmetic-a5.md`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
