# Statement card - A5 Lemma 5 equation (5) source label

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerIncrementPrefix_le_prefixSum_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_add_one_pos_any_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiPrefixSum_sub_current_le_mul_pred_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_le_selectedWidth_of_selectedWidth_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_le_selectedWidth_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel`

## Claim

Lean now proves equation `(5)`'s own-coordinate source-label legality as a
conditional arithmetic bridge.  If

```text
k = Htilde'_p + 1 - alpha,
1 <= alpha <= Htilde'_p-Htilde_p,
```

and Definition 3's selected-width hypotheses hold, then

```text
1 <= k <= aoyagiSelectedWidthNat ell m p.
```

With explicit actual-width compatibility

```text
n((C.point p - 1)+1) = aoyagiSelectedWidthNat ell m p,
```

Lean concludes

```text
actualWidthLabel L n (C.point p - 1) k.
```

For a supplied full equation `(5)` piecewise certificate, Lean also combines
this source-label fact with the own-coordinate value rewrite

```text
T(C.point p - 1) = k-1.
```

## Inputs

- Definition 3 selected-width sum and strict selected-width inequalities.
- `1<=ell`, `a<=ell`, and in-range selected coordinate `p<=ell`.
- Equation `(5)` offset guards `1<=alpha` and
  `alpha<=aoyagiLemma5IntervalExcess ell a p`.
- Source layer bounds for `C.point p - 1` and actual-width compatibility.
- For the piecewise wrapper, a supplied
  `AoyagiLemma5Eq5PiecewiseSourceVector`.

## Proves

- Lower label bound `1<=Htilde'_p+1-alpha`.
- Upper label bound `Htilde'_p+1-alpha<=W_p`.
- Actual source-label legality at the own source layer under width
  compatibility.
- For a supplied piecewise certificate, the own-coordinate value is `k-1` and
  the label is actual-width legal.

## Does Not Prove

- Construction or existence of equation `(5)`'s displayed vector.
- Terminal `tilde t=0`.
- Coverage outside the supplied selected-span branch certificate.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Definition 3, PDF pp. 8-9; displayed `Htilde` chains, PDF p. 25;
Aoyagi Lemma 5 equation `(5)`, PDF p. 27.

## Review

Pen-and-paper scout: `Sagan` (xhigh).
Lean API scout: `Averroes` (xhigh).
Final landed review: `review-lemma5-eq5-source-label-a5.md`.
