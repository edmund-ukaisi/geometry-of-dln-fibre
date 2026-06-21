# Statement card - A5 Lemma 5 equation (5) block source label

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block`

## Claim

Lean now has an arbitrary-own-block version of the equation `(5)` source-label
bridge.  For any source index `S`, if the selected-width hypotheses and Eq5
offset guards prove

```text
1 <= k <= W_p,
```

and the actual source layer satisfies

```text
1 <= S <= L,
n(S+1)=W_p,
```

then

```text
actualWidthLabel L n S k.
```

If a supplied equation `(5)` piecewise certificate is also given and
`C.block p S`, Lean combines this label legality with the own-branch value

```text
T(S)=k-1.
```

## Inputs

- Definition 3 selected-width sum and strict selected-width inequalities.
- Equation `(5)` offset guards `1<=alpha` and
  `alpha<=aoyagiLemma5IntervalExcess ell a p`.
- Source-layer range and actual-width compatibility at the particular `S`.
- For the value rewrite, a supplied `AoyagiLemma5Eq5PiecewiseSourceVector` and
  `C.block p S`.

## Proves

- Actual source-label legality at arbitrary `S` under explicit width
  compatibility.
- For `S` in the own selected block, the supplied Eq5 value is `k-1` and the
  label is actual-width legal.

## Does Not Prove

- That arbitrary block points have actual width `W_p`.
- Construction or existence of equation `(5)`'s displayed vector.
- Terminal `tilde t=0`.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF p. 27, plus Definition 3 selected-width
hypotheses, PDF pp. 8-9.

## Review

Pen-and-paper scout: `Godel` (xhigh).
Final landed review: `Hypatia` (xhigh),
`review-lemma5-eq5-block-source-label-a5.md`.
