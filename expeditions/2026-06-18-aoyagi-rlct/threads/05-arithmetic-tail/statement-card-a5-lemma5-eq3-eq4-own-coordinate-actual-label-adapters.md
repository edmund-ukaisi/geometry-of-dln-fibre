# Statement card - A5 Lemma 5 equations (3)/(4) own-coordinate actual-label adapters

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack`

## Claim

For supplied equation `(3)` and `(4)` piecewise certificates, Lean now packages
the own-coordinate value and actual-label legality into one conclusion:

```text
T(S) = k-1
actualWidthLabel L n S k.
```

Equation `(4)` uses `S=C.point p-1` and `k=Htilde_p+1`.  Equation `(3)` uses
`S=C.point 1-1` and `k=Htilde'_1+1`.

## Inputs

- The relevant supplied piecewise certificate.
- Definition 3 selected-width sum and strict selected-width inequalities.
- Source range and actual-width compatibility at the own source layer.
- For equation `(3)`, the explicit slack `W_1+2<=M`.

## Proves

- Own-coordinate value equals the source label predecessor.
- The same label is legal for the actual source layer.

## Does Not Prove

- Displayed-vector construction.
- Actual-width compatibility from Definition 3.
- Equation `(3)` label legality without the explicit slack.
- Terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5 order
  count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF pp. 26-27.
