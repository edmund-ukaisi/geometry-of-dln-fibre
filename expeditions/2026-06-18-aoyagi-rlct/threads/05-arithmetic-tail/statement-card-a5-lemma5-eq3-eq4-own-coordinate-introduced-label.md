# Statement card - A5 Lemma 5 equations (3)/(4) own-coordinate introduced labels

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint`

## Claim

For supplied equation `(3)` and `(4)` piecewise certificates, the own
coordinate can be packaged as a post-advance introduced label.

Equation `(4)` proves:

```text
T (C.point p-1) = k-1
introducedLabel L n (C.point p-1) k (C.point p-1) k
```

for `k=Htilde_p+1`.

Equation `(3)` proves:

```text
T (C.point 1-1) = k-1
introducedLabel L n (C.point 1-1) k (C.point 1-1) k
```

for `k=Htilde'_1+1`.

## Inputs

- The relevant supplied piecewise certificate.
- Definition 3 selected-width sum and strict selected-width inequalities.
- Last selected cutpoint range `C.point ell<=L+1`.
- Actual-width compatibility at the own source layer.
- For equation `(3)`, the explicit slack `W_1+2<=M`.

## Proves

- Own-coordinate value `T S=k-1`.
- Post-advance introduced-label membership `introducedLabel L n S k S k`.

## Does Not Prove

- Existence of the supplied piecewise certificate.
- Displayed-vector construction.
- Actual-width compatibility from Definition 3 alone.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF pp. 26-27.
