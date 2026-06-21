# Statement Card - A5 Lemma 5 Eq3-Shaped Component Supplied Label Bounds

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds`

## Claim

For a supplied Eq3-shaped component value at coordinate `p`, if the actual
source width agrees with the selected width and the upper-endpoint label bounds
are supplied, then the label `k = Htilde'_p+1` is an actual source label.  The
same data also give introduced-label and finite introduced-label membership
for the current state.

## Inputs

- Guards `1 <= p` and `p <= ell-a`.
- Last-cutpoint source range `C.point ell <= L+1`.
- Actual-width compatibility
  `n((C.point p - 1)+1) = aoyagiSelectedWidthNat ell m p`.
- Supplied label bounds
  `1 <= Htilde'_p+1 <= aoyagiSelectedWidthNat ell m p`.
- Supplied Eq3-shaped piecewise source-vector certificate.

## Proves

- `T(C.point p - 1) = k-1`.
- `actualWidthLabel L n (C.point p - 1) k`.
- `introducedLabel L n (C.point p - 1) k (C.point p - 1) k`.
- `Sigma.mk (C.point p - 1) k` lies in
  `introducedLabelFinset L n (C.point p - 1) k`.
- The same component value lies in the same-coordinate interval.

## Does Not Prove

- Derivation of the supplied label bounds from Definition 3.
- Construction of the Eq3 displayed vector.
- Terminality, all-interval coverage, all-branch coverage, Lemma 5 order
  count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 Eq3-shaped upper branch, PDF pp. 26-27, represented by a
supplied piecewise certificate.  Label legality is supplied as an explicit
hypothesis in this theorem.
