# Statement card - A5 Lemma 5 equation (4) actual-width label

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility`

## Statement

If equation `(4)`'s selected source layer `C.point p - 1` lies in the global
source range, if the actual layer width at that source layer equals the
selected width `W_(p+1)`, and if the natural label `k` has integer value
`Htilde_p+1`, then `k` is an `actualWidthLabel`.

## Assumed

- Definition 3 selected-width sum and strict selected-width inequality.
- `1<=ell`, `a<=ell`, `1<=p`, and `p<=a`.
- Global source-layer bounds for `C.point p - 1`.
- Explicit width compatibility:
  `(n((C.point p - 1)+1) : Int) = aoyagiSelectedWidthNat ell m p`.
- Explicit Nat/Int label identification:
  `(k : Int) = aoyagiHtildeLowerNat ell a M m p + 1`.

## Cited

- None in Lean.  This is finite label-range bookkeeping.

## Deferred

- Selected-width/actual-width compatibility as a constructed fact.
- Introduced-label status in any blow-up stage.
- Displayed-vector construction, terminal `tilde t=0`, terminal exponent,
  least value, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`
