# Statement Card - A5 Lemma 5 Eq5 Domain Insert

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound`

## Claim

For one supplied Eq5 own-block branch whose label is `J+1`, the finite domain
of introduced labels advances by inserting exactly that label:

```text
introducedLabelFinset L n S (J+1)
  = insert (Sigma.mk S (J+1)) (introducedLabelFinset L n S J).
```

## Inputs

- Supplied Eq5 piecewise source-vector certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width lower bound
  `aoyagiSelectedWidthNat ell m p <= n(S+1)`.
- Label identity `J+1 = Htilde'_p + 1 - alpha`.

## Proves

Only a finite-domain insert equality for one supplied Eq5 branch label.

## Does Not Prove

- Construction of Eq5 displayed vectors or all Eq5 branches.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27.
