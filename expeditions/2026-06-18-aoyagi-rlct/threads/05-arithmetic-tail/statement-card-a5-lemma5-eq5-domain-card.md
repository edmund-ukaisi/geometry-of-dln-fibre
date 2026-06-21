# Statement Card - A5 Lemma 5 Eq5 Domain Cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.introducedLabelFinset_card_succ_eq_succ`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound`

## Claim

For one supplied Eq5 own-block branch whose label is `J+1`, advancing the
finite domain of introduced labels from `J` to `J+1` increases cardinality by
one:

```text
(introducedLabelFinset L n S (J+1)).card
  = (introducedLabelFinset L n S J).card + 1.
```

## Inputs

- Supplied Eq5 piecewise source-vector certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width lower bound
  `aoyagiSelectedWidthNat ell m p <= n(S+1)`.
- Label identity `J+1 = Htilde'_p + 1 - alpha`.

## Proves

Only a one-step cardinality increment for the introduced-label finite domain
at one supplied Eq5 branch label.

## Does Not Prove

- Construction of Eq5 displayed vectors or all Eq5 branches.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27, plus finite-domain bookkeeping
already formalised in `introducedLabelFinset_succ_eq_insert` and
`not_mem_introducedLabelFinset_case2_new_before`.
