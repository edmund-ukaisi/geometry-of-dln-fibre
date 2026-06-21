# Statement Card - A5 Lemma 5 Eq3/Eq4 Domain Insert and Cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`

## Claim

For supplied Eq4 and Eq3 endpoint branches whose label is `J+1`, advancing the
introduced-label finite domain from `J` to `J+1` inserts exactly that endpoint
label and increases finite-domain cardinality by one.

Eq4:

```text
introducedLabelFinset L n (C.point p - 1) (J+1)
  = insert (Sigma.mk (C.point p - 1) (J+1))
      (introducedLabelFinset L n (C.point p - 1) J)
```

Eq3:

```text
introducedLabelFinset L n (C.point 1 - 1) (J+1)
  = insert (Sigma.mk (C.point 1 - 1) (J+1))
      (introducedLabelFinset L n (C.point 1 - 1) J)
```

Both have the corresponding cardinality increment by one.

## Inputs

- Supplied Eq4 or Eq3 piecewise source-vector certificate.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width compatibility at the endpoint source layer.
- Eq4: `1 <= p`, `p <= ell-a`, source selected-width hypotheses, and the
  label identity `J+1 = Htilde_p + 1`.
- Eq3: `a < ell`, explicit slack `W_1 + 2 <= M`, source selected-width
  hypotheses, and the label identity `J+1 = Htilde'_1 + 1`.

## Proves

Only one-step finite-domain insert and cardinality equalities for supplied
Eq3/Eq4 endpoint branches.

## Does Not Prove

- Construction of Eq3/Eq4 displayed vectors or all endpoint branches.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF pp. 26-27, plus finite-domain
bookkeeping already formalised in `introducedLabelFinset_succ_eq_insert` and
`introducedLabelFinset_card_succ_eq_succ`.
