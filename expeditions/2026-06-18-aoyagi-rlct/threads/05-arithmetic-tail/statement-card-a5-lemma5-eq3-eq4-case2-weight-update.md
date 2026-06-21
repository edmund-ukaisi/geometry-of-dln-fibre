# Statement Card - A5 Lemma 5 Eq3/Eq4 Case 2 Weight Update

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`

## Claim

For supplied Eq4 and Eq3 endpoint branches whose label is `J+1`, any supplied
Case 2 recurrence post-state with the standard new-label data satisfies
Aoyagi's row-weight update:

```text
post.weight i = u * pre.weight i
```

for every `i` with `J+1 <= i`.

## Inputs

- Supplied Eq4 or Eq3 piecewise source-vector certificate.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width compatibility at the endpoint source layer.
- Eq4: `1 <= p`, `p <= ell-a`, source selected-width hypotheses, and the
  label identity `J+1 = Htilde_p + 1`.
- Eq3: `a < ell`, explicit slack `W_1 + 2 <= M`, source selected-width
  hypotheses, and the label identity `J+1 = Htilde'_1 + 1`.
- Supplied `IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u`.

## Proves

Only the conditional recurrence-weight update for one supplied Eq4 or Eq3
endpoint branch and one supplied Case 2 post-data package.

## Does Not Prove

- Production of the post-state by a blow-up chart.
- Construction of Eq3/Eq4 displayed vectors or all endpoint branches.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF pp. 26-27, plus the generic Case
2 recurrence-weight theorem for supplied post-data.
