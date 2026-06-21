# Statement Card - A5 Lemma 5 Eq5 Case 2 Weight Update

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound`

## Claim

For one supplied Eq5 own-block branch whose label is `J+1`, any supplied Case
2 recurrence post-state with the standard new-label data satisfies Aoyagi's
row-weight update:

```text
post.weight i = u * pre.weight i
```

for every `i` with `J+1 <= i`.

## Inputs

- Supplied Eq5 piecewise source-vector certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit actual-width lower bound
  `aoyagiSelectedWidthNat ell m p <= n(S+1)`.
- Label identity `J+1 = Htilde'_p + 1 - alpha`.
- Supplied `IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u`.

## Proves

Only the conditional recurrence-weight update for one supplied Eq5 branch and
one supplied Case 2 post-data package.

## Does Not Prove

- Production of the post-state by a blow-up chart.
- Construction of Eq5 displayed vectors or all Eq5 branches.
- Any `LabelExponentCertificate`, terminal exponent, or least-value field.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27, plus the generic Case 2
recurrence-weight theorem for supplied post-data.
