# Statement Card - A5 Lemma 5 Eq3 Component Domain/Recurrence/Exponent

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds`

## Claim

For one supplied Eq3-shaped upper component whose label is `J+1`, supplied
actual-width compatibility and supplied label bounds let the component feed the
generic one-step introduced-label finite-domain, recurrence-weight, and
exponent-domain extension APIs.

## Inputs

- Guards `1 <= p` and `p <= ell-a`.
- Last-cutpoint source range `C.point ell <= L+1`.
- Actual-width compatibility
  `n((C.point p - 1)+1) = aoyagiSelectedWidthNat ell m p`.
- Supplied label bounds
  `1 <= Htilde'_p+1 <= aoyagiSelectedWidthNat ell m p`.
- Supplied Eq3-shaped piecewise source-vector certificate.
- Label identity `J+1 = Htilde'_p+1`.
- For the recurrence wrapper, supplied `Case2SuppliedPostData`.
- For the exponent wrapper, prior `IntroducedLabelExponentCertificates`,
  supplied new-label terminal-exponent equality, supplied new-label
  least-value proof, and old-label preservation data.

## Proves

- One-step `introducedLabelFinset` insert equality.
- One-step `introducedLabelFinset` cardinality increment.
- Supplied Case 2 recurrence weights satisfy
  `post.weight i = u * pre.weight i` for `J+1 <= i`.
- Supplied exponent-certificate domain extension from `(S,J)` to `(S,J+1)`
  with `S=C.point p-1`.

## Does Not Prove

- Derivation of the supplied label bounds from Definition 3.
- The terminal-exponent formula for the Eq3 component.
- The least-value theorem for the Eq3 component.
- Construction of the Eq3 displayed vector or all branch families.
- Chart production, terminality, admissibility, chart coverage, Lemma 5 order
  count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 Eq3-shaped upper branch, PDF pp. 26-27, represented by a
supplied piecewise certificate.  The domain/recurrence/exponent handoff uses
generic Lean APIs after source-label legality is supplied.
