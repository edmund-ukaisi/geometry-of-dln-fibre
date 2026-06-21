# Reproduction - Lemma 5 Eq5 One-Step Introduced Domain Insert

Status: checked finite-domain/API wrapper.

This note records the finite-domain update attached to one supplied equation
`(5)` branch.  It does not construct the Eq5 displayed vector family.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(5)` uses a source block coordinate with label
  `k = Htilde'_p + 1 - alpha`.
- The branch value is `k-1`.
- The current-layer introduced-label bookkeeping advances through the label
  `k`.

The existing Lean source-label wrapper already proves that, under the explicit
actual-width lower bound at the own-block source index, this `k` is an actual
source label.

## Reproduction

Fix one supplied Eq5 piecewise certificate, one own-block source index `S`, and
one state label index `J` satisfying:

```text
J + 1 = Htilde'_p + 1 - alpha.
```

The existing Eq5 actual-label wrapper gives:

```text
actualWidthLabel L n S (J+1).
```

The generic finite-domain theorem says that if `(S,J+1)` is an actual source
label, then advancing the current layer from `J` to `J+1` adds exactly this
new label:

```text
introducedLabelFinset L n S (J+1)
  = insert (Sigma.mk S (J+1)) (introducedLabelFinset L n S J).
```

Substituting the Eq5 actual-label proof into this theorem gives the desired
specialized wrapper.

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound
```

## Kill Conditions

- Keep the supplied Eq5 piecewise certificate.
- Keep the last-cutpoint range and actual-width lower-bound hypotheses.
- Do not infer all Eq5 branches or any displayed-vector family.
- Do not infer `LabelExponentCertificate`, terminal exponent, least-value,
  admissibility, chart sequence, Lemma 5 order count, normal crossings, or
  RLCT extraction.
