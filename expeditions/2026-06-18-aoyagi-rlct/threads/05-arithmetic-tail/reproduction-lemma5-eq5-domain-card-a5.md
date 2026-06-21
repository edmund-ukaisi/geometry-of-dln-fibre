# Reproduction - Lemma 5 Eq5 One-Step Introduced Domain Cardinality

Status: checked finite-domain/cardinality wrapper.

This note records the cardinality consequence of the one-step finite-domain
update attached to one supplied equation `(5)` branch.  It does not construct
the Eq5 displayed vector family or prove the Lemma 5 order count.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(5)` uses a source block coordinate with label
  `k = Htilde'_p + 1 - alpha`.
- The branch value is `k-1`.
- The current-layer introduced-label bookkeeping advances through the label
  `k`.

The source-facing content is the same as in the one-step insert wrapper: under
the explicit actual-width lower bound at the own-block source index, the label
`k` is an actual source label.  The cardinality step below is finite-set
bookkeeping over that source label.

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

The one-step finite-domain equality gives:

```text
introducedLabelFinset L n S (J+1)
  = insert (Sigma.mk S (J+1)) (introducedLabelFinset L n S J).
```

The new pair is not in the old domain.  Indeed, any same-source label
introduced before advancing beyond `J` has current label coordinate at most
`J`, while the new pair has coordinate `J+1`.

Therefore:

```text
(introducedLabelFinset L n S (J+1)).card
  = (insert (Sigma.mk S (J+1))
      (introducedLabelFinset L n S J)).card
  = (introducedLabelFinset L n S J).card + 1.
```

Substituting the Eq5 actual-label proof gives the source-facing Eq5
cardinality wrapper.

## Lean Targets

```text
introducedLabelFinset_card_succ_eq_succ
aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound
```

## Kill Conditions

- Keep the supplied Eq5 piecewise certificate.
- Keep the last-cutpoint range and actual-width lower-bound hypotheses.
- Do not infer all Eq5 branches or any displayed-vector family.
- Do not turn this one-step cardinality increment into the Lemma 5 order count.
- Do not infer `LabelExponentCertificate`, terminal exponent, least-value,
  admissibility, chart sequence, normal crossings, or RLCT extraction.
