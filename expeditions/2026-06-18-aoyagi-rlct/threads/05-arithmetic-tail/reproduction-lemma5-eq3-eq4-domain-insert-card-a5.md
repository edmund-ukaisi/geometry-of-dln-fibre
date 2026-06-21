# Reproduction - Lemma 5 Eq3/Eq4 One-Step Domain Insert and Cardinality

Status: checked finite-domain/API wrapper.

This note records the one-step finite-domain update attached to the supplied
equation `(3)` and `(4)` endpoint branches.  It does not construct the
displayed vector family or prove the Lemma 5 order count.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(4)` supplies the lower endpoint branch at source coordinate
  `S_(p+1)-1`, with label `k = Htilde_p + 1`.
- Equation `(3)` supplies the upper endpoint branch at source coordinate
  `S_2-1`, with label `k = Htilde'_1 + 1`.
- These endpoint labels participate in the same introduced-label finite-domain
  bookkeeping as the Eq5 strict-offset labels.

The existing Lean source-label wrappers already prove that, under explicit
actual-width compatibility and the source-side guards, these endpoint labels
are actual source labels.

## Reproduction

### Equation `(4)`

Fix a supplied Eq4 piecewise certificate and a state label index `J` satisfying:

```text
J + 1 = Htilde_p + 1.
```

The existing Eq4 actual-label wrapper gives:

```text
actualWidthLabel L n (C.point p - 1) (J+1).
```

The generic one-step finite-domain theorem gives:

```text
introducedLabelFinset L n (C.point p - 1) (J+1)
  = insert (Sigma.mk (C.point p - 1) (J+1))
      (introducedLabelFinset L n (C.point p - 1) J).
```

Since the new pair is not in the previous `J`-domain, the generic cardinality
theorem gives:

```text
(introducedLabelFinset L n (C.point p - 1) (J+1)).card
  = (introducedLabelFinset L n (C.point p - 1) J).card + 1.
```

### Equation `(3)`

Fix a supplied Eq3 piecewise certificate and a state label index `J` satisfying:

```text
J + 1 = Htilde'_1 + 1.
```

The existing Eq3 actual-label wrapper gives:

```text
actualWidthLabel L n (C.point 1 - 1) (J+1).
```

The same generic insert and cardinality theorems give:

```text
introducedLabelFinset L n (C.point 1 - 1) (J+1)
  = insert (Sigma.mk (C.point 1 - 1) (J+1))
      (introducedLabelFinset L n (C.point 1 - 1) J)

(introducedLabelFinset L n (C.point 1 - 1) (J+1)).card
  = (introducedLabelFinset L n (C.point 1 - 1) J).card + 1.
```

The Eq3 proof keeps the one-unit slack hypothesis explicit.

## Lean Targets

```text
aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint
aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint
aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
```

## Kill Conditions

- Keep the supplied Eq3/Eq4 piecewise certificates.
- Keep Eq4's repaired guards and actual-width compatibility hypothesis.
- Keep Eq3's explicit one-unit slack and actual-width compatibility hypothesis.
- Do not infer endpoint realisation beyond the supplied branch hypotheses.
- Do not infer all branches, displayed-vector construction, Lemma 5 order
  count, terminality, chart sequence, normal crossings, or RLCT extraction.
