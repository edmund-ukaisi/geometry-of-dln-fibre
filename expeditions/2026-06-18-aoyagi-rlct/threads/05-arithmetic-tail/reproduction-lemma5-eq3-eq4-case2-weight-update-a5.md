# Reproduction - Lemma 5 Eq3/Eq4 Case 2 Recurrence Weight Update

Status: checked conditional recurrence/API wrapper.

This note records the recurrence-weight consequence of supplied equation `(3)`
and `(4)` endpoint labels.  It assumes a supplied Case 2 post-data package; it
does not prove that a blow-up chart produces that post-state.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, supplies endpoint labels:

- Eq4 lower endpoint: `k = Htilde_p + 1` at source coordinate
  `S_(p+1)-1`.
- Eq3 upper endpoint: `k = Htilde'_1 + 1` at source coordinate `S_2-1`.

In the Case 2 recurrence bookkeeping, adding a new current-layer label at
level `J` with new variable `u` multiplies all row weights from row `J+1`
onward by `u`.

The existing Lean source-label wrappers already prove that, under explicit
actual-width compatibility and the source-side guards, these endpoint labels
are actual source labels.  The generic recurrence API already proves the
supplied post-data weight update for any actual new current-layer label.

## Reproduction

### Equation `(4)`

Fix one supplied Eq4 endpoint branch and a state label index `J` satisfying:

```text
J + 1 = Htilde_p + 1.
```

The existing Eq4 actual-label wrapper gives:

```text
actualWidthLabel L n (C.point p - 1) (J+1).
```

Assume supplied Case 2 recurrence post-data for a pre-state at
`(C.point p - 1,J)` and a post-state at `(C.point p - 1,J+1)`.  The generic
recurrence theorem then gives:

```text
post.weight i = u * pre.weight i
```

for every row `i` satisfying `J+1 <= i`.

### Equation `(3)`

Fix one supplied Eq3 endpoint branch and a state label index `J` satisfying:

```text
J + 1 = Htilde'_1 + 1.
```

The existing Eq3 actual-label wrapper gives:

```text
actualWidthLabel L n (C.point 1 - 1) (J+1).
```

With supplied Case 2 recurrence post-data for a pre-state at
`(C.point 1 - 1,J)` and a post-state at `(C.point 1 - 1,J+1)`, the same generic
recurrence theorem gives:

```text
post.weight i = u * pre.weight i
```

for every row `i` satisfying `J+1 <= i`.

The Eq3 proof keeps the one-unit slack hypothesis explicit.

## Lean Targets

```text
aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
```

## Kill Conditions

- Keep the supplied Eq3/Eq4 piecewise certificates.
- Keep Eq4's repaired guards and actual-width compatibility hypothesis.
- Keep Eq3's explicit one-unit slack and actual-width compatibility hypothesis.
- Keep the supplied Case 2 recurrence post-data hypothesis.
- Do not infer that a blow-up chart produces the post-state.
- Do not infer all branches, displayed-vector construction, terminal exponent,
  least-value data, `LabelExponentCertificate`, Lemma 5 order count, normal
  crossings, or RLCT extraction.
