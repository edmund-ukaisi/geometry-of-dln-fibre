# Reproduction - Lemma 5 Eq5 Case 2 Recurrence Weight Update

Status: checked conditional recurrence/API wrapper.

This note records the recurrence-weight consequence of one supplied Eq5
current-layer label.  It assumes a supplied Case 2 post-data package; it does
not prove that a blow-up chart produces that post-state.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, uses Eq5 labels

```text
k = Htilde'_p + 1 - alpha
```

as current-layer introduced labels.  In the Case 2 recurrence bookkeeping,
adding the new current-layer label at level `J` with new variable `u` multiplies
all row weights from row `J+1` onward by `u`.

The existing Lean source-label wrapper already proves that, under the explicit
actual-width lower bound at the own-block source index, this Eq5 label is an
actual source label.  The generic recurrence API already proves the supplied
post-data weight update for any actual new current-layer label.

## Reproduction

Fix one supplied Eq5 branch and a state label index `J` satisfying:

```text
J + 1 = Htilde'_p + 1 - alpha.
```

The existing Eq5 actual-label wrapper gives:

```text
actualWidthLabel L n S (J+1).
```

Assume supplied Case 2 recurrence post-data for a pre-state at `(S,J)` and a
post-state at `(S,J+1)`.  This post-data states:

```text
old introduced labels keep their level and variable,
the new label (S,J+1) has level J,
the new label (S,J+1) has variable u.
```

The generic recurrence theorem then gives:

```text
post.weight i = u * pre.weight i
```

for every row `i` satisfying `J+1 <= i`.

Substituting the Eq5 actual-label proof into this generic theorem gives the
source-facing Eq5 wrapper.

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound
```

## Kill Conditions

- Keep the supplied Eq5 piecewise certificate.
- Keep the last-cutpoint range and actual-width lower-bound hypotheses.
- Keep the supplied Case 2 recurrence post-data hypothesis.
- Do not infer that a blow-up chart produces the post-state.
- Do not infer all Eq5 branches, displayed-vector construction, terminal
  exponent, least-value data, `LabelExponentCertificate`, Lemma 5 order count,
  normal crossings, or RLCT extraction.
