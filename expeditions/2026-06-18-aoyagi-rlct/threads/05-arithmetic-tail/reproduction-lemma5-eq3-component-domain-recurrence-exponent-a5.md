# Reproduction - Lemma 5 Eq3 Component Domain/Recurrence/Exponent Wrappers

Status: checked supplied-bound/API wrapper.

This note records the p-general Eq3-shaped upper-component handoff from source
label legality, under supplied bounds, to the existing one-step finite-domain,
recurrence, and exponent-certificate APIs.  It does not compute terminal
exponents or least values.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, includes an equation `(3)`-shaped upper branch.
The preceding Lean slice packages a supplied Eq3-shaped component at coordinate
`p` as a source label only under explicit hypotheses:

```text
n((C.point p - 1)+1) = W_p
1 <= Htilde'_p+1 <= W_p.
```

These bounds are supplied.  This note does not derive them from Definition 3.

## Reproduction

Fix a supplied Eq3-shaped component and a state label index `J` satisfying:

```text
J + 1 = Htilde'_p + 1.
```

The previous source-label wrapper gives:

```text
actualWidthLabel L n (C.point p - 1) (J+1).
```

The generic one-step finite-domain theorem gives:

```text
introducedLabelFinset L n (C.point p - 1) (J+1)
  = insert (Sigma.mk (C.point p - 1) (J+1))
      (introducedLabelFinset L n (C.point p - 1) J).
```

Since the new current-layer label is not in the previous `J`-domain, the
generic cardinality theorem gives:

```text
(introducedLabelFinset L n (C.point p - 1) (J+1)).card
  = (introducedLabelFinset L n (C.point p - 1) J).card + 1.
```

For recurrence bookkeeping, a supplied Case 2 post-data package gives:

```text
post.weight i = u * pre.weight i
```

for every row `i` with `J+1 <= i`.

For exponent-domain bookkeeping, the actual label supplies only:

```text
introducedLabel L n (C.point p - 1) (J+1)
  (C.point p - 1) (J+1).
```

To extend the exponent-certificate family, two additional new-label fields
must be supplied explicitly:

```text
terminalExponent L (widthZ n) (t' (C.point p - 1) (J+1))
  = numerator' (C.point p - 1) (J+1)

IsLeast {v | exists i in Icc 1 L,
    t' (C.point p - 1) (J+1) i = v}
  (leastValue' (C.point p - 1) (J+1)).
```

Together with old-label preservation for vector, numerator, and least-value
data, the generic domain-extension theorem gives
`IntroducedLabelExponentCertificates` at `(C.point p - 1,J+1)`.

## Lean Targets

```text
aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds
aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds
```

## Kill Conditions

- Keep actual-width compatibility explicit.
- Keep the label bounds supplied; do not derive them from Definition 3.
- Do not infer terminal-exponent equality from introduced-label membership.
- Do not infer least-value data from introduced-label membership.
- Do not infer all branches, displayed-vector construction, chart production,
  terminality, Lemma 5 order count, normal crossings, or RLCT extraction.
