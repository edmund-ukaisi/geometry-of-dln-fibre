# Reproduction - Lemma 5 Supplied Exponent-Domain Extension

Status: checked supplied-certificate/API wrapper.

This note records the safe boundary for adding Eq3, Eq4, and Eq5 branch labels
to the exponent-certificate domain.  It does not compute terminal exponents or
least values.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, displays branch labels:

- Eq4 lower endpoint: `k = Htilde_p + 1`.
- Eq3 upper endpoint: `k = Htilde'_1 + 1`.
- Eq5 strict offset: `k = Htilde'_p + 1 - alpha`.

The existing Lean source-label wrappers prove that, under their explicit
guards, these labels are actual source labels at the branch's own source
coordinate.  For a current-layer advance from `(S,J)` to `(S,J+1)`, actual
source-label validity gives:

```text
introducedLabel L n S (J+1) S (J+1).
```

This is only the `introduced` field of a `LabelExponentCertificate`.

## Reproduction

Fix one supplied branch whose label identity says `k=J+1`.  The corresponding
source-label wrapper gives:

```text
actualWidthLabel L n S (J+1).
```

Since the label is at the current source stage and `J+1 <= J+1`, the generic
constructor gives:

```text
introducedLabel L n S (J+1) S (J+1).
```

To build the new label's full exponent certificate, two additional facts must
be supplied:

```text
terminalExponent L (widthZ n) (t' S (J+1)) = numerator' S (J+1)

IsLeast {v | exists i in Icc 1 L, t' S (J+1) i = v}
  (leastValue' S (J+1)).
```

Together these form:

```text
LabelExponentCertificate L n S (J+1) S (J+1)
  (t' S (J+1)) (numerator' S (J+1)) (leastValue' S (J+1)).
```

Assume the old introduced labels preserve vector, numerator, and least-value
data from `t,numerator,leastValue` to `t',numerator',leastValue'`.  The generic
domain-extension theorem then gives:

```text
IntroducedLabelExponentCertificates L n S (J+1)
  t' numerator' leastValue'.
```

The Eq3 wrapper keeps the one-unit slack explicit.  The Eq5 wrapper keeps the
own-block actual-width lower bound explicit.

## Lean Targets

```text
aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound
```

## Kill Conditions

- Do not infer terminal-exponent equality from introduced-label membership.
- Do not infer least-value data from introduced-label membership.
- Keep Eq3 slack and Eq5 actual-width lower bound explicit.
- Do not infer all branches, displayed-vector construction, chart production,
  terminality, Lemma 5 order count, normal crossings, or RLCT extraction.
