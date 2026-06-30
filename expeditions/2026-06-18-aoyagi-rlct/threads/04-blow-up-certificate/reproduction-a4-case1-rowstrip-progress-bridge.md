# Reproduction - A4 Case 1(2) row-strip progress bridge

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can Case 1 feed the introduced-label support-growth progress relation?

Answer: only Case 1(2), and only through its row-strip continuation payload.
Case 1(1) is a same-domain selected-old lowering step and is invisible to the
current introduced-label support-growth measure.

## Source Situation

Aoyagi PDF p. 15 starts Case 1 with a first jump

```text
b_(J+1) = ... = b_(J+J1)
```

and chooses an old variable `u_(s,k)` whose old level is `J+J1`.

On PDF p. 16, Case 1(1) uses that old variable as denominator and lowers the
selected old variable level to `J`.  The branch stays on the same introduced
label domain `(S,J)`.  Its progress is Aoyagi's separate count: the number of
old variables with `tilde t = J+J1` decreases by one.

On PDF pp. 16-18, Case 1(2) factors

```text
u_(s,k) = u_(S,J+1) * u'_(s,k)
```

and introduces the fresh label `(S,J+1)`.  Under the continuation bound

```text
J+1 <= M(S+1),
```

the inductive statement proceeds with `J` increased by one.

## Finite Progress Calculation

The Lean payload

```text
Case1DisplayedRowStripJIncrementPayload
```

already records the finite consequences needed for the progress kernel:

```text
actualWidthLabel L n S (J+1)
introducedLabelFinset L n S (J+1)
  = insert (S,J+1) (introducedLabelFinset L n S J)
```

The actual-width label supplies:

```text
1 <= S,  S <= L,  J+1 <= n(S+1).
```

The generic same-stage progress lemma then gives

```text
progressStep L n (S,J+1) (S,J).
```

## Nonclaims

This does not cover Case 1(1), does not construct the Case 1(2) chart or
post-state, does not prove a full Case 1 transition invariant, and does not
prove source production, branch termination, normal crossings, pole order, or
RLCT.
