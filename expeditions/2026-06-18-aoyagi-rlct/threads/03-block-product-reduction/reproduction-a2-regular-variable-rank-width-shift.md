# Reproduction - A2 regular-variable rank-width shift

Status: formalised and xhigh checked.

## Source Anchor

Aoyagi PDF p. 13 isolates the regular block-entry families

```text
C1 - Er,   F2,   F3
```

after the product-reduction step.  The finite count of these regular entries
has already been formalised as

```text
aoyagiTheorem2RegularVariableCount L H r
```

and the half-count identity has already been proved under the endpoint
rank-width bounds

```text
r <= H 1,     r <= H (L+1).
```

This note checks that the finite regular-variable shift should depend only on
the source-range rank-width hypothesis, not directly on the A2 source-rank
stratum.

## Input

Assume the usual source-range rank-width hypothesis used by Definition 3 and
the final Theorem 2 sockets:

```text
hr : forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

Then the two endpoint hypotheses needed by the regular-variable count are
immediate:

```text
hsource : r <= H 1       := hr 1     (1 <= 1)     (1 <= L+1),
htarget : r <= H (L+1)   := hr (L+1) (1 <= L+1)   (L+1 <= L+1).
```

The second lower-bound premise is automatic because `1 <= L+1`.

## Calculation

The existing finite theorem says:

```text
(D.jacobianPriorLossShift regularCount).exponentMinimum
  = D.exponentMinimum + aoyagiTheorem2RegularTerm L H r
```

provided `hsource` and `htarget` are supplied.  Substituting the two endpoint
projections from `hr` gives the rank-width version:

```text
(D.jacobianPriorLossShift regularCount).exponentMinimum
  = D.exponentMinimum + aoyagiTheorem2RegularTerm L H r.
```

The order theorem does not use rank-width:

```text
(D.jacobianPriorLossShift regularCount).exponentOrder
  = D.exponentOrder.
```

Therefore, if the reduced exponent data satisfies

```text
D.exponentMinimum + aoyagiTheorem2RegularTerm L H r
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,

D.exponentOrder = data.theorem2OrderFormula,
```

then the shifted exponent data satisfies the existing finite Theorem 2 formula
boundary.

The chart-certificate version is the same statement after projecting to
`Cnc.exponentData` and using the existing chart-certificate
`jacobianPriorLossShift` projection.

## Why This Improves the API

The source-rank stratum is one source of `hr`, but it is not mathematically
used by the regular-variable finite shift.  The finite shift needs only the
two endpoint inequalities, and the final socket already carries `hr` as its
rank-width provenance.  Moving the finite shift to an `hr`-based interface
prevents duplicated A2 hypotheses and makes the regular-shift socket reusable
for any future route that proves source-range rank-width without using the A2
source-rank stratum.

## Nonclaims

- No regular-suspension chart is constructed.
- No analytic ideal transport or Aoyagi Lemma 1 is proved.
- No exact-rank openness is proved.
- No normal-crossing chart certificate is produced.
- No active-ratio lower bound or chart-count theorem is proved.
- No pole-order or RLCT conclusion is obtained without the existing A0
  extraction boundary.
