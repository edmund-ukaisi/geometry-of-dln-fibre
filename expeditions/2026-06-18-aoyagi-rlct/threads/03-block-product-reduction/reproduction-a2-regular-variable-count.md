# Reproduction - A2 regular-variable count

Date: 2026-06-23.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13, after Theorem 3, isolates three regular block families:

```text
C1 - Er        size r x r
F2             size r x (H^(L+1)-r)
F3             size (H^(1)-r) x r
```

The paper records their contribution to the displayed lambda formula as

```text
(-r^2 + r(H^(1)+H^(L+1))) / 2.
```

This note checks only the elementary count behind that displayed term.  It
does not prove regular-suspension additivity.

## Calculation

The number of scalar entries in the three regular block families is

```text
c = r^2 + r(H^(L+1)-r) + (H^(1)-r)r.
```

Assuming the endpoint rank-width bounds `r <= H^(1)` and
`r <= H^(L+1)`, the natural subtractions are ordinary integer/rational
subtractions after coercion.  Therefore

```text
c
  = r^2 + rH^(L+1) - r^2 + rH^(1) - r^2
  = rH^(1) + rH^(L+1) - r^2
  = -r^2 + r(H^(1)+H^(L+1)).
```

Dividing by two gives Aoyagi's displayed regular term:

```text
c / 2 = (-r^2 + r(H^(1)+H^(L+1))) / 2.
```

The Lean formula layer already names the right-hand side as
`aoyagiTheorem2RegularTerm L H r`.  This slice adds the finite count
`aoyagiTheorem2RegularVariableCount L H r` and proves that half of this count
is the regular term under the endpoint rank-width bounds.

The normal-crossing finite exponent layer already has the operation

```text
jacobianPriorLossShift c.
```

Applying it with `c = aoyagiTheorem2RegularVariableCount L H r` gives the
finite arithmetic expected from the regular-variable count:

```text
shiftedMinimum = reducedMinimum + aoyagiTheorem2RegularTerm L H r,
shiftedOrder   = reducedOrder.
```

Thus, if a reduced certificate has

```text
reducedMinimum + regularTerm = displayed Theorem 2 lambda
reducedOrder = displayed Theorem 2 order,
```

then the shifted finite exponent data satisfies the existing Theorem 2 finite
formula boundary.

## Nonclaims

- No proof that these coordinates form a regular-suspension chart.
- No analytic ideal transport.
- No Aoyagi Lemma 1.
- No regular-coordinate RLCT additivity theorem.
- No normal-crossing certificate production.
- No pole-order or RLCT conclusion.
