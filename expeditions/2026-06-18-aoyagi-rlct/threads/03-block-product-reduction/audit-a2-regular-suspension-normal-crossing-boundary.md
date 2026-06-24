# Audit - A2 regular-suspension normal-crossing boundary

Date: 2026-06-24.

Status: construction not Lean-ready.

Review basis: controller inspection and xhigh scout `Locke the 3rd`.

## Source Observation

PDF p. 13 finishes the Theorem 3 block reduction and displays

```text
P1 ( prod_s A^(s) - [Er 0; 0 0] ) P2
  =
[ C1 - Er      -F2
  -F3      prod_s C^(s) - F3 F2 ].
```

Immediately after that display, the paper writes the RLCT decomposition

```text
lambda( prod_s A^(s) - prod_s A*^(s) )
  =
(-r^2 + r(H^(1)+H^(L+1))) / 2
  + lambda( prod_s C^(s) ).
```

PDF p. 14 then invokes Theorem 4 to reduce to `r^(s)=r` and starts the
recursive blow-up analysis for `||prod_s C^(s)||^2`.

The pages do not spell out a normal-crossing chart construction for the p. 13
regular-coordinate suspension.  Under the expedition citation boundary, that
decomposition cannot be imported as regular-coordinate additivity or ideal
RLCT invariance.

## Current Source-Side Data

The strongest current source-side object is

```text
PaperEndpointFixedBaseRegularCoordinateSourceData
```

It packages:

- a fixed-base canonical local source certificate;
- the source-shaped-rank-stratum guarded regular/residual ideal split;
- centered continuous scalar regular coordinates for `S.Ctop - 1`, `-S.B`,
  and `lowerLeftBlock S.L`;
- the dimension convention and the cardinality equality with
  `aoyagiTheorem2RegularVariableCount N H r`.

This is source-moving finite/topological data, but it does not state that the
scalar regular-coordinate functions form an analytic coordinate chart.

## Current Normal-Crossing Certificate Shape

Lean's `AoyagiNormalCrossingChartCertificate` records a supplied finite
normal-crossing chart family:

```text
ChartPoint, chartMap, coord,
loss, jacobianPrior,
lossUnit, jacobianPriorUnit,
lossExp, jacobianPriorExp,
monomial identities, unit hypotheses.
```

It is intentionally a certificate spine.  It does not encode analytic chart
coverage, properness, local coordinate invertibility, analytic ideal/germ
transport, or regular-coordinate additivity.  Those facts enter only through
an explicit extraction hypothesis for an actual full certificate `Cfull`.

The finite transformer

```text
jacobianPriorLossShift
```

shifts exponent arrays on an already supplied certificate.  It does not build
the regular-suspension chart whose analytic effect would justify that shift.

## Decision

Do not add a theorem of the form

```text
PaperEndpointFixedBaseRegularCoordinateSourceData -> exists Cfull, ...
```

The current APIs and source reproductions do not support it.

Do not add a source-anchored regular-suspension boundary whose analytic fields
are empty, `True`, or merely renamed arbitrary predicates.  That would hide the
remaining work under better names.

A source-anchored boundary can become Lean-worthy only after its open fields
are concrete enough to state what has to be proved:

- which full product-difference loss/generator family is represented by
  `Cfull`;
- which reduced residual loss/generator family is represented by `Cred`;
- how the regular scalar functions become analytic coordinates;
- what coverage statement relates the source-stratum neighborhood to the full
  chart family;
- what Jacobian/prior identity computes the regular-variable exponent shift;
- why extraction is applied to `Cfull`, not to a synthetic shifted certificate.

## Next Reproduction Target

Before any construction theorem, reproduce the p. 13 regular-suspension chart
argument independently:

1. identify the actual full generator/loss after product reduction;
2. identify the reduced residual generator/loss controlled by `Cred`;
3. prove the scalar entries `Ctop - 1`, `F2`, and `F3` are genuine local
   regular coordinates, not only centered continuous functions;
4. construct the full normal-crossing chart family from a reduced certificate;
5. compute the Jacobian/prior exponent shift by the regular-coordinate count;
6. prove coverage and unit/nonvanishing conditions;
7. apply the normal-crossing extraction citation only to the constructed
   full certificate.

## Kill Conditions

- Treating algebraic ideal equality as RLCT equality.
- Using `Cred.jacobianPriorLossShift m` as the actual full chart without
  proving it represents the product-difference loss.
- Claiming centered continuous scalar functions are regular coordinates.
- Setting analytic transport, coverage, or Jacobian compatibility fields to
  `True`.
- Hiding Aoyagi Lemma 1, Theorem 4, or regular-coordinate additivity under a
  new predicate name.
- Ignoring that current source neighborhoods are source-stratum guarded and do
  not prove exact-rank openness.
