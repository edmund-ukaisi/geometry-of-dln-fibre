# Reproduction - Normal-crossing Jacobian-prior loss shift

Date: 2026-06-23.

Status: A0 finite exponent-array arithmetic.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the normal-crossing finite formula: for a coordinate
with loss exponent `k > 0` and Jacobian/prior exponent `h`, the active ratio is

```text
(h + 1) / (2*k).
```

Aoyagi PDF p. 13 motivates the later use after Theorem 3.  The regular block
variables have count

```text
c = r^2 + r(H^(L+1)-r) + r(H^(1)-r)
  = -r^2 + r(H^(1) + H^(L+1)),
```

and Aoyagi writes the contribution as `c/2` added to the reduced-product
coefficient.

This slice does not prove that analytic regular variables produce this shift.
It proves only the finite exponent-array calculation that would be used after
a full normal-crossing certificate supplies the shifted Jacobian/prior
exponents.

## Finite Operation

For supplied finite exponent data `D`, define `D.jacobianPriorLossShift m` by
leaving the chart set, coordinate set, and loss exponents unchanged, and
replacing

```text
h(c,j)  by  h(c,j) + m*k(c,j).
```

The active coordinates are unchanged because they depend only on `k(c,j) > 0`.

## Ratio Calculation

For an active coordinate, write `k = D.lossExp c j` and
`h = D.jacobianPriorExp c j`.  Since `k > 0`, rational division by `k` is valid.
The shifted ratio is

```text
(h + m*k + 1) / (2*k)
  = ((h + 1) + m*k) / (2*k)
  = (h + 1) / (2*k) + (m*k) / (2*k)
  = (h + 1) / (2*k) + m/2.
```

The Lean theorem is restricted to `p in D.activePairs`; without this
hypothesis `ratioAt` is totalized at `k = 0`, and the displayed cancellation is
not valid.

## Minimum Calculation

Let `q = D.exponentMinimum`, and choose an active pair `p` with
`D.ratioAt p = q`.  For every shifted active pair `p'`, the same pair is active
in `D`, hence

```text
D.ratioAt p' >= q.
```

Adding `m/2` gives

```text
(D.jacobianPriorLossShift m).ratioAt p'
  = D.ratioAt p' + m/2
  >= q + m/2.
```

The original minimizing pair has shifted ratio `q + m/2`, so the shifted
minimum is exactly

```text
(D.jacobianPriorLossShift m).exponentMinimum
  = D.exponentMinimum + m/2.
```

## Chart Counts

For a chart `c`, a coordinate is counted at the shifted ratio `q + m/2` exactly
when it was counted at ratio `q` before the shift:

```text
j in (D.jacobianPriorLossShift m).coordsInChartAtRatio (q + m/2) c
  iff 0 < k(c,j) and D.ratioAt (c,j) + m/2 = q + m/2
  iff 0 < k(c,j) and D.ratioAt (c,j) = q
  iff j in D.coordsInChartAtRatio q c.
```

Taking `q = D.exponentMinimum` and using the shifted-minimum calculation shows
that `minCoordsInChart` and `minCountInChart` are preserved.  Since every
chartwise minimum count is preserved, the finite maximum `exponentOrder` is
also preserved.

## Lean Names

```text
AoyagiNormalCrossingExponentData.jacobianPriorLossShift
AoyagiNormalCrossingExponentData.jacobianPriorLossShift_lossExp
AoyagiNormalCrossingExponentData.jacobianPriorLossShift_jacobianPriorExp
AoyagiNormalCrossingExponentData.activePairs_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.mem_activePairs_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.ratioAt_jacobianPriorLossShift_of_mem_activePairs
AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.coordsInChartAtRatio_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.countInChartAtRatio_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.minCoordsInChart_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.minCountInChart_jacobianPriorLossShift
AoyagiNormalCrossingExponentData.exponentOrder_jacobianPriorLossShift
```

## Nonclaims

This does not construct charts, regular coordinates, chart coverage, analytic
Jacobians, volume-form transformations, normal crossings, pole order, RLCT
additivity, or the full post-Theorem-3 regular-suspension certificate.

## Kill Conditions

- The theorem must remain active-coordinate guarded.
- The shift parameter `m` is a finite exponent-array parameter.  In the
  Theorem 3 application it should be supplied as the nonnegative count
  `r^2 + r(H^(L+1)-r) + r(H^(1)-r)`, with any rewrite to
  `-r^2 + r(H^(1)+H^(L+1))` proved separately under dimension hypotheses.
- This finite shift cannot be used to apply the A0 extraction theorem to a
  reduced certificate and then add `m/2`; the single extraction citation must
  still apply to the final full certificate.
