# Review - A2 product-step full formal Jacobian formulas

Date: 2026-06-26.

Reviewers: xhigh read-only reviewers `Tesla` and `Chandrasekhar`.

## Verdict

Pass for the formula-and-reorder checkpoint.  The formulas are source-faithful
for the full p. 13 one-step formal tangent map, and the determinant-order issue
is correctly exposed rather than hidden.

## Formula Check

Reviewer `Tesla` independently reproduced the full forward tangent at raw base
point `(C1,D,F3old,A1,A2,A3,A4)`, with `Q=C1*A1`, as:

```text
dCtop = dC1*A1 + C1*dA1
dD    = dD
dA1   = dA1
dA3   = dA3
dF2   = A1^-1*dA1*A1^-1*A2 - A1^-1*dA2
dF3   = dF3old
        - dD*A3*Q^-1
        - D*dA3*Q^-1
        + D*A3*Q^-1*dCtop*Q^-1
dC    = dA4
        - dA3*A1^-1*A2
        + A3*A1^-1*dA1*A1^-1*A2
        - A3*A1^-1*dA2.
```

The inverse tangent at chart base point `(Q,D,A1,A3,F2,F3,C)` was reproduced
as:

```text
dC1    = eQ*A1^-1 - Q*A1^-1*eA1*A1^-1
dD     = eD
dF3old = eF3
         + eD*A3*Q^-1
         + D*eA3*Q^-1
         - D*A3*Q^-1*eQ*Q^-1
dA1    = eA1
dA2    = -eA1*F2 - A1*eF2
dA3    = eA3
dA4    = eC - eA3*F2 - A3*eF2.
```

Signs were checked: the `dF3` inverse-variation term is positive, while the
`dD` and `dA3` terms are negative.

## Lean/API Check

Reviewer `Chandrasekhar` confirmed that the full tangent types should use the
existing `TopologyTuple` abbreviations:

```text
ProductReductionStepRawCoordinates.TopologyTuple
ProductReductionStepChartCoordinates.TopologyTuple
```

The raw order is `(C1,D,F3,A1,A2,A3,A4)` and the chart order is
`(Ctop,D,A1,A3,F2,F3,C)`.  Therefore a determinant theorem must use an explicit
chart-to-raw-order permutation:

```text
(Ctop,D,A1,A3,F2,F3,C) -> (Ctop,D,F3,A1,F2,A3,C).
```

The landed `productReductionStepChartTangentRawOrderEquiv` is exactly this
bookkeeping layer.

## Scope Check

This checkpoint deliberately records formulas and reorder plumbing only.  It
does not claim the bundled full `LinearMap`, the full `LinearEquiv`, determinant
unitness, analytic differentiability, source-measure pushforward, density
transport, normal crossings, pole order, or RLCT.
