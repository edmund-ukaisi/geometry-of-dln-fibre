# Review - A2 Retained-Passive Solved A1 Zero Frechet Derivative

Date: 2026-06-27.

Reviewer: xhigh `Feynman`.

Verdict: PASS.

## Findings

The theorem boundary is sound.  The inverse-tail derivative is correctly
stated over upstream `TopologyTuple` coordinates with determinant-chart
hypothesis and right-hand side

```text
-(Tail^-1 * dTail * Tail^-1).
```

The zero solved-`A1` theorem has the correct sign and order:

```text
Tail^-1 * dCtop - Tail^-1 * dTail * Tail^-1 * Ctop.
```

This follows from `solvedA1(0) = Tail^-1 * Ctop` and the product rule.  The
correction term must remain in the displayed noncommutative order.

Using `data.Ctop` in the derivative-file statement is clean.  The coordinate
data copies `Ctop` from the nonredundant data, so this is equivalent to
`coord.Ctop` used in downstream Jacobian notation.

The hypotheses are scoped correctly:

```text
[Fintype rho] [DecidableEq rho] [forall j, Finite (kappa' j)]
hz : z in topologyTupleDetChartSet
```

No downstream `RetainedPassiveRawTopologyTuple`, raw-order formal determinant,
measure, normal-crossing, pole-order, or RLCT statement is introduced.
