# Review - A2 Case 2 passive-source raw-Haar inverse-Jacobian domination

Date: 2026-07-01.

Status: controller review PASS; xhigh scout `Popper the 3rd` independently
confirmed the conditional socket boundary.

## Checks

- Statement keeps the determinant-chart domination as an explicit hypothesis.
  It does not manufacture Haar transport from arbitrary `passiveMeasure`.
- The right-hand side uses
  `topologyTupleEdgeRawOrderInverseJacobianDensity`, so the phrase
  "inverse-Jacobian" is literal here and is distinct from the earlier
  source-side retained-passive formal product readback density.
- The proof route is measure-theoretic:

```text
Measure.map Y mu <= c • detHaar
```

is pushed through `topologyTupleEdgeRawOrder`, and the reference pushforward is
rewritten by the retained-passive raw-order change-of-variables theorem.

- The scalar remains `c`; no additional normalization or determinant product
  factor is inserted.

## Boundary

The theorem is a socket, not the missing source theorem.  The next substantive
mathematical task is to decide when

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart
```

can be proved from a concrete passive-source measure construction.  With an
arbitrary passive measure, such domination is false in general.
