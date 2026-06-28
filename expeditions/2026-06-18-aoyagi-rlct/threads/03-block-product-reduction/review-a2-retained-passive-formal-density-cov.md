# Review - A2 retained-passive formal-density change of variables

Reviewer: `Volta the 2nd`, xhigh read-only reviewer.

Verdict: PASS.

Scope:

- `retainedPassiveFormalRawOrderJacobianProductAbsDetAt`.
- `map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_posTail`.
- `map_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet_eq_restrict_rawSourceChart_zeroTail`.
- `map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_posTail`.
- `map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart_zeroTail`.
- The reproduction note, statement card, thread entry, and scope boundaries.

Findings:

- The a.e. density replacement is under `m.restrict S`, not global, using
  `hs : NullMeasurableSet S m` and `ae_restrict_mem₀ hs` before
  `withDensity_congr_ae`.
- Positive-tail statements use density parameter `M + 1` and invoke the
  positive-tail determinant theorem with parameter `M`; zero-tail statements
  use `M = 0`.
- The product density definition matches the prior formal determinant product
  formula.
- The reused measure theorem is the retained-passive raw-order
  change-of-variables theorem to
  `topologyTupleRawOrderSourceRecursiveDetChartSet`.
- The notes do not overclaim original-source prior transport, signed-box
  density identification, normal crossings, pole order, RLCT, or a single
  all-`M` theorem.

Checks reported by reviewer:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure: passed
scripts/lb DLNFibre: passed with unrelated warning noise
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check: passed
forbidden-marker search in touched Lean file: no hits
```
