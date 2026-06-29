# Statement Card - A2 Case 2 Passive Jacobian Product Bounded-Unit A.E. Handoff

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

## Lean Names

```text
exists_open_ae_restrict_of_eventually_nhds
exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
```

## Reproduction

```text
reproduction-a2-case2-passive-jacobian-product-bounded-unit-ae-handoff.md
```

## Claim

For the concrete passive product-domain measure
`passiveMeasure.prod weightedBox`, the retained-passive solved-`A1` product
raw-order Jacobian density is a.e. bounded above and below by positive
constants after restricting to a sufficiently small open neighborhood of any
determinant-chart basepoint.

## Role

This packages the passive Jacobian factor as a local bounded unit on the
measure domain that will be used in later passive source-measure comparisons.

## Proved

There exist `epsilon > 0`, `K > 0`, and an open set `U` with `z0 in U` such
that, for a.e. `z` with respect to `sourceMeasure.restrict U`,

```text
epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K.
```

## Assumed

Continuity of the passive fields, basepoint determinant-unit hypotheses for
`Ctop z0.1` and `A1passive z0.1`, and the measurable/open-measurable structure
needed to restrict the concrete passive product-domain measure.

## Cited

None.

## Deferred

Determinant-chart Haar transport, raw/source Haar transport,
external/original source-prior comparison, positive-mass/support assertions,
selected-entry image coverage, source-rank coverage, local inverse/coverage,
normal crossings, pole order, and RLCT extraction.

## Status

Proved in Lean and reviewed.  Focused build, `git diff --check`,
`scripts/sorries`, and direct axiom probes passed.
