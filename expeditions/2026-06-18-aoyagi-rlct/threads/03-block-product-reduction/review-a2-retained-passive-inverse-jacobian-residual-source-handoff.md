# Review - A2 retained-passive inverse-Jacobian residual-source handoff

Reviewer: Ampere, xhigh read-only review.

## Verdict

PASS.

## Checks

- The measure direction is correct: the direct determinant-chart measure is
  identified with the raw-order source-chart inverse-Jacobian measure, and the
  support lemma then rewrites `mu.restrict localSource` to `mu`.
- `residualSourceHypotheses_of_measure_map` is applied with
  `chart := directChart` and `nu := m.restrict S`, so the chart-side residual
  hypotheses match the theorem inputs.
- Local-source support is justified from the raw-order source chart
  realization on `T`, then transported to the weighted measure using
  `withDensity` absolute continuity in the right direction.
- Source-side positive-set measurability remains an explicit hypothesis.
- The notes do not claim chart-side residual positivity, finite residual
  integral, selected-entry integrability, source-rank coverage, original
  external source-prior transport, normal crossings, pole order, or RLCT.

## Read-Only Hygiene

The reviewer independently checked `git diff --check` and confirmed the
touched Lean file has no `sorry`, `admit`, `axiom`, `#exit`, or
`native_decide` markers.  The controller ran the Lean build and axiom probes
separately.
