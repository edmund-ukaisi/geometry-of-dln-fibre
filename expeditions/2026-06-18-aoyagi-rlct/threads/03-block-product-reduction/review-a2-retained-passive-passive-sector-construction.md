# Review - A2 retained-passive passive-sector construction frontier

Date: 2026-06-30.

Status: PASS after wording repairs.

## Scope For Review

- `threads/03-block-product-reduction/reproduction-a2-retained-passive-passive-sector-construction.md`
- `threads/03-block-product-reduction/statement-card-a2-retained-passive-passive-sector-construction.md`
- Existing Lean frontier in:
  - `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`
  - `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean`
  - `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`

## Source/Frontier Review

Reviewer: `Raman`.

Verdict: findings, repaired.

The reviewer confirmed the core premise: the reduced selected-entry chart has
domain only `center -> R`, while `Sdet` is the full
`topologyTupleDetChartSet`, and the live theorem still assumes

```text
m.restrict Sdet = Measure.map chart weightedBox.
```

Thus the next target should be a full passive-sector exact pushforward or
finite-scalar/bounded-density domination theorem, not the old reduced-chart
equality.

The reviewer found two wording issues:

1. Bare mutual absolute continuity is too weak for the finite-integral
   handoff.  It transfers a.e. positivity, but not finiteness of an unbounded
   negative-power integral.  The note and statement card now require exact
   equality or finite-scalar/bounded-density domination in the direction
   needed by the local finite-integral consumer.
2. The passive-coordinate list omitted `A3passive`.  The note and statement
   card now list the existing Lean passive datum fields explicitly:
   `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.

## Nonclaim Boundary

This review concerns a construction frontier note only.  No Lean theorem,
original source prior, source-rank coverage, determinant-chart Haar transport
from the reduced selected-entry section, normal crossings, pole order, or RLCT
is claimed.
