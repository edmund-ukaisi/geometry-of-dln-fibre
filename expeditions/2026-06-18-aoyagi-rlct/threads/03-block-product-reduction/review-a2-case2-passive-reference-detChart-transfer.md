# Review - A2 Case 2 passive-reference determinant-chart transfer

Date: 2026-07-01.

Status: controller review PASS; independent xhigh `Kierkegaard` PASS after
the statement-card wording was narrowed from finite-scalar domination to
scalar domination.

## Checks

- The theorem assumes, rather than constructs, the passive reference
  determinant-chart comparison.
- The passive-field domination is on the left factor:

```text
passiveMeasure <= d • passiveReferenceMeasure.
```

- Both product sources use the same selected-entry `weightedBox`; no marginal
  equality or product-source equality is claimed.
- The scalar in the conclusion is `d * c`, matching first domination by the
  passive reference and then the reference determinant-chart comparison.
- The target is still `rawReference.restrict rawDetChart`, not raw-order Haar
  and not a source-image measure.
- The result works for a general raw reference measure; when the future
  reference is additive Haar, the theorem can be instantiated with that
  measure, but Haar invariance is not used here.

## Boundary

This is measure bookkeeping for a future concrete passive reference.  It does
not remove the need to prove that reference's determinant-chart domination,
and it does not establish passive-product Haar transport or any
normal-crossing/RLCT result.
