# Review - A2 Case 2 Passive Jacobian Product Bounded-Unit A.E. Handoff

Date: 2026-06-29.

Reviewer: Heisenberg the 3rd, xhigh, read-only.

Verdict: PASS.

## Scope Checked

Lean targets:

```text
exists_open_ae_restrict_of_eventually_nhds
exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
```

## Findings

No findings.

The generic helper is exactly the basic handoff from a property holding
eventually in `nhds x0` to the same property holding a.e. after restricting any
measure to a small open neighborhood of `x0`.  It asserts only openness,
membership of the basepoint, and the a.e. restricted property.

The Case 2 theorem derives the eventual two-sided bounds from the previously
banked passive Jacobian bounded-unit theorem, then applies the generic helper
to `sourceMeasure = passiveMeasure.prod weightedBox`.  Its conclusion is
limited to positive constants, an open neighborhood containing `z0`, and a.e.
two-sided bounds under `sourceMeasure.restrict U`.

## Boundary

No source-prior transport, determinant-chart Haar transport, raw/source Haar
transport, source-image coverage, source-rank coverage, local inverse/coverage,
positive-mass/support assertion, normal-crossing statement, pole-order claim,
or RLCT claim is introduced.

## Gates

Focused build passed in controller context:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

Controller final gates passed:

```text
git diff --check
scripts/sorries
```

`scripts/sorries` reports `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probes for both Lean targets report only
`[propext, Classical.choice, Quot.sound]`.
