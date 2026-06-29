# Review - A2 Case 2 Passive Jacobian Product Bounded Unit

Date: 2026-06-29.

Reviewer: Leibniz the 3rd, xhigh.

Verdict: PASS.

## Scope Checked

Lean theorem target:

```text
exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive
```

## Findings

No findings.

The theorem assumes continuity of the passive fields
`A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`; it assumes determinant-unit
hypotheses only at the base parameter `z0.1`; and it concludes only local
positive lower and upper bounds for

```text
retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z).
```

The proof establishes continuity of the transported topology-tuple map `Y`,
checks that `Y z0` lies in the retained-passive determinant chart using the
basepoint determinant units, and then applies the generic composed bounded-unit
lemma.

## Boundary

This is passive retained-coordinate Jacobian-unit bookkeeping.  It does not
prove determinant-chart Haar transport, raw/source Haar transport,
external/original source-prior comparison, selected-entry image coverage,
source-rank coverage, local inverse/coverage, normal crossings, pole order, or
RLCT.

## Gates

Reviewer verification passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Controller final gates passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
git diff --check
scripts/sorries
```

`scripts/sorries` reports `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the theorem reports only
`[propext, Classical.choice, Quot.sound]`.
