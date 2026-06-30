# Review - A2 selected-entry all-pivot Jacobian/volume data

Date: 2026-06-29.

## Verdict

PASS.  No required changes.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotJacobianVolumeData.lean
lean/DLNFibre.lean
```

Artifacts:

```text
reproduction-a2-selected-entry-all-pivot-jacobian-volume-data.md
statement-card-a2-selected-entry-all-pivot-jacobian-volume-data.md
```

## Source/Scope Review

Reviewer: Arendt the 4th, xhigh.

Verdict: PASS.  No source/scope fidelity findings.

The reviewer accepted the slice as a chart-by-chart lift of the one-pivot
selected-entry pushforward to the shared all-pivot universal-domain context.
The source boundary is correct: Aoyagi PDF pp. 15-22 support the chosen-pivot
substitution and Jacobian density, while the finite all-pivot family is
expedition-built bookkeeping over the pivots.

The module docstring and docs correctly exclude transition regularity, source
production, branch termination, source-prior/Haar transport, full atlas
production, normal crossings, pole order, and RLCT.  The public predicate
wrapper is only the forgetful
`SelectedEntryAnalyticJacobianVolumeCompatible` wrapper for the same
Jacobian/volume data.

## Lean/API Review

Reviewer: Mendel the 4th, xhigh.

Verdict: PASS.  No concrete findings.

The reviewer checked that the data record uses the shared all-pivot context

```text
selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
```

and that each chart `c` delegates to the one-pivot result at
`chartEquiv c`.  The chart target, nonempty-target witness, nonzero restricted
source measure, and pushforward equality are exactly the one-pivot
chart-point product-measure facts transported through the all-pivot context
fields.

The wrapper

```text
selectedEntryAllPivotAnalyticJacobianVolumeCompatible
```

stays scoped to Jacobian/volume compatibility and does not claim a full
supplied analytic atlas producer.  The aggregator import in `lean/DLNFibre.lean`
includes the new module after its visible dependencies.

Mendel independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotJacobianVolumeData.lean
lake env lean DLNFibre.lean
lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotJacobianVolumeData
lake build DLNFibre
```

The checks passed.

## Controller Verification

Controller local checks before review:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotJacobianVolumeData
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotJacobianVolumeData.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The focused build, warning-level direct Lean check, full local `DLNFibre`
build, zero-sorry scan, and whitespace check passed.  The direct axiom probe
for both new declarations reported only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No transition regularity between distinct selected-entry pivots, source
production, branch termination, source-prior transport, determinant-chart Haar
transport, full supplied analytic atlas producer, normal-crossing extraction,
pole order, or RLCT is proved.
