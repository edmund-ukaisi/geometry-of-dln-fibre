# Review - A2 selected-entry all-pivot regular data

Date: 2026-06-29.

## Verdict

PASS.  No required changes.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotRegularData.lean
lean/DLNFibre.lean
```

Artifacts:

```text
reproduction-a2-selected-entry-all-pivot-regular-data.md
statement-card-a2-selected-entry-all-pivot-regular-data.md
```

## Source/Scope Review

Reviewer: Maxwell the 4th, xhigh.

Verdict: PASS.

The reviewer accepted the scope as all-pivot selected-entry bookkeeping
obtained by varying the already reproduced one-pivot chart calculation
`x_p = u`, `x_i = u r_i` over all finite selected pivots.  The source boundary
is correct: Aoyagi supplies the displayed selected-entry substitution on PDF
pp. 15-22, while the all-pivot family is expedition-built finite coordinate
data for the formal certificate, not an Aoyagi-printed analytic atlas theorem.

The accepted nonclaim boundary is: no transition regularity, Jacobian/volume
compatibility, source production, termination, normal crossings, pole order,
RLCT, source-prior transport, or determinant-chart Haar transport.

## Lean/API Review

Reviewer: Sartre the 4th, xhigh.

Verdict: PASS.

The reviewer checked that both data records use the shared all-pivot context

```text
selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
```

and that the predicate wrappers witness this shared context rather than the
one-chart context.  The all-pivot family is non-vacuous by inspection:
`numCharts = center.card`, `hcenter` supplies a nonempty finite center, and the
context uses universal source/chart domains.

The implementation delegates each chart `c` to the one-pivot facts at
`chartEquiv c`:

```text
continuous_formalChartMap
continuous_chartPointCoord
continuous_chartPointLossUnit
continuous_chartPointJacobianPriorUnit
lossUnit_isUnit
jacobianPriorUnit_isUnit
```

No `sorry`, `admit`, `axiom`, or `unsafe` was found in the new module.  The
aggregator import in `lean/DLNFibre.lean` includes the new module after its
visible dependencies.

## Verification

Controller verification before review:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotRegularData
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotRegularData.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The focused build, direct Lean check, and full `DLNFibre` build passed.  The
direct axiom probe for the four new declarations reported only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No transition regularity, Jacobian/volume compatibility, source production,
branch termination, normal-crossing extraction, pole order, RLCT,
source-prior transport, or determinant-chart Haar transport is proved.
