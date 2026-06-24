# Review - A4 selected-entry Schur transition cocycle

Date: 2026-06-24.

Reviewer: `Sagan the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the finite selected-entry Schur transition cocycle slice:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-selected-entry-schur-transition-cocycle-a4.md`.

The review checked theorem strength, denominator hypotheses, Case 2
source/middle/target pivot memberships, residual-subtype target indexing, and
whether the statements overclaim source production or analytic transition data.

## Findings

No blocking findings.

The reviewer confirmed that the generic theorem
`selectedEntryNormalizedMap_schurComplement_transition_cocycle` assumes only
normalized source coordinates `x_q != 0` and `x_r != 0`, then proves target
Schur-entry equality via the normalized transition cocycle.  No `u*x`
denominator appears.

The Case 2 source-coordinate wrapper uses the source pivot membership for
source normalized coordinates, the middle pivot membership for the
middle-to-target normalization, and the target pivot membership for the target
normalized map.

The residual-subtype wrapper indexes `i` and `j` by the target residual-row and
residual-column subtype complements.  The chart-family wrapper is the intended
namespaced theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_cocycle
```

The statements match the reproduction note's scope: route-independence of the
target lower-right Schur entry, not source production, raw residual-function
equality, analytic transition regularity, coverage, normal crossings, pole
order, RLCT, or printed-vector repair.

## Gates

Controller ran and passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full `DLNFibre` build completed successfully with pre-existing Core/style
warnings outside this slice.

## Minimal Repair

None required.
