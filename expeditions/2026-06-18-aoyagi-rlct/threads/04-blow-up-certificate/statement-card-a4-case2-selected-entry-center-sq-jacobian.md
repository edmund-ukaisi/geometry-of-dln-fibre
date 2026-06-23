# Statement card - A4 Case 2 selected-entry center square and formal Jacobian

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `selectedEntryCenterSq`
- `selectedEntryCenterSq_selectedEntryChartMap`
- `selectedEntryPivotFirstJacobian`
- `selectedEntryPivotFirstJacobian_det`
- `SelectedEntryChartFamilyData.centerSq_chartMap`
- `case2DisplayedSourceChartMap_centerSq`
- `case2DisplayedSourceChartMap_pivotFirstJacobian_det`
- `case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one`

## Claim

For a finite selected-entry center, the square-sum of the transformed center
generators factors as `u^2` times the normalized square-sum.  For the displayed
Aoyagi Case 2 pivot, the same identity specializes to
`case2DisplayedSourceChartMap`.

The formal pivot-first finite Jacobian matrix of the selected-entry coordinate
change has determinant `u` to the number of non-pivot center coordinates.  In
the displayed Case 2 center this exponent is
`card(case2ResidualBlockPivotEntries n S J) - 1`.

## Inputs Kept Explicit

- a finite center and selected pivot membership;
- for the displayed Case 2 specialization, `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- the selected variable `u` and residual coordinates.

## Proved

```text
selectedEntryCenterSq center (selectedEntryChartMap pivot u residual)
  = u^2 * (1 + selectedEntryCenterSq (center.erase pivot) residual)
```

and

```text
det [ 1 0; residual uI ] = u^(number of non-pivot coordinates).
```

The displayed Case 2 wrappers instantiate these facts for the residual-block
center and the displayed pivot `(J+1,J+1)`.

## Not Proved

No analytic unit nonvanishing, no real chart neighbourhood, no differentiable
Jacobian theorem, no chart coverage, no transition regularity, no A0
normal-crossing chart certificate, no pole order, and no RLCT extraction.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

## Review

Xhigh source/math reviewer `Chandrasekhar the 2nd` passed the slice and
confirmed source fidelity to Aoyagi p. 5 and pp. 19-21.  Xhigh Lean/API
reviewer `Dewey the 2nd` passed the slice; the only watchpoint is that the
informal phrase "loss exponent `1`" must remain tied to the supplied A0
certificate convention and not be read as analytic chart production.

Durable review artifact:
`review-case2-selected-entry-center-sq-jacobian-a4.md`.
