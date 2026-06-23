# Statement card - A4/A0 Case 1 exponent-coordinate bridge

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `Case1SelectedEntryExponentCoordinateBridge`
- `Case1SelectedEntryExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two`
- `Case1SelectedEntryExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le`
- `Case1SelectedEntryA0ExponentCoordinateBridge`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.of_coord_exponents`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`

## Claim

If a supplied coordinate `p` of finite normal-crossing exponent data has loss
exponent `1` and Jacobian/prior exponent equal to the Case 1 selected-entry
non-pivot count

```text
J1 * (n (S + 1) - J),
```

then `p` is active and its finite ratio is

```text
(1 + J1 * (n (S + 1) - J)) / 2.
```

With an explicit lower bound saying this candidate ratio is at most every
active ratio in the supplied data, it is the supplied data's finite exponent
minimum.

## Inputs Kept Explicit

- a supplied `D : AoyagiNormalCrossingExponentData`;
- a supplied coordinate `p : Fin D.numCharts x Fin D.numCoords`;
- the exponent equalities `D.lossExp p = 1` and
  `D.jacobianPriorExp p = J1 * (n(S+1)-J)`;
- for the selected-old source-moving wrapper, a supplied
  `Case1SelectedOldUnitSuppliedChartFamilyBoundary`.

## Proved

The bridge returns:

```text
p in D.activePairs
```

and

```text
D.ratioAt p = (1 + J1 * (n (S + 1) - J)) / 2.
```

The minimum wrapper proves the corresponding finite `D.exponentMinimum`
equality when all active coordinates are lower-bounded by this ratio.

## Not Proved

No construction of `D`, no construction of the coordinate `p`, no production
of a normal-crossing chart certificate from the selected-old boundary, no
global lower bound, no chart count, no exponent-order statement, no analytic
Jacobian or volume-form theorem, no chart coverage or transition regularity,
no pole order, and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused build, full build, no-sorry audit, and diff hygiene gate passed.
The full build emitted only unrelated pre-existing Core linter warnings.

## Review

Xhigh source/math and Lean/API review passed with no findings.  See
`review-case1-a0-exponent-coordinate-bridge-a4.md`.
