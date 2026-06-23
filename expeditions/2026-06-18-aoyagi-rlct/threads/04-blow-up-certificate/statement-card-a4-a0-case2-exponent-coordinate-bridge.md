# Statement card - A4/A0 Case 2 exponent-coordinate bridge

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`
- `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`

Names:

- `AoyagiNormalCrossingExponentData.mem_activePairs_of_lossExp_eq_one`
- `AoyagiNormalCrossingExponentData.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq`
- `Case2DisplayedContinuingExponentCoordinateBridge`
- `Case2DisplayedContinuingExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two`
- `Case2DisplayedContinuingExponentCoordinateBridge.activePair`
- `Case2DisplayedContinuingExponentCoordinateBridge.ratioAt_eq_centerCard_div_two`
- `Case2DisplayedContinuingA0ExponentCoordinateBridge`
- `Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two`
- `Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair`
- `Case2DisplayedContinuingA0ExponentCoordinateBridge.ratioAt_eq_centerCard_div_two`

## Claim

If a supplied coordinate `p` of later A0 finite exponent data has loss
exponent `1` and Jacobian/prior exponent equal to the displayed Case 2 formal
pivot exponent, then `p` is active and its finite ratio is

```text
card(case2ResidualBlockPivotEntries n S J) / 2.
```

## Inputs Kept Explicit

- a supplied `D : AoyagiNormalCrossingExponentData`;
- a supplied coordinate `p : Fin D.numCharts × Fin D.numCoords`;
- a displayed continuing Case 2 local certificate;
- the bridge fields `D.lossExp p = 1` and
  `D.jacobianPriorExp p = erased-center cardinality`.

The generic bridge is named
`Case2DisplayedContinuingExponentCoordinateBridge`.  The A0-facing bridge is a
wrapper around it and should be used only when `D` is intended as later finite
exponent data for the full A0 normal-crossing problem.

## Proved

The bridge theorem returns:

```text
p ∈ D.activePairs
```

and

```text
D.ratioAt p =
  ((case2ResidualBlockPivotEntries n S J).card : Q) / 2.
```

## Not Proved

No construction of `D`, no construction of the coordinate `p`, no global
minimum statement, no exponent-order statement, no chart production, no
analytic chart certificate, no analytic Jacobian or volume-form theorem, no
analytic unit neighbourhood, no chart coverage, no transition regularity, no
final pole-order count, and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge
```

The focused builds passed through the shared-store `scripts/lb` workflow.

## Review

Xhigh source/math reviewer `Plato the 2nd` passed the slice with no findings.
Xhigh Lean/API reviewer `Franklin the 2nd` passed the API shape and focused
checks with no required fixes.

Durable review artifact:
`review-case2-a0-exponent-coordinate-bridge-a4.md`.
