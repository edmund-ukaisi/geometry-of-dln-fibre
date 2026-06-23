# Statement card - A4/A0 Case 2 exponent-minimum bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean`

Name:

- `Case2DisplayedContinuingA0ExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le`

## Claim

If a supplied coordinate of A0 finite exponent data matches the displayed
continuing Case 2 local step, and if the corresponding local ratio
`centerCard/2` lower-bounds every active coordinate ratio in that finite data,
then the finite exponent minimum is `centerCard/2`.

## Inputs Kept Explicit

- a supplied `D : AoyagiNormalCrossingExponentData`;
- a supplied coordinate `p : Fin D.numCharts × Fin D.numCoords`;
- a displayed continuing Case 2 local certificate;
- a supplied `Case2DisplayedContinuingA0ExponentCoordinateBridge cert D p`;
- an explicit lower bound over all active pairs:

```text
forall p' in D.activePairs,
  ((case2ResidualBlockPivotEntries n S J).card : Q) / 2 <= D.ratioAt p'
```

## Proved

```text
D.exponentMinimum =
  ((case2ResidualBlockPivotEntries n S J).card : Q) / 2
```

## Not Proved

No construction of `D`, no construction of `p`, no proof of the global lower
bound, no exponent-order statement, no chart production, no analytic chart
certificate, no analytic Jacobian or volume-form theorem, no pole order, and
no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Case2FiniteExponentBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge
cd lean && lake env lean DLNFibre.lean
```

The focused checks passed.

## Review

Xhigh source/math reviewer `Euler the 2nd` passed the slice with no findings.
Xhigh Lean/API reviewer `Schrodinger the 2nd` passed the API shape and
focused checks with no required fixes.

Durable review artifact:
`review-case2-a0-exponent-minimum-bridge-a4.md`.
