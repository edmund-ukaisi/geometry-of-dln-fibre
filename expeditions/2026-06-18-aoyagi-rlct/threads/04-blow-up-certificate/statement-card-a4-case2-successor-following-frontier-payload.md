# Statement card - A4 Case 2 successor following frontier payload

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.ContinuingWeightedSuccFollowingFrontierPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal`

## Statement

Package the successor-following lower-row handoff with the explicit `hnext`
continuing guard and finite current-center principalization.  The RHS tail is
written as

```text
case2SourceFollowingFactor(S,J+1,Csucc)
```

where `Csucc` is the formula-level source successor following factor.

## Proved

Under `J+2 <= prefixMinNat n (S+1)`, the next residual block is nonempty.  The
already proved successor-following lower-row handoff and the current displayed
center principalization facts combine to form a successor-facing continuing
frontier payload.

## Assumed

- The displayed Case 2 hypotheses and the explicit `hnext` guard.
- The same supplied chart-family boundary and pre-state certificate fields as
  the older weighted frontier theorem.

## Cited

- None in Lean.  This is finite packaging and equality rewriting.

## Deferred

- A new `SourceChartFrontierBoundaryPackages` field for this equivalent
  successor-facing payload.  The theorem-only projection is now recorded in
  `statement-card-a4-case2-continuing-successor-following-handoff.md`.
- Source/chart production of `Csucc`, old top rows, suffix product, full
  successor `C'^(S+1)`, chart coverage, arbitrary-pivot coverage, transition
  invariance, Jacobian arithmetic, normal crossings, pole order, termination,
  and RLCT extraction.

## Review

- xhigh `Peirce` passed the payload lift as safe and recommended keeping it
  theorem-only until a downstream theorem needs the package interface field.

## Verification

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
