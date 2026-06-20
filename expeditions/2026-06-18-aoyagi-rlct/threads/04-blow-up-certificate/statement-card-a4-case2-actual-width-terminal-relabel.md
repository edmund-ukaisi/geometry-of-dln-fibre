# Statement card - A4 Case 2 actual-width terminal relabel

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.relabel_currentSucc_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelLevelInvariants.relabel_currentSucc_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_level`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_var`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_step_eq`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.stageRelabelSuccZero_weight_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_level`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_var`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_step_eq_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_weight_eq_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPostLevelInvariants_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelExponentDomain_of_actualWidth`

## Statement

Lean now proves the actual-width terminal relabel for supplied displayed Case 2
post-data.  A post-state over old `(S,J+1)` can be copied to a candidate
state over `(S+1,0)`.  Under

```text
n(S+1) = J+1,
```

the introduced-label finite domains agree, so the copied state has the same
recurrence step and row weights as the old post-state.  The level/least-value
bridge and all-label exponent certificates transport to `(S+1,0)`.

## Proved

- A copied recurrence state `stageRelabelSuccZero`.
- Pointwise equality of copied `level` and `var` maps.
- Step and weight equality under actual-width exhaustion.
- Transport of `IntroducedLabelLevelInvariants`.
- Transport of `IntroducedLabelExponentCertificates`.
- Displayed-boundary projections for relabelled post-state, level invariant,
  and exponent domain.

## Assumed

- Actual next-width exhaustion `n(S+1)=J+1`.
- A supplied displayed Case 2 boundary for the displayed projections.
- The old post recurrence and exponent maps are already supplied by that
  boundary.

## Not Proved

- No chart production of recurrence or exponent data.
- No transport of Case 2 gap or flat-tail invariants.
- No proof that `[Ctop;C0]` is source-produced `C'^(S+1)`.
- No chart coverage or regularity, Jacobian arithmetic, normal crossings,
  RLCT extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-actual-width-terminal-relabel-a4.md`.
- Review artifact:
  `review-case2-actual-width-terminal-relabel-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
