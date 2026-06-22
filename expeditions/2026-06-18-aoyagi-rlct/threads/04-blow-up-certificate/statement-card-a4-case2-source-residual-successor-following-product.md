# Statement card - A4 Case 2 source residual successor following product

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_successorFollowingFactor`

## Statement

The bare lower rows of Aoyagi's displayed product `D''' * C'` can be written
as a source-residual block times the source following factor of the
formula-level successor following factor `Csucc`.

## Proved

The existing source-residual/source-following product theorem combines with
`case2SourceFollowingFactor_successorFollowingFactor_succ`, since the
`(S,J+1)` following restriction ignores row `J+1`.

## Assumed

- Displayed Case 2 hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- Source residual data and following factor `C`.

## Cited

- None in Lean.  This is finite row-restriction rewriting.

## Deferred

- Weighted source-chart handoff in source-residual notation.
- Next-center nonemptiness, chart production of the residual representative or
  `Csucc`, old top rows, suffix product, full successor `C'^(S+1)`, transition
  invariance, normal crossings, pole order, termination, and RLCT extraction.

## Review

- xhigh `Sagan` passed the bare adapter as useful source-pair notation and
  recommended not adding the weighted source-chart variant unless a downstream
  theorem needs it.

## Verification

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
