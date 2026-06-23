# Statement card - A4 continuing certificate without chart family

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily`
- `sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily`
- `sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily`
- existing chart-family-bearing constructors as compatibility wrappers

## Claim

The displayed continuing Case 2 local source-chart certificate, its
ordered-field unit refinement, and its center-square/formal-Jacobian
refinement can be constructed without a supplied
`Case2ResidualBlockChartFamilyBoundary`.  Their fields are finite
selected-entry algebra, concrete `case2Succ` recurrence data, corrected
selected-label exponent data, and the direct reindexed next-source-product
identity.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- the continuation guard `J+1 <= prefixMinNat n (S+1)`;
- the continuing guard `J+2 <= prefixMinNat n (S+1)`;
- the old exponent certificates, level/least-value bridge, and integer
  least-value gap;
- the displayed chart variables `u`, `residual`, and following factor `C`;
- ordered-field assumptions only for the unit and center-square/formal-Jacobian
  refinements.

## Proved

The new direct constructors fill the continuing certificate fields without
`ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The older constructors
remain available but delegate to the direct constructors.

## Not Proved

No source production of `Csucc`, no successor chart family, no suffix
production, no terminal branch production, no coverage or transition
regularity, no analytic Jacobian/volume-form theorem, no normal-crossing
certificate, no pole order, and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/sorries
git diff --check
```

The focused raw Lean check and focused Lake target passed.  The no-sorry
scanner reported `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.
`git diff --check` passed.

Controller also attempted `cd lean && LAKE_JOBS=1 lake build DLNFibre` twice
after VM recovery.  The first run reached 3350/3356 targets and was killed by
the VM with exit code 137; the retry was terminated with exit code 143 before
a final success line.  Both attempts emitted only the known pre-existing Core
warnings before termination.  No Lean error was reported, but a full
post-recovery `DLNFibre` success was not obtained in this VM session.

## Review

Xhigh fidelity/bedrock review passed.  See
`review-case2-continuing-certificate-without-chart-family-a4.md`.
