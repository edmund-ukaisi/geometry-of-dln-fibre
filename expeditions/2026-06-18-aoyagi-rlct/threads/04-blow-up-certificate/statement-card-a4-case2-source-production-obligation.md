# Statement Card - A4 Case 2 Source Production Obligation

2026-06-22 update: the previously described continuing supplied
next-chart-family field has been removed from the current Lean structure as a
vacuous API boundary.  See
`statement-card-a4-case2-source-production-obligation-remove-vacuous-next-boundary.md`.

## Lean Name

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`

## Claim

The displayed Case 2 source-production frontier can be named as a supplied
`Prop` interface whose fields keep the continuing, actual-width stopped, and
row-exhausted stopped branches separate.  The interface records the formula
for a supplied successor following object `Csucc`, actual-width original
terminal rows, row-exhausted transported terminal rows, and the branch-specific
frontier payloads under explicit branch hypotheses.

## Proved

Lean introduces the interface only.  It checks that the branchwise payloads can
be stated simultaneously without collapsing their row meanings or terminal
domains.  No inhabitant is constructed from the current displayed chart
boundary.

## Assumed

An inhabitant supplies the successor following object, terminal source matrix,
branch payloads, source suffix factors, and source following factor.  It also
carries the existing displayed boundary data, including supplied chart-family
and corrected post-data fields.

## Deferred

Constructing the obligation from source coordinates, source production of full
`C'^(S+1)`, suffix production or inheritance, chart coverage, transition
regularity, coordinate derivation of corrected post-data, Jacobian arithmetic,
normal crossings, pole order, termination, and RLCT.

## Cited

None for this A4 interface.

## Verification

Focused Lean, module build, full build, sorry scan, and diff check pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Historical xhigh review passed with the `continuing_suppliedNextChartFamily`
naming hardening applied.  That field has since been removed as vacuous.  See
`review-case2-source-production-obligation-a4.md`.
