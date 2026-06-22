# Statement card - A4 Case 2 successor following weighted handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData`

## Statement

Rewrite the displayed Case 2 paper-`C'` weighted lower-row handoff through the
formula-level source successor following factor `Csucc`.  The RHS tail becomes

```text
case2SourceFollowingFactor(S,J+1,Csucc)
```

instead of the definitionally equivalent restriction from the original `C`.
The supplied-`F` variant right-multiplies both sides by an arbitrary following
product.

## Proved

The `(S,J+1)` source-following restriction ignores the replaced row `J+1`, so
the existing lower-row handoff and its supplied-`F` right-multiplied variant can
be stated in successor-factor notation while preserving the same witness and
corrected post-data projections.

## Assumed

- Aoyagi displayed Case 2 hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- The supplied Case 2 chart-family boundary and pre-state certificate fields
  already required by the older handoff theorem.
- The optional following product `F` is supplied.

## Cited

- None in Lean.  This is finite row-restriction and equality rewriting.

## Deferred

- Nonempty next-center theorem for the continuing branch.
- Chart production of `Csucc` or of `F`.
- Full successor `C'^(S+1)`, old top rows, suffix product, chart coverage,
  arbitrary-pivot coverage, transition invariance, Jacobian arithmetic, normal
  crossings, pole order, termination, and RLCT extraction.

## Review

- xhigh source/math scout `Aquinas` passed the boundary and flagged the
  `hcont` versus `hnext` branch-language trap.
- xhigh Lean scout `Volta` passed the theorem shape and warned to keep
  `Csucc` at the old `(S,J)` while restricting at `(S,J+1)`.

## Verification

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
