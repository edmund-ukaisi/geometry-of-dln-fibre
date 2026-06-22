# Statement card - A4 Case 2 continuing successor-following handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages.continuingWeightedSuccFollowing`

## Statement

Convert a continuing weighted source-following frontier payload into the same
payload written with the formula-level successor following factor.  The package
projection applies this conversion to the existing
`SourceChartFrontierBoundaryPackages.continuingWeighted` field under the same
`hnext : J+2 <= prefixMinNat n (S+1)` continuing guard.

## Proved

The adapter preserves the nonempty next-center witness, corrected exponent
post-data, post level/gap data, and current-center principalization fields.  It
rewrites only the RHS following-factor restriction, using
`case2SourceFollowingFactor_successorFollowingFactor_succ`: after the Case 2
advance, the `(S,J+1)` following factor is restricted to rows strictly after
`J+1`, so replacing row `J+1` by the formula-level successor row does not
change that restricted factor.

## Assumed

- The original continuing weighted source-following payload, or a frontier
  package plus `hnext`.
- The standing displayed Case 2 hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.

## Cited

None.  This is finite row-restriction rewriting.

## Deferred

Source production of `Csucc`, construction of `C'^(S+1)`, successor
chart-family construction, source suffix production, chart coverage,
transition regularity, coordinate derivation of corrected post-data, Jacobian
arithmetic, normal crossings, pole order, termination, RLCT extraction, and
repair of the printed Case 2 vector mismatch.

## Review

Xhigh reviewer `Heisenberg` passed the slice as a finite adapter and flagged
the hidden-hypothesis boundary: this theorem is for the canonical
formula-level successor factor
`case2DisplayedSourceSuccessorFollowingFactor`, not for an arbitrary supplied
`Csucc` unless a separate equality to that formula is supplied.  Reviewer
`Pascal` later caught an initial projection universe restriction; the theorem
now keeps unrelated package field universes independent.

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
