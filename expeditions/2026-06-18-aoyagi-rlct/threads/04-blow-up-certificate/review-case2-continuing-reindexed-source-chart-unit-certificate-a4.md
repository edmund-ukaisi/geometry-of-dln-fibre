# Review - A4 Case 2 continuing reindexed source-chart unit certificate

Date: 2026-06-23.

Verdict: PASS.

Reviewers:

- source/math fidelity: `Lorentz the 2nd`, xhigh;
- Lean/API: `Godel the 2nd`, xhigh.

## Source/Math Findings

No source/math fidelity issue was found.  The slice is an A4-local
ordered-field refinement: it packages the existing displayed continuing Case
2 reindexed source-chart certificate together with the pointwise unit witness
for the normalized selected-entry center-square factor

```text
selectedEntryCenterSqUnitFactor
  ((case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)) residual.
```

Aoyagi p. 5 supports the sum-of-squares convention, and PDF pp. 19-22 support
the displayed top-left Case 2 selected-entry chart where `(J+1,J+1)` maps to
`u` and every other residual-block center entry maps to `u * residual`.

## Lean/API Findings

No Lean/API issue was found.  The statement shape uses a fresh ordered-field
coefficient type:

```text
{τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
```

The field `toReindexedSourceChartCertificate` includes the existing A4-local
certificate without duplicating its fields.  The three new fields target the
exact intended erased-center factor:

```text
centerSqUnitFactor_pos
centerSqUnitFactor_ne_zero
centerSqUnitFactor_isUnit
```

No import change was required.  The constructor takes `hSL` and `hnext`
because the base continuing constructor requires them; the unit-refinement
structure itself does not store those guards.

## Required Caveats

This is pointwise ordered-field algebra, not an analytic local-ring unit or
constructed neighbourhood statement.  It is only for the displayed top-left
Case 2 chart, not arbitrary selected-entry chart coverage.  It does not prove
unit control for later `P`/`Q` regular changes, a total loss unit, a
Jacobian/volume-form theorem, an A0 normal-crossing chart certificate, pole
order, or RLCT extraction.  The corrected post-weight convention remains in
force; do not double-count Aoyagi's printed outside `u`.

## Checks

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build succeeds with only pre-existing Core warnings.
The Lean/API reviewer also ran the focused check read-only.
