# Review - A4 Case 2 Displayed Concrete-Update Boundary

Status: reviewed; no blockers found.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh Lean/API scout `Volta the 3rd`.
- xhigh source/math scout `Boole the 3rd`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Bernoulli the 3rd`.
- xhigh source/docs reviewer `Hubble the 3rd`.

## Source and Math Review

The source/math decision is to specialize only to Aoyagi's displayed top-left
Case 2 pivot. The continuation bound puts `(J+1,J+1)` in the residual-block
center, and the named concrete recurrence/exponent assignments match the
corrected prefix-minimum certificate layer already used by the expedition.

This checkpoint deliberately does not prove that the displayed affine chart
produces those assignments. It only removes two arbitrary supplied fields by
choosing the existing concrete assignment functions.

## Lean and API Review

The Lean/API scout checked the proposed declaration shapes with
`lake env lean --stdin`. The implementation follows that shape:

- source-selected projections for displayed pivot membership and regularity;
- concrete source-selected constructor using `case2Succ` and `updateSelected`;
- displayed boundary wrapper with a projection to the existing source-selected
  boundary;
- displayed source-coordinate `Q/P` projection using the existing displayed
  theorem directly.

The post-Lean Lean/API review found no blocking issues. It confirmed that the
constructors use `pre.case2Succ u` and corrected prefix-minimum exponent
updates rather than `printedCase2Vector`, and that displayed pivot projections
remain supplied finite chart-family projections.

The post-Lean source/docs review found no source-overclaim. It requested that
new artifact files be staged with the commit and that this review artifact be
updated from its pre-review placeholder state.

## Required Caveats

- The concrete recurrence/exponent assignments are not chart-produced data.
- The corrected prefix-minimum exponent assignment is used, not the
  incompatible printed actual-width vector.
- `ChartRegular` and `TransitionRegular` remain supplied predicates.
- No non-top-left source-displayed Case 2 chart formula is proved.
- No coverage, Jacobian, normal crossing, RLCT extraction, termination, or full
  transition invariant is proved.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-review verification:

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
