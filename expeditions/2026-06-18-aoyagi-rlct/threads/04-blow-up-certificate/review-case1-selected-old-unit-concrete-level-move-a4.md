# Review - A4 Case 1(1) Selected-Old Unit Boundary from Concrete Level Move

Pre-Lean reviewers: xhigh source/scope reviewer `Ramanujan the 3rd`; xhigh
Lean/API reviewer `Cicero the 3rd`.

Post-Lean reviewers: xhigh Lean/API reviewer `Ampere the 3rd`; xhigh
source/docs reviewer `Beauvoir the 3rd`.

Status: Lean-proved; pre-Lean and post-Lean reviews passed.

## Findings

No blocking findings.

The source/scope reviewer confirmed that the checkpoint is faithful to Aoyagi
PDF pp. 15-16: Case 1(1) uses the selected old exceptional variable as the
chart denominator, lowers its level from `J+J1` to `J`, and does not introduce
`(S,J+1)`.

The Lean/API reviewer confirmed that this theorem is not redundant with the
existing lowered-boundary constructor: the new checkpoint is the one-field
lift from the concrete lowered recurrence boundary to the Unit chart-family
boundary by carrying the supplied finite chart-family boundary.

The post-Lean reviewers found no blocking Lean/API or source-fidelity issues.
They confirmed that the theorem keeps `sameDomain` specialized to `pre.level`,
uses the fully qualified lowered-boundary constructor, and does not introduce
Case 1(2), `Q/P`, chart construction, transition proofs, coverage, Jacobians,
normal crossings, or RLCT extraction.

## Verdict

The checkpoint is a conservative boundary-instantiation theorem.  It combines
the concrete same-domain recurrence level move with a supplied
`Case1CenterChartFamilyBoundary`; it does not construct chart regularity,
transitions, coverage, Jacobians, normal crossings, or RLCT data.

## Residual Risks

- Chart regularity and transition regularity remain supplied fields.
- The `Unit` finite-center token does not identify `(s0,k0)` by itself.
- The theorem does not construct the selected-old chart from raw coordinates
  or prove the full transition invariant.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
