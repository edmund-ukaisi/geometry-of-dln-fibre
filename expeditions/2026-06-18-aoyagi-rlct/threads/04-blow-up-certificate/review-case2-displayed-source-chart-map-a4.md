# Review - A4 Case 2 Displayed Source-Chart Map

Status: reviewed; no blockers found.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh Lean/API scout `Kant the 3rd`.
- xhigh source/math scout `Newton the 4th`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Hegel the 4th`.
- xhigh source/docs reviewer `Franklin the 4th`.

## Source and Math Review

The source/math scout recommended the displayed top-left Case 2 source-chart
map as the next narrow checkpoint. The reproduced calculation is:

```text
d_(J+1,J+1) = u,
d_ij = u*rho_ij  off the pivot,
D_src = u*A,
A_(J+1,J+1) = 1.
```

The selected variable is counted once. The checkpoint may name the
source-coordinate map and its residual-block restriction, but must not claim
chart-produced recurrence/exponent post-data, coverage, Jacobian, normal
crossing, RLCT extraction, termination, or a full transition invariant.

## Lean and API Review

The Lean/API scout recommended the exact source map/block adapter layer and
warned that the block equalities need an explicit bridge between raw source
pair equality and residual-subtype pair equality. Lean now includes that bridge
as `case2Displayed_source_pair_eq_pivot_iff`.

The post-Lean Lean/API review found no blockers. It checked that the
raw-source-pair/subtype-pivot bridge is sound, that the source normalised and
substituted block lemmas genuinely restrict source residuals through
`case2SourceResidualBlock`, and that
`sourceDisplayedQP_sourceChartMap` only rewrites the already supplied
displayed `Q/P` theorem.

The post-Lean source/docs review found no blockers. It confirmed that the
reproduction keeps residual rows as prefix-minimum rows `J+1..M(S)` and
residual columns as actual-width columns `J+1..M^(S+1)`, and that the caveats
do not overclaim chart coverage, non-top-left formulas, chart-produced
post-data, Jacobian/regularity, normal crossings, RLCT, termination,
transition invariance, or printed-vector repair.

## Required Caveats

- This is source-coordinate map algebra for the displayed top-left Case 2 pivot
  only.
- The final boundary wrapper is a rewrite of an existing supplied displayed
  `Q/P` identity.
- Recurrence and exponent post-data remain supplied or concretely assigned
  bookkeeping; they are not chart-produced by this checkpoint.
- The printed Case 2 vector mismatch is not repaired here.
- The Lean source chart map is total on `Nat × Nat`; it is source-faithful for
  this checkpoint only after restriction to the Case 2 residual block.
- The map-level API inherits the surrounding `CommRing` section although the
  elementary source map itself needs less structure.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-review verification:

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
