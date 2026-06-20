# Review - A4 Case 2 Supplied Source-Selected Pivot Boundary

Status: reviewed; no blockers found.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh Lean/API scout `Archimedes the 3rd`.
- xhigh documentation scout `Hooke the 3rd`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Schrodinger the 3rd`.
- xhigh source/docs reviewer `Rawls the 3rd`.

## Source and Math Review

The source/math decision is to keep this as a supplied boundary. Aoyagi displays
the top-left Case 2 pivot in source order, while the finite selected-entry
algebra can be reindexed to any supplied residual-block pivot. The boundary
therefore packages pivot membership and the already-proved arbitrary-pivot
source-coordinate algebra without claiming source-displayed non-top-left pivot
charts.

The row and column bounds remain separated: residual rows are bounded by the
prefix minimum `M(S)`, while residual columns use the actual width
`M^(S+1)`. The corrected exponent post-data uses the prefix-minimum Case 2
certificate and does not erase the printed-vector mismatch.

## Lean and API Review

The Lean/API shape follows the scout recommendation: the boundary derives
`CorrectedCase2NewLabelCertificate` and `pre.case2Gap` from prefix-bound,
level-invariant, and least-value-gap fields, then feeds those derived facts to
the existing source-selected `Q/P` theorem.

The key type discipline is that the source-selected `Q/P` theorem consumes the
pre-state gap, not the post-state gap. The post-state gap is projected only for
downstream recurrence bookkeeping.

The post-Lean Lean/API review found no blocking correctness, namespace,
typeclass, or overclaiming issues. It specifically checked that
`sourceSelectedQP` feeds the derived `pre.case2Gap` into the existing
source-selected theorem.

## Required Caveats

- The pivot pair is supplied; this is not coverage.
- `ChartRegular` and `TransitionRegular` are supplied predicates.
- Recurrence post-data and exponent post-data are supplied packages.
- Aoyagi displays only the top-left Case 2 pivot in source order.
- Non-top-left source-order transition formulas remain outside this theorem.
- The selected variable is counted once in successor weights.
- No Jacobian, normal crossing, RLCT extraction, termination, or full
  transition invariant is proved.

The post-Lean source/docs review found no blocking source-fidelity issue. It
confirmed that the reproduction, statement card, and control ledgers preserve
the supplied-boundary scope and do not claim chart coverage, source-displayed
non-top-left charts, a full transition invariant, or printed-vector repair.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-review verification:

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
