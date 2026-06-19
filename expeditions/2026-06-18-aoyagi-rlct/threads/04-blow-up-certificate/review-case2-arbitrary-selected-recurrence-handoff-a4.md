# Review - A4 Case 2 Arbitrary Selected-Entry Recurrence Handoff

Status: reviewed; no blockers found.

## Source and Math Review

The source-facing review found no formalisation or mathematical accuracy
blocker in the handoff.

- The selected residual row is genuinely arbitrary: the Lean statements
  quantify `rowPivot : Case2ResidualRowIndex n S J`, and successor weights are
  rewritten at `case2ResidualRowLevel n S J rowPivot`, not forced to the
  displayed row `J+1`.
- The old `case2Gap` hypothesis is scoped to the old recurrence state and the
  residual-row interval beginning at `J+1`, which is enough to make the old
  residual-row weights flat for every row in `Case2ResidualRowIndex n S J`.
- Residual-row and residual-column domains remain separate: rows use the
  prefix-minimum residual interval, while columns use the actual next-layer
  width interval.
- The reproduction note and statement card keep `post` and the pivot supplied,
  and do not claim chart production, arbitrary-pivot coverage, Jacobians,
  exponent transition, normal crossings, or RLCT extraction.

The review only noted that this review file was referenced by the statement
card before it existed; this artifact fixes that documentation gap.

## Lean and API Review

The Lean/API review found no blocker. The targeted file check passed.

Non-blocking API observations:

- The successor-weight wrappers currently take
  `CorrectedCase2NewLabelCertificate`; their proofs only use the new-label
  weight-update component. This is sound but couples recurrence transport to
  corrected exponent bookkeeping.
- The main recurrence-state theorem has `L` explicit even though it is
  determined by the recurrence-state argument. Dot-notation wrappers partly
  compensate for this.
- Under flat weights, the quotient witnesses are morally all `1`, but the
  current API exposes only an existential quotient. Future chart-coordinate
  code may want an explicit matrix witness.
- One successor-weight `Q/P` proof rewrites a large equality in place. A later
  small diagonal-rewrite lemma could make successor-weight wrappers less
  sensitive to expression shape.

These points do not affect the proved statement or source fidelity of this
checkpoint.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`: passed in review.
- Controller rerun:
  `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`: passed.
- Controller rerun: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- Controller rerun: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- Controller rerun: `git diff --check`: passed.
