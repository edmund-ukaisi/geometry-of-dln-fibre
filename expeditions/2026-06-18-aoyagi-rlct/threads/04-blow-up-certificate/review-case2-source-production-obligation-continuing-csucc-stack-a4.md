# Review - Case 2 obligation continuing Csucc stack

Date: 2026-06-22.

Reviewers: xhigh scouts `Volta the 2nd`, `Kant the 2nd`, and `Ptolemy the
2nd`; controller Lean check.

## Verdict

Accepted as a finite supplied-obligation consumer.  It is useful because the
continuing source-current stack can now be consumed with the supplied
successor object `Csucc`, rather than only with the formula-level successor
block.  It does not move the chart/source-production boundary.

## Checks

- `Kant the 2nd` identified this exact theorem family as the best next A4 API
  slice: a block equality from `Csucc_eq_formula`, then a continuing
  source-current stack theorem with `case2SourceCurrentFollowingBlock n S
  Csucc`.
- `Ptolemy the 2nd` independently checked the row meanings: `Csucc` differs
  from `C` only at row `J+1`, the continuing tail starts at `J+2`, and
  row-exhausted data must not be collapsed to old rows without actual-width
  exhaustion.
- `Volta the 2nd` confirmed that a broad total paper-`C'` adapter would be
  cosmetic and that supplied-obligation consumers are the safer near-term
  direction.

## Kill Conditions Checked

- The theorem requires the continuing guard `J+2 <= prefixMinNat n (S+1)`.
- It consumes, rather than constructs, `SourceProductionObligation`.
- It does not introduce `True` chart/transition predicates.
- It does not replace row-exhausted transported rows by old rows.
- It does not claim chart coverage, transition regularity, normal crossings,
  pole order, termination, or RLCT.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```
