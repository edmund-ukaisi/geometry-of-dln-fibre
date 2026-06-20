# Review - A4 Case 2 Displayed Center Count

Status: reviewed; no blockers found.

## Reviewers

Pre-Lean/read-only scouts:

- xhigh source/math scout `Nietzsche the 4th`.
- xhigh Lean/API scout `Wegener the 4th`.

Post-Lean reviewers:

- xhigh Lean/API reviewer `Confucius the 4th`.
- xhigh source/docs reviewer `Ohm the 4th`.

## Source and Math Review

The source/math scout found this checkpoint source-faithful when stated as a
selected coordinate-equation count for the displayed Case 2 residual block.
The reproduced count is:

```text
|{J+1,...,M(S)}| = M(S)-J,
|{J+1,...,M^(S+1)}| = M^(S+1)-J,
N = (M(S)-J)(M^(S+1)-J).
```

The scout emphasized that this is not a center-dimension theorem, not a
Jacobian exponent, and not chart-produced exponent post-data.

## Lean and API Review

The Lean/API scout supplied checked statement shapes using `Nat.card_Icc` and
the existing residual-block definitions. Lean now includes the continuation
bound helpers, row/column/product cardinality lemmas, and an integer corrected
numerator expression equal to the cardinality under explicit bounds or under
continuation.

The post-Lean Lean/API review found no blockers. It checked the inclusive
interval cardinalities, the continuation-bound helpers, and the integer
cardinality comparison. The review confirmed that `Nat.cast_sub` is used only
under explicit bounds or bounds derived from continuation.

The post-Lean source/docs review found no blockers. It confirmed that the docs
keep rows as prefix-minimum `J+1..M(S)` and columns as actual-width
`J+1..M^(S+1)`, and that the caveats do not overclaim dimension, Jacobian
exponent, chart production, coverage, normal crossings, RLCT, termination, or
transition invariance.

## Required Caveats

- The column range is actual width `n(S+1)`, not prefix minimum
  `prefixMinNat n (S+1)`.
- The cardinality lemmas over `Nat` use truncated subtraction and therefore
  need no bound hypotheses; the integer numerator comparison needs explicit
  bounds or continuation.
- The count is not a Jacobian exponent and is not the full chart post-data
  calculation.
- If downstream code needs positivity or nonemptiness, it must use separate
  bounds or continuation hypotheses rather than the unconditional truncated
  cardinality lemmas alone.
- `correctedCase2NewLabelNumerator` is just an integer expression outside the
  stated bounds; equality to a finite cardinality is proved only under explicit
  bounds or continuation.

## Verification

Pre-review focused Lean check:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Post-review verification:

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
