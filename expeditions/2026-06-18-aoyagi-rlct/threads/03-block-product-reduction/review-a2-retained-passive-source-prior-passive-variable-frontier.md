# Review - A2 Retained-Passive Source-Prior Passive-Variable Frontier

Reviewer: Fermat the 3rd, xhigh read-only review.

## Verdict

PASS.

No blocking math or formalisation issues were found.

## Checks

- Aoyagi Lemma 2 signs are represented correctly:
  `F2 = -A1^{-1} A2`, `F3 = -A3 A1^{-1}`, and
  `C4 = -A3 A1^{-1} A2 + A4`.
- The p.13 product-difference display has the correct signs and order:

  ```text
  [C1-Er, -F2; -F3, prod C^(s)-F3F2].
  ```

  In particular, the bottom-right term is `F3 F2`, not `F2 F3`.
- The one-step inverse equations match the existing Lean product-reduction
  coordinate infrastructure:
  `C1 = Ctop A1^{-1}`, `A2 = -A1 F2`,
  `F3old = F3 + D A3 Ctop^{-1}`, and `A4 = C - A3 F2`.
- The lower-dimensional warning is correct: existing Lean records the reduced
  p.13 section with raw `C1 = 1` and raw `A3 = 0`, so it cannot imply full
  raw/determinant-chart Haar pushforward without adding passive variables and
  proving a full chart/Jacobian theorem.
- The source-prior boundary is stated correctly.  Aoyagi pp. 10-13 support the
  finite block/product substitutions, not selected-entry coverage,
  source-rank image equality, raw/source Haar transport, or original DLN prior
  transport.

## Nonblocking Issue

The proposed next Lean payoff names in the statement card are schematic.  They
must be sharpened into actual statements before implementation, with explicit
domain, source map, inverse or image theorem, source and target measures,
local neighborhood, pivot-sector, and rank hypotheses where relevant.

In particular, any theorem shaped like
`sourceRankStratum_subset_selectedEntryPassiveImage` must be visibly local and
sector/rank-qualified, so it cannot be read as global source-rank coverage.
