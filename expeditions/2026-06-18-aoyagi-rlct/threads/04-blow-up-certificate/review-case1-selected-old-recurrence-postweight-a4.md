# Review - A4 Case 1(1) Selected-Old Recurrence Post Weights

Reviewer: xhigh subagent `Bohr the 3rd`.

Status: passed with no findings.

## Verdict

The pure recurrence theorem correctly models moving the selected old factor
from level `J+J1` down to level `J` on active residual rows `i >= J+1`.
Strip rows gain one factor of the selected old variable; rows below the strip
already contained the old factor and remain unchanged.

The residual-row specialization matches the existing Lean conventions:

- `case1ResidualRowStrip n S J J1 i` is the predicate
  `case2ResidualRowLevel n S J i <= J+J1`;
- `case2ResidualRowLevel_ge` supplies the active-row bound
  `J+1 <= case2ResidualRowLevel n S J i`.

The checkpoint keeps the base recurrence supplied rather than constructing it
from arbitrary source recurrence data.  It also keeps the Case 1(1) selected
old denominator separate from the displayed Case 1(2) pivot.

## Scope Check

No overclaim was found.  The Lean and reproduction text stay at recurrence and
source-matrix algebra, and do not assert chart construction, `Q/P`, atlas
coverage, regularity, Jacobians, normal crossings, RLCT extraction, or a full
transition invariant.

Residual risk: the existence and source interpretation of the supplied
factored base recurrence remain future work.

## Reviewer Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff --check`
