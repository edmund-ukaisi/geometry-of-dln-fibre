# Review - A2 retained-passive Case 2 pivot-nonzero source readout

Reviewer: xhigh `Schrodinger the 4th`.

## Verdict

Commit after small documentation edits.  No Lean blockers.

## Findings Addressed

- The reproduction originally described the fixed-pivot nonzero hypothesis as
  strictly weaker than the old entrywise readout.  This was softened to say
  that it replaces the supplied entrywise readout in the nonzero-pivot branch.
- The statement card originally listed `preimageOfPivotNeZero` under
  theorems, although it is a definition.  The heading now says
  "Definitions and theorems."

## Checks

- The fixed-pivot inverse is mathematically correct: a nonzero target pivot
  lets the selected-entry chart recover arbitrary target center coordinates by
  dividing nonpivot coordinates by the pivot.
- The Case 2 pivot-nonzero theorem genuinely constructs the previous
  `hentry` from one nonzero pivot value.  It does not prove that value is
  nonzero and does not construct a full source chart.
- The endpoint orientation is correct: successor center `(S,J+1)`, fixed
  pivot `(J+2,J+2)`, and
  `eNext : tau ~= Case2ResidualColIndex n S (J+1)` in the expected column
  direction.
- Focused Lean checks passed for the three touched modules.
