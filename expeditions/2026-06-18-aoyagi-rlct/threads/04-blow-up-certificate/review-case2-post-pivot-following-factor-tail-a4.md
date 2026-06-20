# Review - A4 Case 2 post-pivot following-factor tail

Reviewer: xhigh `Kierkegaard`.

Scope:

- `pivotQinv_mul_tail_apply`;
- raw-value simp lemmas for displayed pivot-complement equivalences to next
  same-stage row/column domains;
- `case2DisplayedPaperCprimeTail_apply`;
- `case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ`;
- reproduction and statement-card scope.

## Verdict

Pass.  No blocking issues or overclaiming were found.

The Lean theorem is narrow: it identifies only the reindexed lower tail of
`Q^-1 C` with `case2SourceFollowingFactor` at `(S,J+1)`.  The theorem
docstring excludes a full transition theorem, and the reproduction/statement
card keep caveats adjacent to the claim.

## Checked Nonclaims

The patch does not claim:

- production of Aoyagi's full next `C'^(S+1)`;
- recurrence or exponent chart production;
- transition invariance;
- Jacobian, normal-crossing, or RLCT extraction;
- arbitrary pivot coverage;
- terminal relabeling;
- repair of the printed Case 2 vector mismatch.

## Verification

Reviewer ran:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, `#exit` in the
  Lean file
- `git diff --check`

Residual risks: this remains the displayed top-left Case 2 pivot only, and the
source check depends on Aoyagi PDF pp. 19-22 supporting
`C'_J^(S+1)=Q^-1 C_J^(S+1)`.
