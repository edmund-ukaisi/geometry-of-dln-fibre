# Review - A4 Case 2 source successor following factor

Status: reviewed and formalised.

Reviewer: xhigh `Locke`.

## Verdict

Pass.  No blocking findings.

## Scope Check

The source-order successor following factor is source-faithful at the formula
level.  Aoyagi pp. 19-22 form `C' = Q^-1 C`; in the displayed `Q^-1`
operation only the pivot/top row changes, while the lower tail is unchanged.
The Lean object packages this by replacing source row `J+1` with the top row
of `Q^-1 C`.

The restriction lemmas are correct:

- pivot, off-pivot, and old-top rows are direct row-replacement facts;
- the post-pivot tail is unchanged because the `(S,J+1)` following domain has
  source indices at least `J+2`;
- actual-width collapse uses the stronger hypothesis `n(S+1)=J+1`;
- terminal transported rows and terminal candidate as original rows of the
  successor factor agree with the existing terminal-row API.

## Boundary Check

The docs and theorem names keep the slice below chart production.  The result
does not claim a transition invariant, chart coverage, row-exhaustion as
actual-width exhaustion, Jacobian arithmetic, normal crossings, pole order, or
RLCT.

## Naming Note

The reviewer recommended renaming the actual-width theorem from
`eq_self_of_width_next_eq` to `eq_original_of_width_next_eq`, since it proves
equality with the original following factor `C`.  The landed theorem uses the
clearer name.

## Checks

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `git diff --check` passed.
- No proof-placeholder tokens were introduced in the touched Lean file.

No quiver/Lehalleur-Rimanyi source was used.
