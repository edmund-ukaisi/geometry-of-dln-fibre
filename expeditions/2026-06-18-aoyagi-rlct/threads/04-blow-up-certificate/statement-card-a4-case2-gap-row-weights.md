# Statement card - A4 Case 2 gap row weights

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`3b19c8cff32661b37f273dd9ca38f372b2bbdc8d`.

Names:

- `DLNFibre.DLN.Aoyagi.monomialTail_eq_one_of_forall_eq_one`
- `DLNFibre.DLN.Aoyagi.monomialRec_eq_of_step_eq_one_on_Ico`
- `DLNFibre.DLN.Aoyagi.case2ResidualRow_monomialRec_eq_pivot_of_gap`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec`

## Statement

Lean now proves that if the displayed Case 2 recurrence factors are all `1`
on the interval `J+1 <= k < mu_S`, then every displayed residual row has the
same monomial recurrence weight as the pivot row `J+1`. This supplies the
flat row-weight hypothesis needed by the displayed source-substitution `Q/P`
theorem.

## Source role

Aoyagi's Case 2 branch uses the absence of a later jump in the current residual
row range before applying the displayed `Q/P` calculation. This checkpoint
isolates the elementary consequence of that absence: the row-weight recurrence
does not change across the displayed residual rows.

## Proved

- A recurrence tail whose factors are all `1` has tail product `1`.
- A monomial recurrence is constant across an interval whose step factors are
  all `1`.
- In displayed Case 2, the residual row bound `i <= mu_S` turns a gap on
  `J+1..mu_S-1` into equality
  `monomialRec step i = monomialRec step (J+1)`.
- The existing displayed source-substitution `Q/P` theorem applies with row
  weights `monomialRec step rowLevel` under this explicit gap hypothesis.

## Assumed

- The gap hypothesis `step k = 1` on `J+1 <= k < prefixMinNat n S`.
- The residual rows are already the displayed Case 2 residual rows.
- The selected pivot is the source-displayed top-left residual entry.
- The displayed pivot validity bound `J+1 <= prefixMinNat n (S+1)`.
- The residual columns use the actual source width range `J+1..n_(S+1)`.
- The selected variable is counted once in the updated weights `u * b_i`.

## Not proved

- No proof that Aoyagi's recursive invariant establishes the gap.
- No arbitrary selected-entry pivot chart or chart coverage.
- No polynomial coordinate-chart regularity or Jacobian theorem.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-gap-row-weights-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
