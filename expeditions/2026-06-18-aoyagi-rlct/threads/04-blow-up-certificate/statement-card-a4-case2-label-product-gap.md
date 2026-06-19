# Statement card - A4 Case 2 label-product gap

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`d84eef1e59ee6d324927f6d55d4f9b570d70bdcc`.

Names:

- `DLNFibre.DLN.Aoyagi.levelProductStep`
- `DLNFibre.DLN.Aoyagi.levelProductStep_eq_one_of_forall_ne`
- `DLNFibre.DLN.Aoyagi.levelProductStep_eq_one_of_gap`
- `DLNFibre.DLN.Aoyagi.case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap`

## Statement

Lean now models a monomial recurrence factor as the product of supplied label
variables at a given level. If the supplied finite label set has no labels with
levels in the displayed Case 2 gap interval `J+1 <= r < mu_S`, then the
recurrence factors on that interval are `1`; hence the displayed residual row
weights are flat and the displayed source-substitution `Q/P` theorem applies.

## Source role

Aoyagi's recurrence multiplies `b_r` by the product of variables whose
`\tilde t` value is `r`. This checkpoint isolates the finite-product reason
that a label gap forces the recurrence factors to be `1` on the Case 2
displayed residual row range.

## Proved

- A finite product over labels at level `r` is `1` when no supplied label has
  level `r`.
- A supplied finite label gap on `J+1 <= level < mu_S` gives
  `step r = 1` for every `J+1 <= r < mu_S`.
- The previous Case 2 gap-row-weight bridge applies to this finite-product
  recurrence.
- The displayed source-substitution `Q/P` theorem applies with row weights
  `monomialRec (levelProductStep labels level var) rowLevel`.

## Assumed

- The finite `labels` set is the set used by the recurrence factor.
- The label-level map matches the row-weight recurrence levels.
- The residual rows are already the displayed Case 2 residual rows
  `J+1..mu_S`.
- The residual columns use the actual-width range `J+1..n_(S+1)`.
- The displayed pivot validity bound `J+1 <= prefixMinNat n (S+1)`.
- The selected variable is counted once in the updated weights `u * b_i`.

## Not proved

- No proof that the supplied finite labels are exactly Aoyagi's introduced
  labels at the recursive state.
- No proof that the recursive invariant establishes the label gap.
- No arbitrary selected-entry pivot chart or chart coverage.
- No polynomial coordinate-chart regularity or Jacobian theorem.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-label-product-gap-a4.md`.
- Reproduction check:
  `review-case2-label-product-gap-a4.md`.
- Review verdict: xhigh Lean/API and source/ledger reviews accept the result as
  a conditional finite-label bridge only. The supplied labels are not proved to
  be Aoyagi's actual introduced-label state, displayed rows remain
  `J+1..mu_S`, displayed columns remain actual-width `J+1..n_(S+1)`, and the
  selected variable is counted once in `u * b_i`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
