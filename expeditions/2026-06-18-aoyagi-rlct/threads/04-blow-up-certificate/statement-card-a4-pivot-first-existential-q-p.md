# Statement card - A4 pivot-first existential `Q/P` wrappers

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `<pending Lean commit>`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.displayedPivot_mem_center_of_colBound`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.displayedPivot_mem_residualBlockPivotEntries_of_colBound`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.stripEntry_mem_residualBlockPivotEntries`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_pivotQ_of_forall_dvd`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_pivotQ_of_monomialRec_eq_or_le`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_pivotQ_of_pivotMul_monomialRec_eq_or_le`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_of_forall_dvd`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_of_monomialRec_eq_or_le`
- `DLNFibre.DLN.Aoyagi.exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le`

## Statement

Lean now packages the previously proved pivot-first `Q/P` algebra with the
previously proved quotient-witness layer. The new existential wrappers assume
either divisibility of each lower-row weight by the pivot weight, or
equality-or-later monomial recurrence data, and choose the function `q` needed
by the normalised `P` row operation.

Both versions are proved:

- the local identity ending with multiplication by `pivotQ`;
- the product-preservation identity with a following factor multiplied by
  `pivotQinv`.

The Case 1 helper lemmas add finite first-jump consequences: displayed-pivot
center membership, displayed-pivot residual-block membership, and strip-entry
residual-block membership under the existing first-jump row bound plus the
source column bound.

## Source role

Aoyagi's displayed `P` matrices use row-weight quotients. In Case 2 the source
flatness condition makes the quotients trivial; in Case 1 matrix pivot rows in
the row strip use equality inside the strip and recurrence-tail divisibility
for later rows. This checkpoint records the algebraic bridge needed once those
row-weight hypotheses have been transported into pivot-first coordinates.

## Proved

- Divisibility hypotheses can be used directly to choose the `q` in the
  pivot-first `Q/P` identities.
- Equality-or-later monomial recurrence hypotheses can be used directly to
  choose the `q` in the pivot-first `Q/P` identities.
- The same is true after common multiplication by a selected pivot variable.
- `Case1FirstJumpHypotheses` supplies the row-bound part of displayed-pivot
  and strip-entry residual-block membership.

## Assumed

- The selected pivot entry is already normalised to `1`.
- The matrix, following factor, row weights, and row-weight hypotheses are
  already in pivot-first coordinates.
- For recurrence wrappers, every lower row is either equal in recurrence
  weight to the pivot level or later than that level.

## Not proved

- No selected-entry chart construction, affine blow-up atlas, or chart
  coverage.
- No source reproduction of non-displayed arbitrary pivot charts.
- No coordinate or weight transport theorem for Aoyagi's following factors.
- No proof that all Aoyagi row hypotheses hold after a selected-entry chart.
- No Case 1 old-exceptional-variable branch.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-pivot-first-existential-q-p-a4.md`.
- Xhigh source, Lean, and roadmap explorers agreed this checkpoint must remain
  a conditional algebra bridge, not a chart-coverage theorem.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
