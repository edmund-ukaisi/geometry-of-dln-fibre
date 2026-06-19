# Statement card - A4 Case 2 source-block tail lift

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`f60cc5a46f4d7ebba089d728d6560d8f43898ffc`.

Names:

- `DLNFibre.DLN.Aoyagi.verticalBlock`
- `DLNFibre.DLN.Aoyagi.fromBlocks_mul_verticalBlock`
- `DLNFibre.DLN.Aoyagi.fromBlocks_mul_verticalBlock_eq_of_tail`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec`

## Statement

Lean now proves that an already-proved displayed Case 2 residual-tail `Q/P`
identity can be lifted through unchanged top rows by block-diagonal
multiplication:

```text
fromBlocks A_top 0 0 L_tail * verticalBlock C_top C_tail
  =
fromBlocks A_top 0 0 R_tail * verticalBlock C_top C_tail'.
```

The displayed wrappers instantiate this for the source-substitution tail
identity and for the row-index monomial-recurrence transported-following-factor
identity.

## Source role

Aoyagi's displayed Case 2 calculation performs `Q` and `P` operations on the
residual block while the earlier top rows are carried along unchanged. This
checkpoint proves that finite block-matrix bookkeeping: the top rows receive
the same action on both sides, and the proved residual-tail identity supplies
the lower block.

## Proved

- Vertical stacking of top and residual following-factor row blocks.
- A block-diagonal matrix acts separately on the top and residual blocks.
- Any residual-tail product identity lifts through the unchanged top block.
- The displayed source-substitution `Q/P` tail identity lifts through this
  top block under the existing flat-row-weight hypothesis.
- The displayed row-index monomial-recurrence `Q/P` tail identity lifts through
  this top block, with the following factor replaced by `Q^-1 C_tail`.

## Assumed

- The residual-tail identity has already been proved in displayed pivot
  coordinates.
- The selected pivot is the source-displayed top-left residual entry.
- Tail row weights are supplied in the needed flat or
  `u * monomialRec step rowLevel` form.
- The top block is unchanged except for the same supplied `A_top` on both
  sides.
- The selected variable is counted once in the updated row weights.

## Not proved

- No arbitrary selected-entry pivot chart or chart coverage.
- No full polynomial-coordinate source chart construction.
- No proof that Aoyagi's recursive state produces the row weights used here.
- No Jacobian or regular-coordinate theorem.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-source-block-tail-lift-a4.md`.
- Xhigh Lean-shape explorer and xhigh source/ledger fidelity explorer both
  reviewed the scope during promotion.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
