# Statement card - A4 displayed top-left source-order adapter

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`76209d8507d853a8a6e0c152c3d50062b475c8d8`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.continuationBound_of_colBound`
- `DLNFibre.DLN.Aoyagi.WeightedPivotFirstSubstitutionData`
- `DLNFibre.DLN.Aoyagi.WeightedPivotFirstSubstitutionData.sourceOrder_identity`
- `DLNFibre.DLN.Aoyagi.exists_weightedPivotFirstSubstitution_sourceOrder_identity_of_forall_dvd`

## Statement

Lean now has a generic source-order adapter for Aoyagi's displayed top-left
selected-entry pivot calculation. Here "source-order adapter" means an
adapter for an already supplied source-substituted block in pivot-first
coordinates. The adapter assumes the selected chart and row weights have
already been transported into pivot-first coordinates:

```text
weightedSource = weightedPivotDiagonal b0 b * pivotPreQBlock x y D,
b i = q i * b0.
```

It then proves the source-order product identity

```text
(P * weightedSource) * C
  = (weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x*y))
      * (Q^-1 * C).
```

The existential wrapper chooses `q` when divisibility `b0 | b i` is supplied.

## Source Role

This is the finite algebraic handoff common to the source-displayed top-left
Case 1(2) and Case 2 pivot charts. It is not a chart construction or a
transition theorem.

For Case 1(2), this deliberately keeps the weighted source block supplied,
because the source divides only the row strip and transforms the old
exceptional variable. For Case 2, existing displayed residual-block wrappers
can supply stronger source-substitution data, but the printed-vector mismatch
still remains outside this algebraic adapter.

## Proved

- The Case 1 first-jump row bound and actual column bound imply
  `J+1 <= mu_(S+1)` for the displayed top-left pivot.
- A supplied weighted pivot-first source block satisfies the displayed
  source-order `Q/P` identity.
- Divisibility of lower row weights by the pivot row weight supplies quotient
  witnesses for the adapter.

## Assumed

- The weighted source block has already been produced and transported to
  pivot-first coordinates.
- The pivot block is already normalised to have top-left entry `1`.
- Row-weight quotient/divisibility data are supplied.
- The following factor is already in the matching pivot-first column order.

## Not Proved

- No selected-entry chart construction.
- No affine blow-up atlas or chart coverage.
- No chart regularity or transition regularity.
- No full residual-block substitution for Case 1(2).
- No source validity of the hidden old label represented by `Unit`.
- No recurrence or exponent post-data.
- No continuation/advance transition invariant.
- No polynomial-coordinate Jacobian formula, normal crossings, or RLCT
  extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-displayed-top-left-source-order-adapter-a4.md`.
- Reproduction check:
  `review-displayed-top-left-source-order-adapter-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
