# Review - A4 Case 2 chart-index Schur transition

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Raman the 2nd`; controller gate.

Verdict: pass.

## Scope Reviewed

- Lean diff in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- Lean diff in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- reproduction note
  `reproduction-case2-chart-index-schur-transition-a4.md`;
- statement card
  `statement-card-a4-case2-chart-index-schur-transition.md`.

## Findings

No blocking soundness or fidelity issues were found.

The reviewer confirmed that the denominator hypothesis is the normalised
target coordinate, not `u` times that coordinate; that supplied source and
target pivot memberships are preserved; that the chart-indexed theorem obtains
both memberships from `finsetSubtypeChartEquiv`; and that the docstrings and
docs restrict the result to finite selected-entry algebra.

Non-blocking caveat: the off-pivot indices in these wrappers are ambient
`ℕ` complements of the target row and column, not residual-row and
residual-column subtype complements.  This is sound because the normalised
source-selected map is total on source coordinate pairs.  Do not cite this
wrapper as a residual-block-domain restriction without an additional subtype
adapter.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
git diff --check
```

The controller additionally ran:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build still reports pre-existing unrelated Core/style
warnings.
