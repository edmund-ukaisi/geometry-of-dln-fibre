# Review - A4 Case 2 Source-Selected Chart-Map Adapter

## Reviewers

- Source/math fidelity: `Popper the 4th`, xhigh.
- Lean/API soundness: `Ramanujan the 4th`, xhigh.

## Findings

No math/source-fidelity blocker was found.  The checkpoint keeps Aoyagi
pp. 19-21 as the source anchor for Case 2's residual-block center and
displayed top-left chart, while the new arbitrary source-selected statements
remain conditional on a supplied pivot membership proof.  The notes and Lean
docstrings do not claim atlas coverage, non-top-left displayed chart formulas,
or chart-produced post-data.

No Lean/API soundness blocker was found.  The subtype bridge
`case2SourceSelected_source_pair_eq_pivot_iff` correctly relates equality of
source coordinate pairs to equality of the residual-row/residual-column subtype
pivot extracted from `hp`.  The boundary theorem
`Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap`
uses the extracted pivot row and column and keeps the leading post weight as
`post.weight (case2ResidualRowLevel n S J row)`, not the displayed
top-left specialization `post.weight (J+1)`.

The Lean/API reviewer noted a low naming risk: the two `OfMem` maps take an
arbitrary source coordinate pair `q : Nat x Nat`, and the membership proof
certifies only the selected pivot `p`, not the input `q`.  The Lean docstrings
now state this explicitly.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff --check`

## Residual Risk

The remaining risk is intentional: this is a finite adapter for supplied
source-selected pivot data.  It does not construct an affine blow-up atlas,
prove coverage or regularity from coordinates, produce recurrence or exponent
post-data from the chart, compute Jacobians, prove normal crossings, extract
RLCT, prove termination/transition invariance, or repair the printed Case 2
vector mismatch.
