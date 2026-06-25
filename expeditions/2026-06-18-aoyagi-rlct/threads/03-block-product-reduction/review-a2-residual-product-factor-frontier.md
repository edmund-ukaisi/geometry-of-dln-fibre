# Review - A2 residual-product factor frontier

Date: 2026-06-25.

Reviewers: xhigh source scout Dirac, xhigh pen-and-paper scout Poincare,
xhigh Lean API scout Herschel, xhigh final diff reviewer Pauli.

## Verdict

The factor-data direction is the correct next boundary for the selected-entry
residual-product frontier.

## Findings

Dirac checked Aoyagi PDF pp. 10-23 and confirmed that Aoyagi prints the p.13
block reduction, the later residual block `D_J`, and the top-left selected-entry
cleanup in Cases 1(2) and 2.  The paper does not print a fixed-base
`CedgeBase`, residual-index equivalence, source chart coverage, source-measure
identity, all-pivot atlas, normal crossings, pole order, or RLCT extraction
from this selected-entry chart alone.

Poincare checked the fixed-base realization question.  An arbitrary final
matrix `D : Matrix (kappa last) (kappa 0) R` cannot generally be realized as
`residualProduct Ebase last 0` without intermediate residual factors: the
product factors through every intermediate `kappa q`, so rank obstructions
appear whenever an intermediate residual space is too small.  The honest data
is a family `C p : Matrix (kappa p.succ) (kappa p.castSucc) R` together with a
product identity to the desired terminal matrix.

Herschel identified the smallest Lean API extraction:
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base`.
It says the existing fixed-base p.13 product-coordinate constructor preserves
the base suffix residual product.  This is a residual-product theorem, not an
integral/source wrapper, and needs no analytic hypotheses.

## Boundary Check

The new Lean statements should be read as chart-local/fixed-base algebra:

- `residualFactorProduct` exposes an explicit ordered product of supplied
  residual factors.
- `residualProduct_eq_residualFactorProduct_of_residualBlock_eq` proves the
  factor product from equality of all suffix residual blocks below the
  endpoint `j`.
- `residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct`
  specializes this to raw product-coordinate edge patterns.
- `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base`
  says the fixed-base p.13 constructor preserves the base residual product.

They do not prove the selected-entry residual-product matrix identity, produce
the residual factors from Aoyagi source data, realize an arbitrary terminal
matrix, construct a source chart, construct residual-index equivalence, prove
coverage or measure transport, or extract RLCT.

## Final Diff Review

Pauli found one wording/API issue: the general comparison lemma assumes equality
of all suffix residual blocks below endpoint `j`, while the first draft prose
said only "visited" blocks.  The theorem docstring and expedition notes were
updated to say "all suffix blocks below `j`"; the full p.13 `last,0` theorem is
unchanged, where this is the entire traversed suffix.
