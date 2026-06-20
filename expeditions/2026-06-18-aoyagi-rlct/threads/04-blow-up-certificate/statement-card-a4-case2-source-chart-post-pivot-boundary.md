# Statement card - A4 Case 2 source-chart post-pivot boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postPivotResidualBlock_nonempty_of_next`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData`

## Statement

Lean now connects the displayed source-chart corrected post-data boundary to
the continuing-branch post-pivot next-block adapter.

From any supplied displayed Case 2 boundary, the lower rows of Aoyagi's paper
product `D''' * C'`, after pivot-complement row reindexing, equal the product
of the supplied post-pivot residual block and supplied following-factor tail
over the next same-stage domains `(S,J+1)`.  Under the explicit bound
`J+2 <= prefixMinNat n (S+1)`, the next residual-block center is nonempty.

The concrete source-chart package instantiates the boundary constructor whose
post state is `pre.case2Succ` at the displayed source-chart pivot value and
conjoins the product identity with the already-proved corrected post-data
projections: exponent-domain extension, post level/least-value invariants,
successor least-value Case 2 gap, and successor recurrence Case 2 gap.

## Proved

- The supplied displayed boundary exports the post-pivot lower-row product
  identity over the same `(S,J+1)` residual domains as its post state.
- The supplied displayed boundary exports next-center nonemptiness under
  `J+2 <= prefixMinNat n (S+1)`.
- The displayed source-chart constructor packages the product identity
  together with corrected supplied post-data projections at `(S,J+1)`.

## Assumed

- Displayed Case 2 stage and continuation hypotheses: `1 <= S`,
  `S <= L`, and `J+1 <= prefixMinNat n (S+1)`.
- The supplied pre exponent certificates, level/least-value bridge, Case 2
  least-value gap, and chart-family boundary required by the existing
  displayed source-chart constructor.
- Residual coordinates and the following factor are supplied as functions.

## Cited

- None in Lean.  This checkpoint is finite matrix algebra, reindexing, and
  projection of already-formalised corrected supplied post-data.

## Deferred

- Chart production of recurrence or exponent post-data.
- Construction of a successor chart-family boundary for `(S,J+1)`.
- Atlas coverage, arbitrary pivot coverage, coordinate regularity,
  transition invariance, Jacobian arithmetic, normal crossings, RLCT
  extraction, and terminal `(S+1,0)` relabeling.
- Repair of Aoyagi's printed Case 2 vector mismatch.

## Review

- Pen-and-paper/source scope checked by xhigh `Dirac`.
- Lean API scope checked by xhigh `James`.
- Landed-patch review passed by xhigh `Parfit`; wording fix applied.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
