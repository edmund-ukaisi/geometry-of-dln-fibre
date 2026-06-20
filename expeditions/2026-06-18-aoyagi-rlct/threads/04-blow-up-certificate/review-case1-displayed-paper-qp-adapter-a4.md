# Review - A4 Case 1(2) Displayed Paper `Q/P` Adapter

Status: reviewed by controller and independent xhigh reviewers; pass after
proof repair.

## Math Review

The checkpoint is source-faithful as a paper-facing adapter for Aoyagi's
displayed top-left Case 1(2) chart. The reproduction separates:

- the normalized source-coordinate block;
- the row-strip source block, where only strip rows are multiplied by the
  displayed pivot variable;
- `Q = [1 -y; 0 I]`;
- `Q^-1 = [1 y; 0 I]`;
- `D'' = D_chart * Q`;
- `C' = Q^-1 C`;
- `D''' = blockdiag(1,D - x*y)`.

The selected variable is counted once. Strip rows get the factor from
`d_ij = u d'_ij`, while lower residual rows remain undivided and get the
factor through the hidden old-variable substitution
`u_(s,k)=u_(S,J+1)u'_(s,k)`.

## Lean/API Review

The new `case1DisplayedPaper*` names are paper-facing aliases for supplied
source-coordinate data, not constructed chart data. `Dchart` is an internal
name for the already normalized mixed pre-`Q` source-coordinate block; Aoyagi
does not explicitly name that block `D_chart`.

The residual domains are correct: prefix-minimum residual rows and
actual-width residual columns. The theorem stays at the displayed Case 1(2)
source-order boundary and does not shift the residual block to `(S,J+1)`.

No `Unit`/displayed-pivot confusion was found. The selected-old `Unit` token
remains supplied through the boundary, while this paper `Q/P` theorem uses the
displayed top-left pivot through `case2DisplayedPivotRow` and
`case2DisplayedPivotCol`.

`case1DisplayedPaperDpp_eq_pivotPostQBlock` uses the right normalization
hypothesis: the source-coordinate displayed pivot value
`residual (J+1,J+1)=1`. The theorem `case1DisplayedPaperDpp_mul_Cprime`
correctly records the paper orientation `C' = Q^-1 C` by proving
`D'' * C' = D_chart^pivot * C`.

The main theorem
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates_paperQP`
is intentionally duplicative: it is a notation/adapter layer over the already
supplied source-order identity.

## Caveats

- `Dchart` should not be described downstream as a source-named object; it is
  the Lean name for the normalized residual block before `Q`.
- The raw chart, selected-old pullback, recurrence/exponent post-data, and
  quotient witnesses remain supplied by earlier boundaries.
- No affine chart construction, atlas coverage, regularity from coordinates,
  Jacobian formula, transition invariant, normal crossings, or RLCT extraction
  is proved.
- No non-displayed pivot chart or arbitrary-pivot coverage is asserted.

## Independent xhigh Review

The source reviewer initially saw an obsolete failing proof of
`case1DisplayedPaperDpp_mul_Cprime`; the proof was repaired by explicit
reassociation and the focused Lean check subsequently passed. The reviewer
found no source-fidelity issue and confirmed that the note avoids
double-counting `u`.

The Lean/API reviewer reran
`lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and `git diff
--check`; both passed. The reviewer confirmed that the adapter is worth keeping
as a paper-facing bridge and that `C' = Q^-1 C` is oriented correctly.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
