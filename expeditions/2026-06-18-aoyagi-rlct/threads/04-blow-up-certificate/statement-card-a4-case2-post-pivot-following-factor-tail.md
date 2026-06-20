# Statement card - A4 Case 2 post-pivot following-factor tail

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.pivotQinv_mul_tail_apply`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivResidualRowSucc_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRowComplementEquivResidualRowSucc_symm_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivResidualColSucc_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotColComplementEquivResidualColSucc_symm_apply_coe`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperCprimeTail_apply`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ`

## Statement

Lean now records that the lower tail of Aoyagi's displayed Case 2 transported
following factor `C' = Q^-1 C` is unchanged by the inverse column operation.
After reindexing the displayed pivot-column complement to the next same-stage
residual-column domain, the post-pivot following-factor candidate is exactly
the original source following factor restricted to `(S,J+1)` columns.

## Proved

- For `Q^-1 = [1 y; 0 I]`, every lower row of `Q^-1 C` equals the
  corresponding lower row of `C`.
- The displayed paper tail satisfies
  `case2DisplayedPaperCprimeTail ... j a = C j a` in raw source columns.
- The post-pivot following-factor candidate satisfies
  `case2DisplayedPostPivotFollowingFactor ... =
  case2SourceFollowingFactor (J := J+1) C`.
- Raw-value simp lemmas are available for the displayed pivot-complement
  equivalences to next same-stage row/column domains.

## Assumed

- Displayed Case 2 stage and continuation hypotheses:
  `1 <= S` and `J+1 <= prefixMinNat n (S+1)`.
- Source residual coordinates and source following factor are supplied.

## Cited

- None in Lean.  This is finite matrix algebra and subtype reindexing.

## Deferred

- Identifying this object with Aoyagi's full source-produced next
  `C'^(S+1)`.
- Chart production of recurrence or exponent post-data.
- Successor chart-family construction, atlas coverage, arbitrary pivot
  coverage, coordinate regularity, transition invariance, Jacobian arithmetic,
  normal crossings, RLCT extraction, terminal relabeling, and printed-vector
  repair.

## Review

- Source target selected by xhigh `Hume`.
- Lean API target selected by xhigh `Tesla`.
- Landed-patch review passed by xhigh `Kierkegaard`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
