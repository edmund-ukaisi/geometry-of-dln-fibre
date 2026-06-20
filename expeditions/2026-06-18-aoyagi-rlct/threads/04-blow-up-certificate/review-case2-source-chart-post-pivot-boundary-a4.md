# Review - A4 Case 2 source-chart post-pivot boundary

Reviewer: xhigh `Parfit`.

Scope:

- Lean boundary projections
  `Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct`
  and `postPivotResidualBlock_nonempty_of_next`.
- Concrete source-chart package
  `sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData`.
- Reproduction and statement-card scope against Aoyagi's displayed Case 2
  calculation.

## Verdict

Pass after a wording fix in the reproduction note.

No blocking mathematical/source-fidelity or Lean-scope issues were found.  The
Lean statements remain within the intended supplied-data compatibility scope:
lower-row post-pivot product projection, explicit next nonempty bound, and a
concrete conjunction with corrected supplied post-data.

## Finding Resolved

- Low wording precision: the reproduction note said the displayed source-chart
  pivot value was "definitionally `u`".  The source-chart map is written as a
  selected-entry expression and the pivot equality is proved separately, so the
  note now says the value "equals `u`".

## Checked Nonclaims

The patch does not claim:

- chart production of recurrence or exponent post-data;
- transition invariance;
- Jacobian, normal-crossing, or RLCT extraction;
- arbitrary pivot coverage;
- terminal relabeling;
- repair of the printed Case 2 vector mismatch.

## Verification

Reviewer ran:

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `git diff --check`

Residual risk: later consumers could overread the phrase "source-chart
package" unless they preserve the current supplied-data caveats.
