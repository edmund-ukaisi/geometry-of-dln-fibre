# Review - A2 selected-entry finite sector cover

Date: 2026-06-25.

Reviewer: xhigh `Bacon`.

Verdict: pass.

## Scope Checked

The reviewer checked the uncommitted finite selected-entry sector-cover Lean
slice in:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

with declarations:

```text
SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_of_pivot_abs_max
SelectedEntrySignedBox.CenterCoord.exists_pivot_abs_le_abs_of_ne_zero
SelectedEntrySignedBox.CenterCoord.exists_maxPivot_mem_chartMap_image_signedBoxSet_of_mem_signedBoxSet_ne_zero
SelectedEntrySignedBox.CenterCoord.signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt
```

## Findings

No blocking findings.

The statements are mathematically correct as finite selected-entry signed-box
geometry.  The cover uses the fixed-pivot image characterization, a supplied
maximal-pivot inequality, finite maximum-coordinate existence, and then the
union over pivots.

The radius hypotheses are sufficient.  `S i <= R i` transfers the pivot bound
from the smaller signed box to the target radius, and `1 < R i` handles tied
maximal non-pivot quotients in the open quotient radii.  No separate
positivity assumption on `S` is needed.

## Boundary Check

The slice does not reduce the fixed-pivot local source-stratum equality
socket.  It proves only finite all-pivot sector geometry and does not prove
source/image equality, fixed-base source-chart construction, residual-product
matrix identity, source-measure identification, normal crossings, pole order,
or RLCT.

## Checks

The reviewer checked Lean elaboration for the touched file and `git diff
--check`.  The controller also ran:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
```

successfully before recording this review.
