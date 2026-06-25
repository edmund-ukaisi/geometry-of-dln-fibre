# Review - A2 edge-matrix signed-box adapted-loss finite integral

Date: 2026-06-25.

Reviewer: xhigh `Copernicus the 5th`.

## Verdict

Pass.  No required fixes.

## Checks

- `ChartTopology.lean`: measurable finite-matrix rank loci are Borel
  preimages of closed determinantal rank loci; no continuity is hidden in the
  measurable variants.
- `ProductReductionBoundary.lean`: source-stratum measurability from
  measurable fixed-base edge matrices is sound and keeps base-rank and
  source-inequality conditions explicit.
- `RegularSuspensionLocalMeasure.lean`: the measurable-edge signed-box theorem
  keeps chart, pushforward, source-density bounds, residual monomial lower
  bound, product-coordinate adapted lower bound, and adapted-to-loss comparison
  as hypotheses.
- `OriginalLossLocalMeasure.lean`: the original `lossDLN` specialization uses
  only the finite endpoint basis comparison to discharge
  `c0 * adapted <= loss`; it does not smuggle in continuity of `Cedge`.
- Notes and statement card correctly frame the adapted-loss theorem as
  conditional plumbing, with no chart construction, density/Jacobian transport,
  normal crossing, pole order, or RLCT extraction.

## Reviewer Verification

The reviewer ran `lake env lean` successfully on all four focused Lean files
from the `lean/` project directory:

```text
DLNFibre/DLN/Aoyagi/ChartTopology.lean
DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean
DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean
```

No reviewer edits were made.
