# Review - A2 selected-entry chart Jacobian pushforward

Date: 2026-06-25.

## Verdict

Accepted after low-severity cleanup.

The reviewer found no mathematical fidelity issue.  The Lean chart is the
selected-entry map `u` on the pivot and `u*y_i` off the pivot; the determinant
is `u^(center.erase pivot).card`; the density is its absolute value; injectivity
is used only on `{u != 0}`; and the full-box statement is recovered by deleting
the null pivot hyperplane.

## Findings And Fixes

- Downstream specializations also need measurability of the chart image.  Fixed
  by adding
  `measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero` and
  `measurableSet_chartMap_image_signedBoxSet`.
- The module docstring still said no pushforward identity was supplied.  Fixed
  to state the finite selected-entry pushforward theorem while keeping source
  coverage/original-measure claims out of scope.
- The file imported the normal-crossing layer unnecessarily.  Fixed by
  replacing `SelectedEntryNormalCrossing` with `BlowupArithmetic`.

## Boundary

This slice proves finite chart transport only.  It does not construct the p.13
source chart, prove source image/coverage in the original parameter space,
identify the original source measure, compare the full DLN loss, produce normal
crossings, compute pole order, or extract RLCT.
