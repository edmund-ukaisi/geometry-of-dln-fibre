# Review - A2 adjacent-window Case 2 selected-entry consumer

Reviewer: xhigh `Herschel the 4th`.

## Verdict

No findings.

## Checks

- The adjacent-window factor order is correct: the product from `p+2` to `p`
  is `C p.succ * C p.castSucc`.
- Endpoint equivalences are oriented correctly for `Matrix.submatrix`.
- The selected-entry bridge uses `e2.symm` and `e0κ.symm.trans eNext` in the
  correct direction.
- The fixed successor pivot remains a supplied displayed-product nonzero
  hypothesis.
- The retained-passive wrapper only forwards `data.C`; it does not claim
  full-suffix collapse or fixed-base source alignment.
- The documentation records the conditional boundary and nonclaims correctly.

## Residual risk

Future work may still need ergonomic adapters when instantiating the supplied
endpoint/factor hypotheses for an actual fixed-base source-readback family.
