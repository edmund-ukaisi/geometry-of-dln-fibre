# Review - A2 Retained-Passive Raw-Order Jacobian Density Interface

Date: 2026-06-27.

Reviewer: xhigh read-only explorer `Laplace the 4th`.

Verdict: accepted.  No blockers.

## Scope Reviewed

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-jacobian-density-interface.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-jacobian-density-interface.md
```

## Verdict Details

The Lean slice is mathematically sound and appropriately modest.  It proves
pointwise determinant nonvanishing and absolute positivity from the ambient
`fderiv` determinant-unit theorem, obtains eventual positivity from openness of
the determinant chart, and derives quantitative local lower and upper bounds
only under an explicit `ContinuousAt` hypothesis.

## Audit Notes

- The reproduction correctly separates pointwise determinant unitness from
  local quantitative lower bounds.
- The Lean statements do not prove or claim continuity of the retained-passive
  derivative family, a closed determinant formula, a pushforward/change of
  variables theorem, an inverse-density formula, normal crossings, pole order,
  or RLCT.
- The `_of_continuousAt` suffix on the lower/upper bound theorems correctly
  advertises that continuity is supplied, not proved.
- Placement and naming are consistent with the existing product-step density
  pattern.
- No hidden quiver-paper or non-Aoyagi dependency was found.

## Nonblocking Note

The upper-bound theorem does not require determinant-chart membership, unlike
the lower-bound theorem and the product-step paired API.  This is
mathematically fine because continuity alone gives a positive finite upper
bound.  A chart-specific wrapper can be added later if a downstream consumer
benefits from paired hypotheses.
