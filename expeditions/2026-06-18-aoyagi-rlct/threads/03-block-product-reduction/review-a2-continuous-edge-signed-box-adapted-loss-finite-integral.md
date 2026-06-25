# Review - A2 continuous-edge signed-box adapted-loss finite integral

Date: 2026-06-25.

Reviewer: xhigh `Poincare the 5th`, read-only scout, plus controller
post-build check.

## Verdict

Accepted as the one useful composed A2 front end, provided it is documented as
conditional finite-integral plumbing and not as progress on the hard analytic
chart/loss-comparison gaps.

The scout advised against a ladder of low-value wrappers, but identified this
top front end as the only worthwhile A2 composition: it replaces the direct
local loss lower-bound hypothesis in the existing continuous-edge signed-box
continuous-density theorem by the two explicit adapted-loss hypotheses

```text
c * (residualSquareSum(x) + squareSum(u)) <= adaptedSquareSum(x,u),
c0 * adaptedSquareSum(x,u) <= loss(x,u),
```

and derives the final comparison constant `c0 * c`.

## Soundness Check

The proof keeps the base/source edge family `Cedge` distinct from the product
edge family `CedgeProd`.  The source stratum and residual square-sum use
`Cedge`; the adapted square-sum uses `CedgeProd`.

The proof assumes both adapted-loss hypotheses on `ball(0,Rmax)`.  The
continuous-density theorem shrinks to `R <= Rmax`, and the proof restricts the
hypotheses with `Metric.ball_subset_ball`.

## Nonclaims Check

The theorem still assumes the signed-box chart and pushforward, residual
monomial lower bound, source-density bounds, product density positivity and
continuity, product-coordinate adapted lower bound, and adapted-to-loss
comparison.  It does not prove source-rank openness, product chart
construction, density/Jacobian transport, original-loss comparison, normal
crossings, pole order, or RLCT extraction.

