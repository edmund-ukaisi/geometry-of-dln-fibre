# Review - A2 local-source original-loss product-family continuation

Date: 2026-06-25.

## Verdict

Accepted as a conditional composition wrapper.

The theorem is source-faithful only at this scope: Aoyagi pp.10-13 support the
block/product-coordinate p.13 reduction and the separation of regular
variables from the residual product.  The Lean theorem packages already-proved
local-source/product-family data with the already-proved original-loss
local-source finite-integral socket.  It is not an additional theorem stated
by Aoyagi.

## Scope Checks

- The theorem constructs the measurable local source rather than assuming it.
- The returned source is still `sourceU inter sourceRankStratum`.
- The theorem keeps source-rank facts and the `nhdsWithin` equality available
  for future chart work.
- The product-coordinate family is the explicit self-base multi-edge family,
  not an arbitrary product family.
- Residual positivity and residual negative-power integrability remain
  hypotheses on the returned `source`.
- Density nonnegativity and boundedness remain hypotheses on
  `nhdsWithin x0 source` and the returned radius ball.
- The final integral is for the concrete endpoint square-Frobenius `lossDLN`
  of the chain-map matrix tuple built from the product-coordinate family.

## Audit Notes

The xhigh Lean/API audit accepted the API shape: construct `source`, `sourceU`,
`R`, and `c`; build a continuation by introducing `mu`, `nu`, `density`, `t`,
and `C`; install the supplied additive Haar proof as a local instance; and
delegate to the local-source original-loss socket.

The xhigh source-fidelity audit accepted the theorem only as Lean plumbing for
the p.13 reduction.  It specifically warned not to treat the result as chart
construction, source coverage, pushforward/Jacobian transport, residual
integrability, normal crossings, pole order, or RLCT extraction.

## Risks and Use Guidance

Use this theorem after a future local residual chart package has supplied the
remaining source-side analytic data on the returned `source`.  It should be the
preferred local-source original-loss consumer when the chart is tied to the
explicit self-base multi-edge product-coordinate family, because it no longer
requires callers to separately construct the local source or restate the
adapted product-family lower bound.

Do not use it as evidence that the signed-box source chart exists, that the
chart image covers a neighborhood, or that the residual and source-density
monomial-unit identities have been proved.

## Nonclaims

No signed-box chart, source image/coverage theorem, weighted pushforward,
Jacobian/source-density formula, prior-density construction, residual
positivity proof, residual negative-power integrability proof,
residual/source-density monomial-unit identity, normal-crossing extraction,
pole-order computation, or RLCT theorem is proved.
