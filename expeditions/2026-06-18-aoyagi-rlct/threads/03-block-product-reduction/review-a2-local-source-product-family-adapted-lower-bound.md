# Review - A2 local-source product-family adapted lower bound

Date: 2026-06-25.

## Verdict

Accepted at local-source product-family lower-bound scope.

The theorem combines two already-audited pieces: measurable local-source
extraction from the source certificate and the explicit self-base multi-edge
p.13 product-coordinate adapted lower bound.  The only new move is transporting
an eventual statement along the proved equality of `nhdsWithin` filters.

## Scope Checks

- The local source is concrete: `source = sourceU inter sourceRankStratum`.
- The theorem proves `MeasurableSet source` and `x0 in source`.
- The theorem keeps `source subset sourceRankStratum` and the canonical
  source-rank conclusion for all points of `source`.
- The theorem returns the `nhdsWithin` equality, so later local chart packages
  can reuse other source-stratum eventual facts without rerunning source
  extraction.
- The adapted lower bound is exactly the existing multi-edge self-base product
  family lower bound, not an arbitrary product-family assertion.
- The proof does not introduce measure transport or density facts.

## Source-Fidelity Notes

Aoyagi pp.10-13 support the p.13 block/product-coordinate lower-bound
direction: the regular coordinates and residual product are used to dominate
the product-difference loss locally after the source-shaped rank conditions are
fixed.  The source shrink is an implementation device for later local chart
work; it is faithful only as local packaging, not as an assertion that the
paper proves a global measurable chart image.

The measurable-edge-matrix hypothesis is Lean infrastructure rather than a
displayed hypothesis in Aoyagi.  The returned radius and constant are
existential local bounds, not Aoyagi's displayed final `lambda` formula or
optimal constants.

## Risks and Use Guidance

Use this theorem when a downstream local chart package has residual
positivity/integrability and density hypotheses on the returned `source`, but
needs the explicit p.13 product-family adapted lower bound without upgrading
back to the full source-rank stratum.

It should not be cited as source coverage.  The next genuine chart-side tasks
remain: constructing/supplying the local residual signed-box chart,
weighted pushforward and Jacobian/source-density identity, and concrete
residual/source-density monomial-unit identities.

## Nonclaims

No signed-box chart, source image/coverage theorem, weighted pushforward,
Jacobian/source-density identity, residual/source-density monomial-unit
production, normal-crossing extraction, pole-order computation, or RLCT theorem
is proved.
