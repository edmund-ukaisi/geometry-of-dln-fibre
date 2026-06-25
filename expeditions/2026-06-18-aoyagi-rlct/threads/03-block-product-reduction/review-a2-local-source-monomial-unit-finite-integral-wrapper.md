# Review - A2 local-source monomial-unit finite-integral wrapper

Date: 2026-06-25.

## Independent Inputs

Two xhigh read-only audits informed this slice:

- the source audit checked Aoyagi p.13 with pp.10-14 context and concluded that
  p.13 supports the finite block/product formulas and the elementary
  monomial-unit inequality step, but not chart construction, pushforward, or
  density/Jacobian transport;
- the Lean/API audit recommended the local-source monomial-unit wrapper as the
  smallest bedrock theorem after the landed local-source signed-box boundary.

## Verdict

Accepted at the stated scope.

The theorem only replaces expanded residual/source-density inequalities by
supplied monomial-times-unit identities and unit bounds.  It does not infer the
pushforward identity, local source coverage, chart regularity, or any RLCT
claim.

## Risks

The theorem still leaves the original-loss product-family front end on the
older full source-rank-stratum boundary.  A later consumer should either add a
local-source adapted/original-loss wrapper or construct the local chart package
that supplies the current theorem's inputs.
