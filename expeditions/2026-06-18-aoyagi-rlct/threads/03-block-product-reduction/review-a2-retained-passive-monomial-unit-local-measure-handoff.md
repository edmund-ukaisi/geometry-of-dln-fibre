# Review - A2 Retained-Passive Monomial-Unit Local-Measure Handoff

Date: 2026-06-26.

Reviewer: Linnaeus the 3rd, xhigh.

Verdict: pass after documentation correction.

## Findings

The theorem is a wrapper around
`signedBox_monomialLower_sourceDensityBounds_of_monomialUnits` followed by
the retained-passive signed-box handoff.  It leaves the source chart,
weighted pushforward, monomial-unit identities, unit bounds, local
loss/density bounds, Jacobian/density transport, original-loss comparison,
normal crossings, pole order, and RLCT extraction outside the theorem.

No soundness issue was found.  The retained-passive index convention is
correct: retained-passive vertices are `Fin (M + 2)`, edges are `Fin (M + 1)`,
and the generic regular-suspension parameter is `N = M + 1`.

## Documentation Correction

The statement card initially called `Cres` a residual density constant.  It is
the signed-box source-density upper constant.  The statement card was
corrected.
