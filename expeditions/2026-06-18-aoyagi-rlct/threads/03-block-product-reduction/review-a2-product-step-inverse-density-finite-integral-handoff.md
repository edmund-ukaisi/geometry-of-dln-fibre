# Review - A2 p.13 product-step inverse-density finite-integral handoff

Date: 2026-06-26.

Verdict: accepted after documentation fixes.

## Findings

- The Lean theorem statements are honest specializations of the existing
  abstract-density finite-integral handoffs.  They remove the supplied
  `density`, `hdensity_cont`, and `hdensity_pos` inputs, and keep the loss
  lower bound, residual integrability, signed-box pushforward, source-density
  bounds, and source measurability hypotheses explicit.
- The pen-and-paper inverse-coordinate specialization is correct:

```text
Phi^{-1}(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x))
  = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)F2(u),0,C0(x)).
```

- The general inverse-coordinate display was corrected to use
  `A4 = C - A3 F2`, matching the Lean inverse formula.  The concrete
  specialization was unaffected because `A3 = 0`.
- The reproduction note now describes the density as a positive continuous
  local density, not as an analytic unit.  This matches the Lean proof, which
  uses only `ContinuousAt` and strict positivity.

## Boundary

No product chart, source coverage, product-step pushforward identity, original
source/prior transport, signed-box density identification, normal crossings,
pole order, or RLCT theorem is proved here.
