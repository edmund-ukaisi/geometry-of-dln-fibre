# Review - A2 product-step weighted Haar change of variables

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The theorem is a direct adapter around
  `MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar`.
- The derivative hypothesis is supplied by the landed raw determinant-chart
  `HasFDerivWithinAt` theorem.
- The injectivity hypothesis is supplied by the landed raw-order `InjOn`
  theorem.
- The density is exactly `ENNReal.ofReal |det J(z)|`, where `J(z)` is the
  continuous-linear version of the formal raw-order product-step Jacobian.
- The theorem targets `m.restrict (Phi '' S)`, not the whole target
  determinant chart.
- The public hypotheses use `[Fintype pi] [Fintype nu]`, matching the normed
  matrix instances needed by Mathlib's Jacobian theorem.

## Boundary

This proves weighted additive-Haar transport for the raw p. 13 determinant
chart. It does not identify the original source/prior measure, compare prior
density units, prove finite source coverage, construct normal crossings, give
regular-suspension additivity, or extract an RLCT.

The source-faithful reading of Aoyagi pp. 10-13 remains: those pages give the
coordinate formulas and block identities; they do not explicitly state this
measure theorem. The Lean theorem is an independent elementary analytic
adapter built from Mathlib plus the already-landed derivative and injectivity
facts.
