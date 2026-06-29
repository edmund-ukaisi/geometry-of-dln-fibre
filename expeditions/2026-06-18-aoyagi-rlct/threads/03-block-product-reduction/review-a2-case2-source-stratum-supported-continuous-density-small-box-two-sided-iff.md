# Review - A2 Case 2 source-stratum-supported continuous-density small-box two-sided iff

Reviewer: xhigh read-only scout `Pasteur the 3rd` plus controller build check.

Verdict: PASS.

## Checks

- The theorem is a support wrapper for the new Case 2 continuous-density
  small-box iff, not a new analytic claim.
- It keeps the explicit uniform source-rank support equations as hypotheses.
- It rewrites both the product-integral side and the
  `residualNegPowerIntegrableOn` side to the open set `U`.
- It leaves the source-stratum loss comparison hypotheses on
  `nhdsWithin base sourceStratum`; support is used only for the final measure
  restriction.
- It preserves the radius discipline: `R dρ Dρ` are produced before `delta`,
  and the small-box inequality is checked at `R^2`.
- The Lean proof uses the existing support theorem and the same restriction
  calculation as the earlier finite-integral support wrapper.

Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.

## Nonclaims

No source-rank coverage, selected-entry source/image equality, exact-rank
openness, original source-prior transport, Jacobian comparison, normal
crossings, pole order, or RLCT is proved.
