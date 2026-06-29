# Review - A2 Case 2 Passive Jacobian-Weighted Residual Integrability

Date: 2026-06-29.

Reviewer: Archimedes the 3rd, xhigh read-only.

## Verdict

PASS on theorem fidelity after two stale module-documentation boundary fixes.

The Lean theorem matches the documented handoff claim.  It proves existence of
an open `U`, defines the Jacobian-weighted restricted passive-domain measure
and its source-chart pushforward `muJ`, and proves only residual square-sum
positivity a.e. and finite negative-power lintegral for `muJ`.

The proof is domination transfer: upper Jacobian sandwich, comparison of
restricted and global source measures, preservation of scalar domination under
`Measure.map`, the base passive finite-mass residual theorem, and generic
a.e./lower-integral transfer.

## Findings and Fixes

- Low finding: the module doc in
  `RetainedPassiveCase2LocalJacobianMeasure.lean` still said the file proved
  no positivity or integrability statement.  Fixed by narrowing the boundary:
  positivity/integrability statements here are chart-produced or domination-
  based handoffs, not exact localized residual marginals, determinant-chart
  Haar/source-prior transport, normal crossings, or RLCT.
- Low finding: the module doc in `LocalMeasureHandoff.lean` still said the
  file proved no integrability theorem.  Fixed by saying the finite-lintegral
  lemmas are generic measure-theoretic domination handoffs, not
  Aoyagi-specific integrability theorems.

## Boundary

No exact localized residual marginal, determinant-chart Haar transport,
raw/source Haar transport, external or original source-prior comparison,
source-image equality, local inverse/coverage theorem, normal crossings, pole
order, or RLCT extraction is proved.
