# Review - A2 Case 2 Passive Jacobian-Weighted Residual Source Hypotheses

Date: 2026-06-29.

Status: PASS.

## Reviewed Artifacts

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-residual-source-hypotheses.md
expeditions/2026-06-18-aoyagi-rlct/claims.md
expeditions/2026-06-18-aoyagi-rlct/priorities.md
expeditions/2026-06-18-aoyagi-rlct/synthesis.md
```

## Lean/API Review

Reviewer: Dirac the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem statement matches the proof: the conclusion is a.e. positivity
  over `muJ.restrict localSource` plus
  `residualNegPowerIntegrableOn ... localSource muJ t`.
- Reuse of the whole-measure theorem is sound.  The proof calls the banked
  Jacobian-weighted residual theorem with the same local `let` objects and
  weighted measure, then obtains the `center`-indexed positivity and
  integrability.
- The `aoyagiCoordinateSquareSum_comp_equiv` use has the right orientation:
  `residualMap E c = residualBase E (residualCoordEquiv.symm c)`.
- The local-source support equality applies to the weighted restricted
  measure because the support lemma is arbitrary in the source-domain measure,
  and the proof supplies `jacobianWeightedMeasure` plus source-chart
  a.e. measurability.
- No hidden assumptions were found.  The continuity and determinant-unit
  hypotheses are inherited from the concrete whole-measure theorem and
  chart-produced support path.

No Lean/API findings were reported.

## Source/Scope Review

Reviewer: Hegel the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem is scoped as residual-source packaging only: it keeps the
  chart-produced passive product-domain measure, restricts to an open
  determinant neighborhood, weights by the formal raw-order Jacobian factor,
  maps by `sourceChart`, and proves only residual-source positivity and
  integrability.
- The proof route matches the docs: whole-measure theorem, finite square-sum
  reindexing, and local-source support equality.
- The docs and ledgers preserve the nonclaim boundary: no Haar/prior/Jacobian
  transport, source-image coverage, exact localized residual marginal, normal
  crossings, pole order, or RLCT.
- The Aoyagi page scope is honest when read narrowly: pp. 10-13 motivate the
  retained-passive p.13 coordinate and Jacobian bookkeeping, and pp. 19-22
  motivate the Case 2 selected-entry residual chart algebra.  The Lean proof
  is described as support packaging plus finite reindexing, not as an analytic
  citation.

No source/scope findings were reported.

## Controller Resolution

No Lean or documentation repairs were required after review.

Verification completed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
scripts/lb DLNFibre
git diff --check
scripts/sorries
direct #print axioms probe
```

`scripts/sorries` reports `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Nonclaim boundary remains: no exact localized residual marginal,
determinant-chart Haar pushforward, raw/source Haar theorem, original
source-prior transport, source-prior Jacobian formula, source-image equality,
local coverage, normal crossings, pole order, or RLCT.
