# Thread 22 — per-pivot conjugation skeleton (B3-5) (formaliser) — certificate

**Formaliser tide (bundle-conjugation).** New module `Core/FibreChartConjugation.lean` (484 LoC), wired
by the controller; whole library green (3803 jobs); headlines axiom-clean `[propext, Classical.choice,
Quot.sound]` (controller-gated); reviewer PASS (fidelity + honesty + decorrelated Codex). Commit
`efb05408`. Route taken: the **conjugation skeleton** (Codex option a), NOT per-pivot re-derivation.

## HEADLINE — `e_β` transports to a `LocalTrivializationDatum` at EVERY pivot (PARTIAL, not locallyTrivial)
The deep chart `e_β` now has a genuine per-pivot analogue `e_{s,t}` and a `LocalTrivializationDatum` at
every pivot `(s,t)` of the per-minor cover — the "plausible-but-not-automatic" rung is closed. Still NOT
`locallyTrivial`: a further rung WAS revealed (as the tower-risk feared) — the cocycle transport ON the
per-pivot trivializations (#133).

## Landed (axiom-clean)
- `gaugeEquiv_ΔPdeep_eq_ΔPdeepAt` — THE SEAM: the endpoint-permutation gauge `pivotGauge σ τ` carries
  the top-left deep minor `ΔPdeep` to the `(s,t)` minor `ΔPdeepAt s t` (determinant identity: `gaugeEquiv`
  sends the generic product to `σ·M·τ⁻¹ = M.submatrix σ τ`). `N ≥ 1`.
- `map_gaugeEquiv_multPoly` — the matrix-level conjugation.
- `gaugeEquivSigma d r P` — descent of `gaugeEquiv P` to `sweepSigmaRing` (via `Ideal.quotientEquivAlg`;
  rests on `vanishingIdeal_sweepSigma_map_gaugeEquiv` G_d-stability, `gaugeEquiv_eq_baseChangePullback`
  = gaugeSub = baseChangeSub). `[Infinite k]`.
- `gaugeEquivSigma_chartDsig` — the carry `chartDsig ↦ chartDsigAt s t`.
- `awayCongr` — reusable localization transport of an `AlgEquiv` carrying `a ↦ b`.
- `chartLocalizedAlgEquivAt` — per-pivot `e_{s,t} : Away (chartDsigAt s t) ≃ₐ[k] Away chartGfib`.
- `chartDsigAt_tensorEquiv` — per-pivot tensor trivialization to `SchurLoc ⊗ sweepFibreRing` (same
  standard fibre).
- `perPivotLocalTrivializationDatum` — a genuine `LocalTrivializationDatum` at EVERY pivot;
  `perPivotLocalTrivializationDatum_topLeft` recovers the top-left datum (non-vacuity).

## The remaining rung to `locallyTrivial` (#133, "likely final", ~300–600 LoC)
The transition cocycle ON the per-pivot trivializations: restrict two charts to the double overlap
`D(chartDsigAt s t · chartDsigAt s' t')` and identify the restricted composite `e_{s,t} ∘ e_{s',t'}⁻¹`
(unrestricted does NOT type-check — sources differ) with the ambient
`FibreBundleTransition.awayOverlapTransition`. Same target fibre ring is a uniform normal form, NOT the
cocycle. ~300–600 LoC (denominator bookkeeping comparing two localization presentations over different
coordinate rings). Reviewer + Codex confirm the disclaimer HONEST.

## Net B3 state
cover (#18) + ambient cocycle (#19) + top-left datum (#21) + per-pivot trivializations & datums at every
pivot (#22). One rung left: cocycle transport (#133).

## Key reuse (real refs)
`EndpointNormalization.{gaugeEquiv, gaugeEquiv_multPoly, aeval_gaugeSub_gaugeSub, liftGauge_val_eq}`,
`OrbitClosure.{baseChangeSub, eval_baseChangePullback}`, `FibreNormalForm.mult_smul`,
`EndBaseChangeSweep.rank_endpoint_conj`, `FibreBundlePerMinor.perMinorEquiv`,
`FibreBundleLocallyTrivial.LocalTrivializationDatum`,
`FibreBundleReduced.reducedFibre_chartDsig_tensorEquiv_reducedVariety`. Mathlib: `Equiv.Perm.permMatrix`
+ `Matrix.permMatrix_{mul,one}`, `PEquiv.*`, `Ideal.quotientEquivAlg`, `IsLocalization.Away.mapₐ`,
`IsLocalization.ringHom_ext`. NEW import: `Mathlib.LinearAlgebra.Matrix.Permutation`.

## Artifacts (committed @ efb05408)
`threads/22-chart-conjugation/statement-card.md` + codex consults (skeleton + reviewer-cocycle). Lean:
`Core/FibreChartConjugation.lean`.
