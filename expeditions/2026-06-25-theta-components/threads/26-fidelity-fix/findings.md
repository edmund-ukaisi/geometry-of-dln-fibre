# Thread 26 — PR #11 review-round-1 fidelity fixes (C3/C4/C5) (formaliser) — certificate

**Formaliser tide (fix-fidelity), integrated + controller-gated.** Whole library green (3806 jobs),
sorries 0, all new/changed headlines axiom-clean `[propext, Classical.choice, Quot.sound]`. Reviewer +
decorrelated Codex PASS (C3/C4/C5, no overclaim). (The tide's own statement-card/codex writes misfired
on the cwd-reset; this certificate is the controller's persisted record.)

## C3 — arbitrary-`B` θ-count — CLOSED (the headline overclaim is now genuinely true)
NEW module `Core/FibreThetaCountArbitrary.lean` (wired into the aggregator by the controller):
- `ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (universe-poly): `B.rank = B'.rank ⟹ numTop(O(fibre B)) =
  numTop(O(fibre B'))`.
- `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank` (`Type 0`): for ANY `B` with `B.rank = r`,
  `numTop(O(mult⁻¹ B)) = cTheta(d−r)`. `B` is a free variable constrained ONLY by `B.rank = r`
  (reviewer-confirmed: not secretly the normal form).
Route (Codex-confirmed clean; bare `RingEquiv` suffices, no properness): `exists_baseChange_of_rank_eq`
+ `image_smul_fibre` + `vanishingIdeal_image_smul` (comap along `baseChangeAlgEquiv`) +
`Ideal.quotientEquiv` + `topDimMinPrimes_ncard_eq_of_ringEquiv` + radical-insensitivity. The composing
`Type 0` headline lives in a `section UnivZero` (model-headline universe trap). **Closes the review C3
overclaim — `numTop(mult⁻¹ B)` for arbitrary rank-`r` `B` is now a theorem.**

## C4 — chart-smoothness incidence — PARTIAL + honest
Edited `FibreComponentOrbitTransport.lean` + `FibreGenericSmoothUncond.lean`:
- NEW `isSmoothAt_chartDsig_topComponent_nonvacuous` (+ helper
  `exists_smooth_localizationAway_chartDsig_nonvacuous`): the smooth chart witness `h` additionally
  satisfies `¬ IsNilpotent h`, so `D(h) ≠ ∅` — fixes the as-written-vacuous gap (same `h` feeds both
  conjuncts).
- CORRECTED the docstring of the weak `exists_isSmoothAt_chartDsig_unconditional`: it now flags it does
  NOT certify `D(h)` nonempty or that `D(h)` meets `V(I)`.
- HONEST RESIDUAL: full component-incidence `D(h) ∩ V(I) ≠ ∅` NOT built — needs faithfully-flat
  lying-over of `includeRight : sweepFibreRing → SchurLoc ⊗_k sweepFibreRing` over `I`
  (`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`), which needs
  `Module.FaithfullyFlat sweepFibreRing (SchurLoc ⊗_k sweepFibreRing)` — PROBED, NOT TC-discoverable
  (needs `Module.Free k SchurLoc` + `Nontrivial SchurLoc` + a tensor-orientation flip; Mathlib's
  base-change instance is `S ⊗[R] M` over S, the chart is `M ⊗[k] S`). Multi-lemma; stopped per
  thrash discipline + landed the honest non-vacuity + corrected claim (the brief's stated fallback).

## C5 — deprecate dead consumers — CLOSED
`@[deprecated "…superseded by isSmoothAt_sweepFibre_topComponent…historical scaffolding, do not use"
(since := "2026-06-26")]` on `FibreComponentOrbit.isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` and
`FibreGenericSmoothUncond.isSmoothAt_sweepFibre_of_component_orbitSmooth`. **Whole-library build fires
ZERO deprecation warnings on either ⟹ confirmed FINDING: both genuinely dead, no live consumer.** ⚠
docstrings retained.

## Gates (controller-re-verified on the integrated tree)
`scripts/sorries` 0/0/0/0; whole-library `scripts/lb` green (3806 jobs); `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on `ncard_topDimMinPrimes_fibre_eq_of_rank_eq`,
`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank`, `isSmoothAt_chartDsig_topComponent_nonvacuous`
(+ the fix-bundle-api headlines). No `sorryAx`.

## Companion: thread 25 (fix-bundle-api, committed fd70f6c2)
C1 cover→`PivotDatum` bridge CLOSED (`pivotOfCover` atlas field); C2 base-side overlap restriction
CLOSED (`overlapRestrict`, `chartOverlapTransition_restrict`, `awayOverlapTransition_restrict_left`) +
`transitionFactors` docstring corrected (common-target cancellation, NOT an overlap cocycle). RESIDUAL:
the full overlap-restricted *trivialization* cocycle (`targetOverlapTransition`) — the per-pivot chart
map is only a `k`-algebra map, not `sweepSigmaRing`-algebra, so the localization-subsingleton trick
fails; genuinely new/heavy, disclaimed.

## Net (review round 1)
All 5 owner comments actioned: C1 closed, C2 base-side closed (full cocycle residual), C3 closed
(arbitrary-B now true), C4 non-vacuity closed (incidence residual), C5 closed. Two honest residuals
roadmapped: `targetOverlapTransition` (C2) and the faithfully-flat component-incidence (C4).
