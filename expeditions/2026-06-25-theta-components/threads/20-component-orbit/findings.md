# Thread 20 — C2(a) corrected fibre-component↔orbit + sigma labeling (formaliser, #119) — certificate

**Formaliser tide, with a load-bearing FIDELITY CATCH.** New module `Core/FibreComponentOrbit.lean`
(264 lines), wired by the controller; whole library green (3790 jobs); headlines axiom-clean
`[propext, Classical.choice, Quot.sound]` (controller-gated); reviewer PASS on all 3 fidelity questions
+ decorrelated Codex. Commit `90c26d4c`.

## THE FIDELITY CATCH — thread-17's C2(a) interface was DIMENSIONALLY IMPOSSIBLE
Thread-17's `isSmoothAt_sweepFibre_of_component_orbitSmooth` consumes `e : sweepFibreRing⧸I ≃ₐ[k]
orbitRing M`. **That iso cannot exist.** The chart identity gives `dim(fibre top component) =
dim(orbit closure) + δ`, with `δ = r·(d_last + d_0 − r) > 0` for `r ≥ 1`. So a fibre top component is the
orbit closure **× `A^δ`** — NOT iso to a bare shifted orbit ring (which has dimension `dim F − δ`).
Numeric witness: `(2,2,2), r=1` → `4 = 1 + 3`. The tide ESCALATED (did not silently rewrite), left
`FibreGenericSmoothUncond` UNTOUCHED, and built a corrected sibling.
**Lesson:** thread-17's earlier "non-vacuous, confirmed-final" review (reviewer + Codex×2) verified the
implication was non-circular/load-bearing but MISSED that the hypothesis is unsatisfiable on dimension
grounds — "non-vacuous" needs a dimension/satisfiability check, not just "the implication is non-trivial".

## DELIVERED (axiom-clean)
1. `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` — the dimension-CORRECT C2(a) consumer: given
   `e : sweepFibreRing⧸I ≃ₐ[k] MvPolynomial η (orbitRing M)` (orbit ring × `δ` poly vars), then
   `IsSmoothAt k I`. Plugs `MvPolynomial η (orbitRing M)` (a smooth fp domain) into the banked C1+C3
   bridge. Covers `r=0` as `n=0`.
2. `exists_sigma_topComponent_orbitRingEquiv` — **UNCONDITIONAL**: every top-dim component of `O(Σ̄^r)`
   IS `orbitRing (realizerD m)` exactly (no affine factor — `δ` lives only on the FIBRE side, via the
   chart). The first genuine "label a component by an orbit" result; the target the eventual fibre→sigma
   transport lands in.
3. Reusable CA: `isSmoothAt_bot_mvPolynomial_of_isSmoothAt`,
   `smooth_localizationAway_C_of_smooth_localizationAway` (reuse the C3 keystones).

## STILL OPEN — the genuine wall (corrected form, task #128)
The intrinsic block-triangular fibre iso `e : sweepFibreRing⧸I ≃ₐ[k] MvPolynomial η (orbitRing M)`
(fibre top component ≅ orbit closure × `A^δ` as reduced varieties). The θ-count chain is `ncard`-only —
it never labels an individual fibre component. Codex tier ~800–1800 LoC; hardest rung = the labeled
fibre→sigma transport across chart `e` + Schur poly extension + localizations + the W0 `δ`-shift.
`exists_sigma_topComponent_orbitRingEquiv` (the sigma-side landing target) is done; the fibre→sigma
labeled transport + the `A^δ` factor is the remainder.

## Net smoothness state (controller synthesis, CORRECTED)
Generic smoothness is unconditional EXCEPT the corrected, dimensionally-honest C2(a) iso
(`fibre component ≅ orbit × A^δ`), carried by `…_of_component_orbitPolyEquiv`. The thread-17 bare-orbit
consumer is superseded (kept in-library, harmless, but its hypothesis is unsatisfiable — never use it).
Plus a genuine NEW unconditional result: the sigma-side component labeling.

## Artifacts (committed @ 90c26d4c)
`threads/20-component-orbit/statement-card.md` + codex consults. Lean: `Core/FibreComponentOrbit.lean`.
New transitive imports (already in lib): `TopDimMinPrimesW0`, `CCodimCornerMono`,
`Mathlib.RingTheory.TensorProduct.MvPolynomial`. Left the parallel `bundle-conjugation` files
(thread-22 / `FibreChartConjugation.lean`) untouched.
